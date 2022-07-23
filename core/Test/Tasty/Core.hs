-- | Core types and definitions
{-# LANGUAGE FlexibleContexts, ExistentialQuantification, RankNTypes, DeriveDataTypeable,
             NoMonomorphismRestriction, DeriveGeneric, LambdaCase #-}
module Test.Tasty.Core where

import qualified Data.DList as DList
import qualified Data.Foldable as F
import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Test.Tasty.Patterns.Trie as Trie

import Control.Exception
import Control.Monad (guard)
import Data.DList (DList)
import Data.Foldable
import Data.Graph (stronglyConnComp, SCC(CyclicSCC, AcyclicSCC))
import Data.List (intercalate)
import Data.Map.Strict (Map)
import Data.Maybe (maybeToList, mapMaybe)
import Data.Sequence ((|>))
import Data.Tagged
import Data.Typeable
import GHC.Generics
import Text.Printf

#if !MIN_VERSION_base(4,11,0)
import Data.Monoid
#endif

import Test.Tasty.Options
import Test.Tasty.Patterns
import Test.Tasty.Patterns.Eval
import Test.Tasty.Patterns.Types
import Test.Tasty.Providers.ConsoleFormat

-- | Maps a test to all its dependencies
type DependencyTree = Map ExactPath [(DependencyType, ExactPath)]

-- | Specifies how to calculate a dependency
data DependencySpec
  = ExactDep ExactPath
  -- ^ Points to an 'AfterTree' node. That means that the dependencies can be
  -- fetched by appending @EpcAfterTree L@, and the tests that depend on these
  -- dependencies by appending @EpcAfterTree R@.
  | PatternDep Expr ExactPath
  -- ^ All tests matching this 'Expr' should be considered dependencies of all
  -- tests matching the 'ExactPath'.
  deriving (Show, Eq)

-- | Dependency of a test. Either it points to an exact path it depends on, or
-- contains a pattern that should be tested against all tests in a 'TestTree'.
data Dependency = Dependency
  { dpType :: DependencyType
  , dpSpec :: DependencySpec
  }
  deriving (Show, Eq)

-- | Dependencies of a test
type Deps = [Dependency]

-- | If a test failed, 'FailureReason' describes why
data FailureReason
  = TestFailed
    -- ^ test provider indicated failure of the code to test, either because
    -- the tested code returned wrong results, or raised an exception
  | TestThrewException SomeException
    -- ^ the test code itself raised an exception. Typical cases include missing
    -- example input or output files.
    --
    -- Usually, providers do not have to implement this, as their 'run' method
    -- may simply raise an exception.
  | TestTimedOut Integer
    -- ^ test didn't complete in allotted time
  | TestDepFailed -- See Note [Skipped tests]
    -- ^ a dependency of this test failed, so this test was skipped.
  deriving Show

-- | Outcome of a test run
--
-- Note: this is isomorphic to @'Maybe' 'FailureReason'@. You can use the
-- @generic-maybe@ package to exploit that.
data Outcome
  = Success -- ^ test succeeded
  | Failure FailureReason -- ^ test failed because of the 'FailureReason'
  deriving (Show, Generic)

-- | Time in seconds. Used to measure how long the tests took to run.
type Time = Double

-- | A test result
data Result = Result
  { resultOutcome :: Outcome
    -- ^ Did the test fail? If so, why?
  , resultDescription :: String
    -- ^
    -- 'resultDescription' may contain some details about the test. For
    -- a passed test it's ok to leave it empty. Providers like SmallCheck and
    -- QuickCheck use it to provide information about how many tests were
    -- generated.
    --
    -- For a failed test, 'resultDescription' should typically provide more
    -- information about the failure.
  , resultShortDescription :: String
    -- ^ The short description printed in the test run summary, usually @OK@ or
    -- @FAIL@.
  , resultTime :: Time
    -- ^ How long it took to run the test, in seconds.
  , resultDetailsPrinter :: ResultDetailsPrinter
    -- ^ An action that prints additional information about a test.
    --
    -- This is similar to 'resultDescription' except it can produce
    -- colorful/formatted output; see "Test.Tasty.Providers.ConsoleFormat".
    --
    -- This can be used instead of or in addition to 'resultDescription'.
    --
    -- Usually this is set to 'noResultDetails', which does nothing.
    --
    -- @since 1.3.1
  }
  deriving Show

{- Note [Skipped tests]
   ~~~~~~~~~~~~~~~~~~~~
   There are two potential ways to represent the tests that are skipped
   because of their failed dependencies:
   1. With Outcome = Failure, and FailureReason giving the specifics (TestDepFailed)
   2. With a dedicated Outcome = Skipped

   It seems to me that (1) will lead to fewer bugs (esp. in the extension packages),
   because most of the time skipped tests should be handled in the same way
   as failed tests.
   But sometimes it is not obvious what the right behavior should be. E.g.
   should --hide-successes show or hide the skipped tests?

   Perhaps we should hide them, because they aren't really informative.
   Or perhaps we shouldn't hide them, because we are not sure that they
   will pass, and hiding them will imply a false sense of security
   ("there's at most 2 tests failing", whereas in fact there could be much more).

   So I might change this in the future, but for now treating them as
   failures seems the easiest yet reasonable approach.
-}

{- Note [Tree folding gotchas]
   ~~~~~~~~~~~~~~~~~~~~
   A tree fold reduces a tree to a single value using the functions in
   'TreeFold'. As the documentation notices, the folder also filters tests based
   on filter options passed to it (typically passed by the user using the "-p"
   flag on the command line). While this can seemingly happen in a single pass,
   let's consider a simple 'TestTree':

       testGroup "tests"
         [ singleTest "A" aTest
         , after AllSucceed "A" (singleTest "B" bTest)
         ]

   Test "B" defines "A" to be a dependency. Therefore, if a user were to filter
   with "-p B", they would expect "A" to run too. Because patterns can match tests
   anywhere in the tree, a tree has to be traversed in its entirety _before_ the
   folder can decide whether or not to exclude a test. Therfore, 'foldTestTree'
   roughly does the following things:

       1. It builds a 'DependencyTree' by traversing the 'TestTree' without any
          filters applied.

       2. It builds a list of tests the user wishes to be included just by looking
          at the pattern supplied.

       3. It combines (1) and (2) and finds all the user specified tests plus their
          dependencies.

       4. Finally, it uses all the user supplied folding functions, but replaces the
          filter that tests whether a test is included in the collection constructed
          in (3).

   To prevent infinite loops while constructing the various collections, the 'TestTree'
   is checked for cycles - as test patterns can impose them. To keep API compatibility
   the function throws an exception if it detects cycles. Even though this in some sense
   violates the function's type signature, it seems like a fair trade-off: we can't do
   anything useful with test trees containing cycles any way so crashing seems OK.

   Note that this complexity -- the existence of 'Trie', 'DependencyTree', dependency
   cycles, quadratic test tree construction, and the fact that we need to traverse the
   tree multiple times for a single fold -- is imposed by the fact that dependencies
   specified using patterns can match _any_ subtree in the full test tree. We might
   want to consider deprecating this feature and eventually removing it in favor of
   'AfterTree'.
-}

-- | 'True' for a passed test, 'False' for a failed one.
resultSuccessful :: Result -> Bool
resultSuccessful r =
  case resultOutcome r of
    Success -> True
    Failure {} -> False

-- | Shortcut for creating a 'Result' that indicates exception
exceptionResult :: SomeException -> Result
exceptionResult e = Result
  { resultOutcome = Failure $ TestThrewException e
  , resultDescription = "Exception: " ++ show e
  , resultShortDescription = "FAIL"
  , resultTime = 0
  , resultDetailsPrinter = noResultDetails
  }

-- | Test progress information.
--
-- This may be used by a runner to provide some feedback to the user while
-- a long-running test is executing.
data Progress = Progress
  { progressText :: String
    -- ^ textual information about the test's progress
  , progressPercent :: Float
    -- ^
    -- 'progressPercent' should be a value between 0 and 1. If it's impossible
    -- to compute the estimate, use 0.
  }
  deriving Show

-- | The interface to be implemented by a test provider.
--
-- The type @t@ is the concrete representation of the test which is used by
-- the provider.
class Typeable t => IsTest t where
  -- | Run the test
  --
  -- This method should cleanly catch any exceptions in the code to test, and
  -- return them as part of the 'Result', see 'FailureReason' for an
  -- explanation. It is ok for 'run' to raise an exception if there is a
  -- problem with the test suite code itself (for example, if a file that
  -- should contain example data or expected output is not found).
  run
    :: OptionSet -- ^ options
    -> t -- ^ the test to run
    -> (Progress -> IO ()) -- ^ a callback to report progress.
                           -- Note: the callback is a no-op at the moment
                           -- and there are no plans to use it;
                           -- feel free to ignore this argument for now.
    -> IO Result

  -- | The list of options that affect execution of tests of this type
  testOptions :: Tagged t [OptionDescription]

-- | The name of a test or a group of tests
type TestName = String

-- | 'ResourceSpec' describes how to acquire a resource (the first field)
-- and how to release it (the second field).
data ResourceSpec a = ResourceSpec (IO a) (a -> IO ())

-- | A resources-related exception
data ResourceError
  = NotRunningTests
  | UnexpectedState String String
  | UseOutsideOfTest
  deriving Typeable

instance Show ResourceError where
  show NotRunningTests =
    "Unhandled resource. Probably a bug in the runner you're using."
  show (UnexpectedState where_ what) =
    printf "Unexpected state of the resource (%s) in %s. Report as a tasty bug."
      what where_
  show UseOutsideOfTest =
    "It looks like you're attempting to use a resource outside of its test. Don't do that!"

instance Exception ResourceError

-- | Exceptions related to dependencies between tests.
data DependencyException
  = DependencyLoop [[Path]]
    -- ^ Test dependencies form cycles. In other words, test A cannot start
    -- until test B finishes, and test B cannot start until test
    -- A finishes. Field lists detected cycles.
  deriving (Typeable)

instance Show DependencyException where
  show (DependencyLoop css) = "Test dependencies have cycles:\n" ++ showCycles css
    where
      showCycles = intercalate "\n" . map showCycle
      showPath = intercalate "." . Data.Foldable.toList

      -- For clarity in the error message, the first element is repeated at the end
      showCycle []     = "- <empty cycle>"
      showCycle (x:xs) = "- " ++ intercalate ", " (map showPath (x:xs ++ [x]))

instance Exception DependencyException

-- | These are the two ways in which one test may depend on the others.
--
-- This is the same distinction as the
-- <http://testng.org/doc/documentation-main.html#dependent-methods hard vs soft dependencies in TestNG>.
--
-- @since 1.2
data DependencyType
  = AllSucceed
    -- ^ The current test tree will be executed after its dependencies finish, and only
    -- if all of the dependencies succeed.
  | AllFinish
    -- ^ The current test tree will be executed after its dependencies finish,
    -- regardless of whether they succeed or not.
  deriving (Eq, Show)

-- | The main data structure defining a test suite.
--
-- It consists of individual test cases and properties, organized in named
-- groups which form a tree-like hierarchy.
--
-- There is no generic way to create a test case. Instead, every test
-- provider (tasty-hunit, tasty-smallcheck etc.) provides a function to
-- turn a test case into a 'TestTree'.
--
-- Groups can be created using 'testGroup'.
data TestTree
  = forall t . IsTest t => SingleTest TestName t
    -- ^ A single test of some particular type
  | TestGroup TestName [TestTree]
    -- ^ Assemble a number of tests into a cohesive group
  | PlusTestOptions (OptionSet -> OptionSet) TestTree
    -- ^ Add some options to child tests
  | forall a . WithResource (ResourceSpec a) (IO a -> TestTree)
    -- ^ Acquire the resource before the tests in the inner tree start and
    -- release it after they finish. The tree gets an `IO` action which
    -- yields the resource, although the resource is shared across all the
    -- tests.
  | AskOptions (OptionSet -> TestTree)
    -- ^ Ask for the options and customize the tests based on them
  | After DependencyType Expr TestTree
    -- ^ Only run after all tests that match a given pattern finish
    -- (and, depending on the 'DependencyType', succeed)
  | AfterTree DependencyType TestTree TestTree
    -- ^ Only run tests in the right 'TestTree' after tests in the left
    -- 'TestTree' finish (and, depending on the 'DependencyType', succeed)

-- | Create a named group of test cases or other groups
testGroup :: TestName -> [TestTree] -> TestTree
testGroup = TestGroup

-- | Like 'after', but accepts the pattern as a syntax tree instead
-- of a string. Useful for generating a test tree programmatically.
--
-- ==== __Examples__
--
-- Only match on the test's own name, ignoring the group names:
--
-- @
-- 'after_' 'AllFinish' ('Test.Tasty.Patterns.Types.EQ' ('Field' 'NF') ('StringLit' \"Bar\")) $
--    'testCase' \"A test that depends on Foo.Bar\" $ ...
-- @
--
-- @since 1.2
after_
  :: DependencyType -- ^ whether to run the tests even if some of the dependencies fail
  -> Expr -- ^ the pattern
  -> TestTree -- ^ the subtree that depends on other tests
  -> TestTree -- ^ the subtree annotated with dependency information
after_ = After

-- | The 'after' combinator declares dependencies between tests.
--
-- If a 'TestTree' is wrapped in 'after', the tests in this tree will not run
-- until certain other tests («dependencies») have finished. These
-- dependencies are specified using an AWK pattern (see the «Patterns» section
-- in the README).
--
-- Moreover, if the 'DependencyType' argument is set to 'AllSucceed' and
-- at least one dependency has failed, this test tree will not run at all.
--
-- Tasty does not check that the pattern matches any tests (let alone the
-- correct set of tests), so it is on you to supply the right pattern.
--
-- ==== __Examples__
--
-- The following test will be executed only after all tests that contain
-- @Foo@ anywhere in their path finish.
--
-- @
-- 'after' 'AllFinish' \"Foo\" $
--    'testCase' \"A test that depends on Foo.Bar\" $ ...
-- @
--
-- Note, however, that our test also happens to contain @Foo@ as part of its name,
-- so it also matches the pattern and becomes a dependency of itself. This
-- will result in a 'DependencyLoop' exception. To avoid this, either
-- change the test name so that it doesn't mention @Foo@ or make the
-- pattern more specific.
--
-- You can use AWK patterns, for instance, to specify the full path to the dependency.
--
-- @
-- 'after' 'AllFinish' \"$0 == \\\"Tests.Foo.Bar\\\"\" $
--    'testCase' \"A test that depends on Foo.Bar\" $ ...
-- @
--
-- Or only specify the dependency's own name, ignoring the group names:
--
-- @
-- 'after' 'AllFinish' \"$NF == \\\"Bar\\\"\" $
--    'testCase' \"A test that depends on Foo.Bar\" $ ...
-- @
--
-- @since 1.2
after
  :: DependencyType -- ^ whether to run the tests even if some of the dependencies fail
  -> String -- ^ the pattern
  -> TestTree -- ^ the subtree that depends on other tests
  -> TestTree -- ^ the subtree annotated with dependency information
after deptype s =
  case parseExpr s of
    Nothing -> error $ "Could not parse pattern " ++ show s
    Just e -> after_ deptype e

-- | Run given 'TestTree's one after another.
--
-- @since 1.5
afterTree
  :: DependencyType -- ^ whether to run the tests even if some of the dependencies fail
  -> TestTree -- ^ dependencies
  -> TestTree -- ^ tests to run after all dependencies have finished
  -> TestTree
afterTree = AfterTree

-- | Run given 'TestTree's one after another.
--
-- @since 1.5
sequentialTestGroup
  :: TestName -- ^ Test group name
  -> DependencyType -- ^ whether to run the tests even if some of the dependencies fail
  -> [TestTree] -- ^ tests to run sequentially
  -> TestTree
sequentialTestGroup groupName depType =
  testGroup groupName . maybeToList . go
 where
  go [] = Nothing
  go (t:ts) = Just (foldl' (afterTree depType) t ts)

-- | An algebra for folding a `TestTree`.
--
-- Instead of constructing fresh records, build upon `trivialFold`
-- instead. This way your code won't break when new nodes/fields are
-- indroduced.
data TreeFold b = TreeFold
  { foldSingle :: forall t . IsTest t => OptionSet -> ExactPath -> TestName -> t -> b
  , foldGroup :: OptionSet -> TestName -> b -> b
  , foldResource :: forall a . OptionSet -> ResourceSpec a -> (IO a -> b) -> b
  , foldAfter :: OptionSet -> DependencyType -> ExactPath -> Expr -> b -> b
  , foldAfterTree :: OptionSet -> DependencyType -> ExactPath-> b -> b
  , foldFilter :: TestPattern -> ExactPath -> Bool
  }

-- | 'trivialFold' can serve as the basis for custom folds. Just override
-- the fields you need.
--
-- Here's what it does:
--
-- * single tests are mapped to `mempty` (you probably do want to override that)
--
-- * test groups are returned unmodified
--
-- * for a resource, an IO action that throws an exception is passed (you
-- want to override this for runners/ingredients that execute tests)
trivialFold :: Monoid b => TreeFold b
trivialFold = TreeFold
  { foldSingle = \_ _ _ -> mempty
  , foldGroup = \_ _ b -> b
  , foldResource = \_ _ f -> f $ throwIO NotRunningTests
  , foldAfter = \_ _ _ _ b -> b
  , foldAfterTree = \_ _ _ b -> b
  , foldFilter = \pat -> testPatternMatches pat . exactPathToPath
  }

-- | Fold a test tree into a single value.
--
-- Like 'foldTestTree', but does not take into account dependencies.
foldTestTreeNoDeps
  :: forall b . Monoid b
  => TreeFold b
     -- ^ the algebra (i.e. how to fold a tree)
  -> OptionSet
     -- ^ initial options
  -> TestTree
     -- ^ the tree to fold
  -> b
foldTestTreeNoDeps (TreeFold fTest fGroup fResource fAfter fAfterTree fFilter) =
  go mempty
  where
    go :: ExactPath -> OptionSet -> TestTree -> b
    go path opts tree1 =
      case tree1 of
        SingleTest name test
          | fFilter pat (path |> EpcSingleTest name)
            -> fTest opts (path |> EpcSingleTest name) name test
          | otherwise -> mempty
        TestGroup name trees ->
          fGroup opts name $ foldMap (goGroup name path opts) (zip [0..] trees)
        PlusTestOptions f tree -> go (path |> EpcPlusTestOptions) (f opts) tree
        WithResource res0 tree ->
          fResource opts res0 $ \res ->
            go (path |> EpcWithResource) opts (tree res)
        AskOptions f -> go (path |> EpcAskOptions) opts (f opts)
        After deptype dep tree ->
          fAfter opts deptype (path |> EpcAfter) dep $ go (path |> EpcAfter) opts tree
        AfterTree deptype treeLeft treeRight ->
          let
            bLeft = go (path |> EpcAfterTree L) opts treeLeft
            bRight = go (path |> EpcAfterTree R) opts treeRight
          in
            bLeft <> fAfterTree opts deptype path bRight
      where
        pat = lookupOption opts :: TestPattern

    goGroup :: String -> ExactPath -> OptionSet -> (Int, TestTree) -> b
    goGroup name path opts (n, tree1) = go (path |> EpcTestGroup name n) opts tree1

-- | Fold a test tree into a single value.
--
-- Like 'foldTestTree', but returns 'DependencyTree' it constructed for reuse.
foldTestTreeWithDeps
  :: forall b . Monoid b
  => TreeFold b
     -- ^ the algebra (i.e. how to fold a tree)
  -> OptionSet
     -- ^ initial options
  -> TestTree
     -- ^ the tree to fold
  -> (b, DependencyTree)
foldTestTreeWithDeps algebra opts testTree =
  let
    -- Build a dependency tree based on the _whole_ tree, including tests that would naively
    -- be filtered by the algebra. Also see [Note: Tree folding gotchas].
    goFold opt alg = DList.toList (foldTestTreeNoDeps alg opt testTree)
    allPaths = goFold mempty treePathsFold{foldFilter = \_ _ -> True}
    allDeps =  goFold mempty treeDependenciesFold{foldFilter = \_ _ -> True}
    depTree = toDependencyTreeOrThrow allPaths allDeps

    -- Construct a set of all tests that need to be run. These tests consists of all
    -- tests that would naively be selected, plus all their dependencies.
    paths = Set.fromList (goFold opts treePathsFold)
    depPaths = Set.fromList (concatMap (transitiveDependencyPaths depTree) paths)

    -- Construct a new filter that takes into account dependencies.
    newFoldFilter _pat path = path `Set.member` Set.union paths depPaths
  in
    -- 'depTree' might be a 'DependencyLoop' error so we need to make sure it
    -- gets evaluated, even if the consumer doesn't evaluate it. See
    -- [Note: tree folding gotchas].
    depTree `seq`
      ( foldTestTreeNoDeps algebra{foldFilter=newFoldFilter} opts testTree
      , depTree )

-- | Fold a test tree into a single value.
--
-- The fold result type should be a monoid. This is used to fold multiple
-- results in a test group. In particular, empty groups get folded into 'mempty'.
--
-- Apart from pure convenience, this function also does the following
-- useful things:
--
-- 1. Keeping track of the current options (which may change due to
-- `PlusTestOptions` nodes)
--
-- 2. Filtering out the tests which do not match the patterns.
--
-- Thus, it is preferred to an explicit recursive traversal of the tree.
--
-- Note: right now, the patterns are looked up only once, and won't be
-- affected by the subsequent option changes. This shouldn't be a problem
-- in practice; OTOH, this behaviour may be changed later.
--
-- Note: this function will throw a 'DependencyLoop' exception if cycles are
-- detected in the 'TestTree'. Use 'foldTestTreeNoDeps' if you don't want folding
-- to account for dependencies.
foldTestTree
  :: forall b . Monoid b
  => TreeFold b
     -- ^ the algebra (i.e. how to fold a tree)
  -> OptionSet
     -- ^ initial options
  -> TestTree
     -- ^ the tree to fold
  -> b
foldTestTree algebra opts testTree =
  fst (foldTestTreeWithDeps algebra opts testTree)

-- | Get the list of options that are relevant for a given test tree
treeOptions :: TestTree -> [OptionDescription]
treeOptions =

  Prelude.concat .
  Map.elems .

  foldTestTree
    trivialFold { foldSingle = \_ _ _ -> getTestOptions }
    mempty

  where
    getTestOptions
      :: forall t . IsTest t
      => t -> Map.Map TypeRep [OptionDescription]
    getTestOptions t =
      Map.singleton (typeOf t) $
          witness testOptions t

-- | Get all paths in a 'TestTree', potentially filtered by options given in
-- the first argument, 'OptionSet'.
treePathsFold :: TreeFold (DList ExactPath)
treePathsFold = trivialFold{foldSingle = \_ path _ _ -> DList.singleton path}

-- | Get all dependencies stored in a 'TestTree'.
treeDependenciesFold :: TreeFold (DList Dependency)
treeDependenciesFold = trivialFold{foldAfter=goAfter, foldAfterTree=goAfterTree}
 where
  goAfterTree _ depType path deps =
    Dependency depType (ExactDep path) `DList.cons` deps

  goAfter _ depType path expr deps =
    Dependency depType (PatternDep expr path) `DList.cons` deps

-- | Fetch all dependencies (and theirs, and so on) for a given test.
transitiveDependencies :: DependencyTree -> ExactPath -> [(DependencyType, ExactPath)]
transitiveDependencies depTree = go
 where
  go :: ExactPath -> [(DependencyType, ExactPath)]
  go p =
    case Map.lookup p depTree of
      Nothing -> []
      Just depsAndPaths ->
        depsAndPaths <> concatMap (go . snd) depsAndPaths

-- | Fetch all dependencies (and theirs, and so on) for a given test.
transitiveDependencyPaths :: DependencyTree -> ExactPath -> [ExactPath]
transitiveDependencyPaths tree = map snd . transitiveDependencies tree

-- | Construct a 'DependencyTree' from a given tree, or fail with an exception
-- if the test contained cycles.
toDependencyTreeOrThrow
  :: [ExactPath]
  -- ^ All paths in the tree.
  -> [Dependency]
  -- ^ All dependencies in the tree.
  -> DependencyTree
  -- ^ Returns the constructued 'DependencyTree' or throws if the tree contains cycles.
toDependencyTreeOrThrow allPaths deps =
  either
    (throw . DependencyLoop . map (map exactPathToPath))
    id
    (toDependencyTree allPaths deps)

-- | Construct a 'DependencyTree' from a given tree.
toDependencyTree
  :: [ExactPath]
  -- ^ All paths in the tree.
  -> [Dependency]
  -- ^ All dependencies in the tree.
  -> Either [[ExactPath]] DependencyTree
  -- ^ Returns the constructued 'DependencyTree' or a list of all cycles found
  -- within it.
toDependencyTree allPaths deps =
  case checkCycles depTree of
    Nothing -> Right depTree
    Just cycles -> Left cycles

 where
  depTree = foldl' insert mempty (concatMap go deps)
  insert tree (test, dep) =  Map.alter (Just . maybe [dep] (dep:)) test tree

  go :: Dependency -> [(ExactPath, (DependencyType, ExactPath))]
  go (Dependency depType depSpec) = case depSpec of
    ExactDep path -> do
      -- Filter any dependencies that are part of the _left_ side of an
      -- 'AfterTree'. All tests in the _right_ tree depend on them to
      -- finish anyway, so no need to wait pollute the dependency list
      -- with them.
      (depPath, ()) <- Trie.matchPrefix trie (path |> EpcAfterTree L)
      let subDepPath = Seq.drop (length depPath) depPath
      -- TODO: Build into Trie for more efficient filtering
      guard $ F.notElem (EpcAfterTree L) subDepPath

      -- Filter any tests that are part of the _right_ side of an
      -- 'AfterTree'.
      (testPath, ()) <- Trie.matchPrefix trie (path |> EpcAfterTree R)
      let subTestPath = Seq.drop (length testPath) testPath
      -- TODO: Build into Trie for more efficient filtering
      guard $ F.notElem (EpcAfterTree R) subTestPath

      pure (testPath, (depType, depPath))

    -- Note: Duplicate dependencies may arise if the same test name matches
    -- multiple patterns. It's not clear that removing them is worth the
    -- trouble; might consider this in the future.
    PatternDep depexpr testPrefix -> do
      -- Consider each test in the whole test tree, and filter the ones
      -- that match 'depexpr'.
      depPath <- allPaths
      (testPath, ()) <- Trie.matchPrefix trie testPrefix
      guard $ exprMatches depexpr (exactPathToPath depPath)
      pure (testPath, (depType, depPath))

  trie = Trie.fromList (zip allPaths (repeat ()))

-- | Check whether a 'DependencyTree' contains cycles. If it does, return the
-- tests that formed cycles.
checkCycles :: DependencyTree -> Maybe [[ExactPath]]
checkCycles tests = do
  case cycles of
    [] -> Nothing
    _  -> Just cycles
 where
  graph = [(v, v, map snd vs) | (v, vs) <- Map.toList tests]
  sccs = stronglyConnComp graph
  cycles =
    flip mapMaybe sccs $ \case
      AcyclicSCC{} -> Nothing
      CyclicSCC vs -> Just vs
