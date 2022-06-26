module Trie where

import qualified Data.Sequence as Seq
import Data.Sequence (Seq)

import Data.Bifunctor (second)
import qualified Data.Map as Map

import Test.Tasty
import Test.Tasty.QuickCheck
import qualified Test.Tasty.Patterns.Trie as Trie

-- | A naively constructed 'Trie' through 'Map' should contain the same values
-- as a 'Trie' constructed from the same list.
prop_match :: [(Seq Char, Int)] -> Property
prop_match trieList = expected === actual
 where
  expected = map (second Just) (Map.assocs (Map.fromList trieList))
  actual = map (\(k, _) -> (k, fst (Trie.match trie k))) expected
  trie = Trie.fromList trieList

-- | A naively constructed 'Trie' through 'Map' should match the same prefixes
-- as a 'Trie' constructed from the same list. Note that the ad-hoc 'Map'
-- implementation does the same as 'Trie', but with quadratic complexity.
prop_matchPrefix :: [(Seq Char, Int)] -> Property
prop_matchPrefix trieList0 = expected === actual
 where
  actual =
    flip concatMap trieList1 $ \(k, _) ->
      flip concatMap (prefixes k) $ \prefix ->
        Trie.matchPrefix trie prefix

  expected =
    flip concatMap trieList1 $ \(k, _) ->
      flip concatMap (prefixes k) $ \prefix ->
        [(path, v) | (path, v) <- trieList1, isPrefix prefix path]

  trie = Trie.fromList trieList0
  trieList1 = Map.assocs (Map.fromList trieList0)
  prefixes k = map (`Seq.take` k) [0..Seq.length k]

  isPrefix prefix path
    | Seq.length prefix > Seq.length path = False
    | otherwise = prefix == Seq.take (Seq.length prefix) path

testTrie :: TestTree
testTrie = testGroup "Trie"
  [ testProperty "prop_match" prop_match
  , testProperty "prop_matchPrefix" prop_matchPrefix
  ]
