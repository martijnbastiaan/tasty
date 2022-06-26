{-# LANGUAGE NamedFieldPuns #-}

-- |
-- A barebones implementation of a prefix tree. Within Tasty it is used to efficiently
-- match dependencies constructed with 'AfterTree'.
--
module Test.Tasty.Patterns.Trie where

import Prelude hiding (lookup)

import Data.List (foldl')
import Data.Maybe (fromMaybe)
import Data.Sequence (Seq, ViewL(EmptyL, (:<)), viewl, (|>))

import Data.Map (Map)
import qualified Data.Map as Map


#if !MIN_VERSION_base(4,11,0)
import Data.Monoid ((<>))
#endif

-- | A 'Trie' (also called a prefix tree, or digital tree) is an n-ary search
-- tree. It allows efficient retrieval of values matching some prefix.
data Trie k v = Trie
  { value :: !(Maybe v)
  , children :: !(Map k (Trie k v))
  }

-- | 'Trie' without any values.
empty :: Trie k v
empty = Trie Nothing Map.empty

-- | Construct a 'Trie' from a list. If a key is found multiple times, only the
-- last value is inserted.
fromList :: Ord k => [(Seq k, v)] -> Trie k v
fromList = foldl' (uncurry . insert) empty

-- | Return all keys and values in the 'Trie'
toList :: Trie k v -> [(Seq k, v)]
toList = go mempty
 where
  go :: Seq k -> Trie k v -> [(Seq k, v)]
  go key (Trie (Just v) children) =
    (key, v) : go key (Trie Nothing children)

  go key (Trie Nothing children) =
    flip concatMap (Map.assocs children) $ \(p, subTrie) ->
      go (key |> p) subTrie

-- | Lookup a key in a 'Trie'. Returns the exact match, and all of its children.
match :: Ord k => Trie k v -> Seq k -> (Maybe v, [(Seq k, v)])
match t prefix0 = go t prefix0
 where
  go Trie{value, children} prefix1 =
    case viewl prefix1 of
      EmptyL ->
        let
          childrenNoPrefix = toList Trie{value=Nothing, children=children}
          prependPrefix (k, v) = (prefix0 <> k, v)
        in
          (value, map prependPrefix childrenNoPrefix)

      k :< ks ->
        case Map.lookup k children of
          Nothing -> (Nothing, [])
          Just subTrie -> go subTrie ks

-- | Lookup a key in a 'Trie'. Returns the exact match, and all of its children.
matchPrefix :: Ord k => Trie k v -> Seq k -> [(Seq k, v)]
matchPrefix trie prefix =
  case match trie prefix of
    (Nothing, kvs) -> kvs
    (Just v, kvs) -> (prefix, v) : kvs

-- | Lookup an key in a 'Trie'. Returns 'Nothing' if no such value exists.
lookup :: Ord k => Trie k v -> Seq k -> Maybe v
lookup trie key = fst (match trie key)

-- | Inserts a value into a 'Trie'. If a value already exists for the given key,
-- it is overwritten.
insert :: Ord k => Trie k v -> Seq k -> v -> Trie k v
insert trie@Trie{children} key v =
  case viewl key of
    EmptyL ->
      Trie (Just v) children

    k :< ks ->
      let
        subTrie0 = fromMaybe empty (Map.lookup k children)
        subTrie1 = insert subTrie0 ks v
      in
        trie{children=Map.insert k subTrie1 children}
