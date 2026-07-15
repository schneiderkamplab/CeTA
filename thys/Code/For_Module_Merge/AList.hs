{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module AList(update, merge, map_entry, map_default) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;
import qualified Uint;
import qualified Array;
import qualified IArray;
import qualified Uint32;
import qualified Uint64;
import qualified Data_Bits;
import qualified Bit_Shifts;
import qualified Str_Literal;
import qualified Product_Type;
import qualified List;

update :: forall a b. (Eq a) => a -> b -> [(a, b)] -> [(a, b)];
update k v [] = [(k, v)];
update k v (p : ps) = (if fst p == k then (k, v) : ps else p : update k v ps);

merge :: forall a b. (Eq a) => [(a, b)] -> [(a, b)] -> [(a, b)];
merge qs ps = List.foldr (\ (a, b) -> update a b) ps qs;

map_entry :: forall a b. (Eq a) => a -> (b -> b) -> [(a, b)] -> [(a, b)];
map_entry k f [] = [];
map_entry k f (p : ps) =
  (if fst p == k then (k, f (snd p)) : ps else p : map_entry k f ps);

map_default :: forall a b. (Eq a) => a -> b -> (b -> b) -> [(a, b)] -> [(a, b)];
map_default k v f [] = [(k, v)];
map_default k v f (p : ps) =
  (if fst p == k then (k, f (snd p)) : ps else p : map_default k v f ps);

}
