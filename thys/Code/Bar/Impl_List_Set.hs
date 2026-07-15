{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Impl_List_Set(glist_delete, glist_insert) where {

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

rev_append :: forall a. [a] -> [a] -> [a];
rev_append [] ac = ac;
rev_append (x : xs) ac = rev_append xs (x : ac);

glist_delete_aux :: forall a. (a -> a -> Bool) -> a -> [a] -> [a] -> [a];
glist_delete_aux eq x [] asa = asa;
glist_delete_aux eq x (y : ys) asa =
  (if eq x y then rev_append asa ys else glist_delete_aux eq x ys (y : asa));

glist_delete :: forall a. (a -> a -> Bool) -> a -> [a] -> [a];
glist_delete eq x l = glist_delete_aux eq x l [];

glist_member :: forall a. (a -> a -> Bool) -> a -> [a] -> Bool;
glist_member eq x [] = False;
glist_member eq x (y : ys) = eq x y || glist_member eq x ys;

glist_insert :: forall a. (a -> a -> Bool) -> a -> [a] -> [a];
glist_insert eq x xs = (if glist_member eq x xs then xs else x : xs);

}
