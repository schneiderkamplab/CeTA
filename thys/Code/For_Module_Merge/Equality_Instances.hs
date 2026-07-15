{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Equality_Instances(equality_list, equality_prod, equality_option) where {

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

equality_list :: forall a. (a -> a -> Bool) -> [a] -> [a] -> Bool;
equality_list eq_a [] [] = True;
equality_list eq_a [] (y : ya) = False;
equality_list eq_a (x : xa) [] = False;
equality_list eq_a (x : xa) (y : ya) = eq_a x y && equality_list eq_a xa ya;

equality_prod ::
  forall a b. (a -> a -> Bool) -> (b -> b -> Bool) -> (a, b) -> (a, b) -> Bool;
equality_prod eq_a eq_b (x, xa) (y, ya) = eq_a x y && eq_b xa ya;

equality_option :: forall a. (a -> a -> Bool) -> Maybe a -> Maybe a -> Bool;
equality_option eq_a Nothing Nothing = True;
equality_option eq_a Nothing (Just y) = False;
equality_option eq_a (Just x) Nothing = False;
equality_option eq_a (Just x) (Just y) = eq_a x y;

}
