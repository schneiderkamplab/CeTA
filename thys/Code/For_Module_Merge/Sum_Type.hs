{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Sum_Type(Sum(..), equal_sum, projr) where {

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

data Sum a b = Inl a | Inr b;

equal_sum :: forall a b. (Eq a, Eq b) => Sum a b -> Sum a b -> Bool;
equal_sum (Inl x1) (Inr x2) = False;
equal_sum (Inr x2) (Inl x1) = False;
equal_sum (Inr x2) (Inr y2) = x2 == y2;
equal_sum (Inl x1) (Inl y1) = x1 == y1;

instance (Eq a, Eq b) => Eq (Sum a b) where {
  a == b = equal_sum a b;
};

projr :: forall a b. Sum a b -> b;
projr (Inr x2) = x2;

}
