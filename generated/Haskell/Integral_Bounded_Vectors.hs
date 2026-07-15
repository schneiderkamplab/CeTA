{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Integral_Bounded_Vectors(det_bound_hadamard) where {

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
import qualified Binary_Exponentiation;
import qualified Term_Rewriting;
import qualified Arith;

det_bound_hadamard :: Arith.Nat -> Arith.Int -> Arith.Int;
det_bound_hadamard n c =
  (if Arith.equal_nat n Arith.one_nat ||
        Arith.dvd (Arith.nat_of_integer (2 :: Integer)) n
    then Arith.times_int
           (Binary_Exponentiation.binary_power (Arith.int_of_nat n)
             (Arith.divide_nat n (Arith.nat_of_integer (2 :: Integer))))
           (Binary_Exponentiation.binary_power (Arith.abs_int c) n)
    else Term_Rewriting.sqrt_int_floor
           (Binary_Exponentiation.binary_power
             (Arith.times_int (Arith.int_of_nat n)
               (Binary_Exponentiation.binary_power c
                 (Arith.nat_of_integer (2 :: Integer))))
             n));

}
