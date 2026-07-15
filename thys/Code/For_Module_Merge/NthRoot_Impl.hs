{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module NthRoot_Impl(start_value, root_nat_floor) where {

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
import qualified HOL;
import qualified Binary_Exponentiation;
import qualified Archimedean_Field;
import qualified Log_Impl;
import qualified Rat;
import qualified Arith;

start_value :: Arith.Int -> Arith.Nat -> Arith.Int;
start_value n p =
  Binary_Exponentiation.binary_power (Arith.Int_of_integer (2 :: Integer))
    (Arith.nat
      (Archimedean_Field.ceiling
        (Rat.divide_rat
          (Arith.of_nat
            (Log_Impl.log_ceiling (Arith.Int_of_integer (2 :: Integer)) n))
          (Arith.of_nat p))));

root_int_maina ::
  Arith.Nat ->
    Arith.Int -> Arith.Int -> Arith.Int -> Arith.Int -> (Arith.Int, Bool);
root_int_maina pm ipm ip x n =
  let {
    xpm = Binary_Exponentiation.binary_power x pm;
    xp = Arith.times_int xpm x;
  } in (if Arith.less_eq_int xp n then (x, Arith.equal_int xp n)
         else root_int_maina pm ipm ip
                (Arith.divide_int
                  (Arith.plus_int (Arith.divide_int n xpm)
                    (Arith.times_int x ipm))
                  ip)
                n);

root_int_main :: Arith.Nat -> Arith.Int -> (Arith.Int, Bool);
root_int_main p n =
  (if Arith.equal_nat p Arith.zero_nat
    then (Arith.one_int, Arith.equal_int n Arith.one_int)
    else let {
           pm = Arith.minus_nat p Arith.one_nat;
         } in root_int_maina pm (Arith.int_of_nat pm) (Arith.int_of_nat p)
                (start_value n p) n);

root_int_floor_pos :: Arith.Nat -> Arith.Int -> Arith.Int;
root_int_floor_pos p x =
  (if Arith.equal_nat p Arith.zero_nat then Arith.zero_int
    else fst (root_int_main p x));

root_nat_floor :: Arith.Nat -> Arith.Nat -> Arith.Int;
root_nat_floor p x = root_int_floor_pos p (Arith.int_of_nat x);

}
