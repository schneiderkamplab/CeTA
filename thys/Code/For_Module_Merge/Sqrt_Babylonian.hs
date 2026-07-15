{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Sqrt_Babylonian(sqrt_int, sqrt_nat, sqrt_rat, sqrt_int_ceiling_pos,
                   sqrt_int_floor_pos, sqrt_int_floor)
  where {

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
import qualified NthRoot_Impl;
import qualified Rat;
import qualified List;
import qualified Product_Type;
import qualified Arith;

sqrt_int_maina :: Arith.Int -> Arith.Int -> (Arith.Int, Bool);
sqrt_int_maina x n =
  let {
    x2 = Arith.times_int x x;
  } in (if Arith.less_eq_int x2 n then (x, Arith.equal_int x2 n)
         else sqrt_int_maina
                (Arith.divide_int (Arith.plus_int (Arith.divide_int n x) x)
                  (Arith.Int_of_integer (2 :: Integer)))
                n);

sqrt_int_main :: Arith.Int -> (Arith.Int, Bool);
sqrt_int_main x =
  sqrt_int_maina
    (NthRoot_Impl.start_value x (Arith.nat_of_integer (2 :: Integer))) x;

sqrt_int :: Arith.Int -> [Arith.Int];
sqrt_int x =
  (if Arith.less_int x Arith.zero_int then []
    else (case sqrt_int_main x of {
           (y, True) ->
             (if Arith.equal_int y Arith.zero_int then [Arith.zero_int]
               else [y, Arith.uminus_int y]);
           (_, False) -> [];
         }));

sqrt_nat :: Arith.Nat -> [Arith.Nat];
sqrt_nat x =
  map Arith.nat (List.take Arith.one_nat (sqrt_int (Arith.int_of_nat x)));

sqrt_rat :: Rat.Rat -> [Rat.Rat];
sqrt_rat x =
  (case Rat.quotient_of x of {
    (z, n) ->
      (case sqrt_int n of {
        [] -> [];
        sn : _ ->
          map (\ sz -> Rat.divide_rat (Rat.of_int sz) (Rat.of_int sn))
            (sqrt_int z);
      });
  });

sqrt_int_ceiling_pos :: Arith.Int -> Arith.Int;
sqrt_int_ceiling_pos x = (case sqrt_int_main x of {
                           (y, True) -> y;
                           (y, False) -> Arith.plus_int y Arith.one_int;
                         });

sqrt_int_floor_pos :: Arith.Int -> Arith.Int;
sqrt_int_floor_pos x = fst (sqrt_int_main x);

sqrt_int_floor :: Arith.Int -> Arith.Int;
sqrt_int_floor x =
  (if Arith.less_eq_int Arith.zero_int x then sqrt_int_floor_pos x
    else Arith.uminus_int (sqrt_int_ceiling_pos (Arith.uminus_int x)));

}
