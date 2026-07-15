{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Prime_Product(prime_product_factor) where {

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
import qualified Sqrt_Babylonian;
import qualified List;
import qualified Arith;

prime_product_factor_main ::
  Arith.Nat ->
    Arith.Nat -> Arith.Nat -> Arith.Nat -> Arith.Nat -> (Arith.Nat, Arith.Nat);
prime_product_factor_main factor_sq factor_pr limit n i =
  (if Arith.less_eq_nat i limit &&
        Arith.less_eq_nat (Arith.nat_of_integer (2 :: Integer)) i
    then (if Arith.dvd i n
           then let {
                  na = Arith.divide_nat n i;
                } in (if Arith.dvd i na
                       then let {
                              nb = Arith.divide_nat na i;
                            } in prime_product_factor_main
                                   (Arith.times_nat factor_sq i) factor_pr
                                   (Arith.nat
                                     (NthRoot_Impl.root_nat_floor
                                       (Arith.nat_of_integer (3 :: Integer))
                                       nb))
                                   nb i
                       else (case Sqrt_Babylonian.sqrt_nat na of {
                              [] -> prime_product_factor_main factor_sq
                                      (Arith.times_nat factor_pr i)
                                      (Arith.nat
(NthRoot_Impl.root_nat_floor (Arith.nat_of_integer (3 :: Integer)) na))
                                      na (Arith.suc i);
                              sn : _ ->
                                (Arith.times_nat factor_sq sn,
                                  Arith.times_nat factor_pr i);
                            }))
           else prime_product_factor_main factor_sq factor_pr limit n
                  (Arith.suc i))
    else (factor_sq, Arith.times_nat factor_pr n));

prime_product_factor :: Arith.Nat -> (Arith.Nat, Arith.Nat);
prime_product_factor n =
  (case Sqrt_Babylonian.sqrt_nat n of {
    [] -> prime_product_factor_main Arith.one_nat Arith.one_nat
            (Arith.nat
              (NthRoot_Impl.root_nat_floor (Arith.nat_of_integer (3 :: Integer))
                n))
            n (Arith.nat_of_integer (2 :: Integer));
    s : _ -> (s, Arith.one_nat);
  });

}
