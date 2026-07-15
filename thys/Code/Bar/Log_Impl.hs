{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Log_Impl(Proper_base, log_ceiling) where {

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
import qualified Arith;

newtype Proper_base = Abs_proper_base Arith.Int;

rep_proper_base :: Proper_base -> Arith.Int;
rep_proper_base (Abs_proper_base x) = x;

get_base :: Proper_base -> Arith.Int;
get_base x = rep_proper_base x;

square_base :: Proper_base -> Proper_base;
square_base xa =
  Abs_proper_base (Arith.times_int (rep_proper_base xa) (rep_proper_base xa));

log_main :: Proper_base -> Arith.Int -> (Arith.Nat, Arith.Int);
log_main b x =
  (if Arith.less_int x (get_base b) then (Arith.zero_nat, Arith.one_int)
    else (case log_main (square_base b) x of {
           (z, bz) ->
             let {
               l = Arith.times_nat (Arith.nat_of_integer (2 :: Integer)) z;
               bz1 = Arith.times_int bz (get_base b);
             } in (if Arith.less_int x bz1 then (l, bz)
                    else (Arith.suc l, bz1));
         }));

into_base :: Arith.Int -> Proper_base;
into_base xa =
  Abs_proper_base
    (if Arith.less_eq_int (Arith.Int_of_integer (2 :: Integer)) xa then xa
      else Arith.Int_of_integer (2 :: Integer));

log_ceiling :: Arith.Int -> Arith.Int -> Arith.Nat;
log_ceiling b x =
  (case log_main (into_base b) x of {
    (y, by) -> (if Arith.equal_int x by then y else Arith.suc y);
  });

}
