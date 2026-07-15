{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Binary_Exponentiation(binary_power) where {

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
import qualified HOL;
import qualified Arith;

binary_power :: forall a. (Arith.Monoid_mult a) => a -> Arith.Nat -> a;
binary_power x n =
  (if Arith.equal_nat n Arith.zero_nat then Arith.one
    else (case Arith.divmod_nat n (Arith.nat_of_integer (2 :: Integer)) of {
           (d, r) ->
             let {
               rec = binary_power (Arith.times x x) d;
             } in (if Arith.equal_nat r Arith.zero_nat then rec
                    else Arith.times rec x);
         }));

}
