{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Is_Rat_To_Rat(int_of_rat, is_int_rat) where {

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
import qualified Rat;
import qualified Arith;

int_of_rat :: Rat.Rat -> Arith.Int;
int_of_rat x = fst (Rat.quotient_of x);

is_int_rat :: Rat.Rat -> Bool;
is_int_rat x = Arith.equal_int (snd (Rat.quotient_of x)) Arith.one_int;

}
