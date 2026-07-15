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
import qualified Term_Rewriting;
import qualified Arith;

int_of_rat :: Term_Rewriting.Rat -> Arith.Int;
int_of_rat x = fst (Term_Rewriting.quotient_of x);

is_int_rat :: Term_Rewriting.Rat -> Bool;
is_int_rat x =
  Arith.equal_int (snd (Term_Rewriting.quotient_of x)) Arith.one_int;

}
