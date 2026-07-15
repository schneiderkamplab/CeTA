{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Size_Change_Termination_Processors(get_arg) where {

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

get_arg ::
  forall a b. Term_Rewriting.Term a b -> Arith.Nat -> Term_Rewriting.Term a b;
get_arg t n =
  (if Arith.equal_nat n Arith.zero_nat then t
    else Arith.nth (Term_Rewriting.args t) (Arith.minus_nat n Arith.one_nat));

}
