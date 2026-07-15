{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Outermost_Forbidden_Patterns(o_to_fp_impl) where {

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
import qualified Forbidden_Patterns;
import qualified Term_Rewriting;

o_to_fp_term ::
  forall a b.
    Term_Rewriting.Term a b ->
      (Term_Rewriting.Actxt a (Term_Rewriting.Term a b),
        (Term_Rewriting.Term a b, Forbidden_Patterns.Location));
o_to_fp_term t = (Term_Rewriting.Hole, (t, Forbidden_Patterns.B));

o_to_fp_impl ::
  forall a b.
    [Term_Rewriting.Term a b] ->
      [(Term_Rewriting.Actxt a (Term_Rewriting.Term a b),
         (Term_Rewriting.Term a b, Forbidden_Patterns.Location))];
o_to_fp_impl = map o_to_fp_term;

}
