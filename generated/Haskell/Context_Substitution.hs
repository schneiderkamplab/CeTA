{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Context_Substitution(ctxt_subst) where {

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

ctxt_subst ::
  forall a b.
    Term_Rewriting.Actxt a (Term_Rewriting.Term a b) ->
      (b -> Term_Rewriting.Term a b) ->
        Arith.Nat -> Term_Rewriting.Term a b -> Term_Rewriting.Term a b;
ctxt_subst uu uv n t =
  (if Arith.equal_nat n Arith.zero_nat then t
    else Term_Rewriting.intp_actxt Term_Rewriting.Fun uu
           (Term_Rewriting.eval_term Term_Rewriting.Fun
             (ctxt_subst uu uv (Arith.minus_nat n Arith.one_nat) t) uv));

}
