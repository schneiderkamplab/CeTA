{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module String_Reversal(rev_rule, unary_term) where {

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

rev_term ::
  forall a b.
    Term_Rewriting.Actxt a (Term_Rewriting.Term a b) ->
      Term_Rewriting.Term a b -> Term_Rewriting.Term a b;
rev_term c (Term_Rewriting.Var x) =
  Term_Rewriting.intp_actxt Term_Rewriting.Fun c (Term_Rewriting.Var x);
rev_term c (Term_Rewriting.Fun f [t]) =
  rev_term (Term_Rewriting.More f [] c []) t;

rev_rule ::
  forall a b.
    (Term_Rewriting.Term a b, Term_Rewriting.Term a b) ->
      (Term_Rewriting.Term a b, Term_Rewriting.Term a b);
rev_rule (l, r) =
  (rev_term Term_Rewriting.Hole l, rev_term Term_Rewriting.Hole r);

unary_term :: forall a b. Term_Rewriting.Term a b -> Bool;
unary_term (Term_Rewriting.Var x) = True;
unary_term (Term_Rewriting.Fun f [t]) = unary_term t;
unary_term (Term_Rewriting.Fun v []) = False;
unary_term (Term_Rewriting.Fun v (vb : vd : ve)) = False;

}
