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
import qualified Subterm_and_Context;
import qualified Term;

rev_term ::
  forall a b.
    Subterm_and_Context.Actxt a (Term.Term a b) ->
      Term.Term a b -> Term.Term a b;
rev_term c (Term.Var x) =
  Subterm_and_Context.intp_actxt Term.Fun c (Term.Var x);
rev_term c (Term.Fun f [t]) = rev_term (Subterm_and_Context.More f [] c []) t;

rev_rule ::
  forall a b. (Term.Term a b, Term.Term a b) -> (Term.Term a b, Term.Term a b);
rev_rule (l, r) =
  (rev_term Subterm_and_Context.Hole l, rev_term Subterm_and_Context.Hole r);

unary_term :: forall a b. Term.Term a b -> Bool;
unary_term (Term.Var x) = True;
unary_term (Term.Fun f [t]) = unary_term t;
unary_term (Term.Fun v []) = False;
unary_term (Term.Fun v (vb : vd : ve)) = False;

}
