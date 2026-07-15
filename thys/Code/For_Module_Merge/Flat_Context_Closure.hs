{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Flat_Context_Closure(hole_at, block_rule, unblock_rule) where {

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
import qualified Term;
import qualified List;
import qualified Subterm_and_Context;
import qualified Arith;

hole_at ::
  forall a b.
    (Eq a) => Arith.Nat ->
                Arith.Nat -> a -> Subterm_and_Context.Actxt a b -> Bool;
hole_at n i f (Subterm_and_Context.More g ss1 Subterm_and_Context.Hole ss2) =
  g == f &&
    Arith.equal_nat (List.size_list ss1) i &&
      Arith.equal_nat (List.size_list ss2)
        (Arith.minus_nat (Arith.minus_nat n i) Arith.one_nat);
hole_at n i f Subterm_and_Context.Hole = False;
hole_at n i f
  (Subterm_and_Context.More v va (Subterm_and_Context.More vd ve vf vg) vc) =
  False;

block_term :: forall a b. a -> Term.Term a b -> Term.Term a b;
block_term f (Term.Var x) = Term.Var x;
block_term f (Term.Fun g ts) = Term.Fun g (map (\ t -> Term.Fun f [t]) ts);

block_rule ::
  forall a b.
    a -> (Term.Term a b, Term.Term a b) -> (Term.Term a b, Term.Term a b);
block_rule f r = (block_term f (fst r), block_term f (snd r));

strip_unary_root :: forall a b. (Eq a) => a -> Term.Term a b -> Term.Term a b;
strip_unary_root f (Term.Fun g [t]) = (if f == g then t else Term.Fun g [t]);
strip_unary_root f (Term.Var v) = Term.Var v;
strip_unary_root f (Term.Fun v []) = Term.Fun v [];
strip_unary_root f (Term.Fun v (vb : vd : ve)) = Term.Fun v (vb : vd : ve);

has_unary_root :: forall a b. (Eq a) => a -> Term.Term a b -> Bool;
has_unary_root f (Term.Fun g [t]) = f == g;
has_unary_root f (Term.Var v) = False;
has_unary_root f (Term.Fun v []) = False;
has_unary_root f (Term.Fun v (vb : vd : ve)) = False;

unblock_term :: forall a b. (Eq a) => a -> Term.Term a b -> Term.Term a b;
unblock_term f (Term.Fun g ts) =
  (if all (has_unary_root f) ts then Term.Fun g (map (strip_unary_root f) ts)
    else Term.Fun g ts);
unblock_term f (Term.Var v) = Term.Var v;

unblock_rule ::
  forall a b.
    (Eq a) => a -> (Term.Term a b, Term.Term a b) ->
                     (Term.Term a b, Term.Term a b);
unblock_rule f r = (unblock_term f (fst r), unblock_term f (snd r));

}
