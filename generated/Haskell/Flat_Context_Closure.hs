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
import qualified Term_Rewriting;
import qualified Arith;

hole_at ::
  forall a b.
    (Eq a) => Arith.Nat -> Arith.Nat -> a -> Term_Rewriting.Actxt a b -> Bool;
hole_at n i f (Term_Rewriting.More g ss1 Term_Rewriting.Hole ss2) =
  g == f &&
    Arith.equal_nat (Arith.size_list ss1) i &&
      Arith.equal_nat (Arith.size_list ss2)
        (Arith.minus_nat (Arith.minus_nat n i) Arith.one_nat);
hole_at n i f Term_Rewriting.Hole = False;
hole_at n i f (Term_Rewriting.More v va (Term_Rewriting.More vd ve vf vg) vc) =
  False;

block_term ::
  forall a b. a -> Term_Rewriting.Term a b -> Term_Rewriting.Term a b;
block_term f (Term_Rewriting.Var x) = Term_Rewriting.Var x;
block_term f (Term_Rewriting.Fun g ts) =
  Term_Rewriting.Fun g (map (\ t -> Term_Rewriting.Fun f [t]) ts);

block_rule ::
  forall a b.
    a -> (Term_Rewriting.Term a b, Term_Rewriting.Term a b) ->
           (Term_Rewriting.Term a b, Term_Rewriting.Term a b);
block_rule f r = (block_term f (fst r), block_term f (snd r));

strip_unary_root ::
  forall a b. (Eq a) => a -> Term_Rewriting.Term a b -> Term_Rewriting.Term a b;
strip_unary_root f (Term_Rewriting.Fun g [t]) =
  (if f == g then t else Term_Rewriting.Fun g [t]);
strip_unary_root f (Term_Rewriting.Var v) = Term_Rewriting.Var v;
strip_unary_root f (Term_Rewriting.Fun v []) = Term_Rewriting.Fun v [];
strip_unary_root f (Term_Rewriting.Fun v (vb : vd : ve)) =
  Term_Rewriting.Fun v (vb : vd : ve);

has_unary_root :: forall a b. (Eq a) => a -> Term_Rewriting.Term a b -> Bool;
has_unary_root f (Term_Rewriting.Fun g [t]) = f == g;
has_unary_root f (Term_Rewriting.Var v) = False;
has_unary_root f (Term_Rewriting.Fun v []) = False;
has_unary_root f (Term_Rewriting.Fun v (vb : vd : ve)) = False;

unblock_term ::
  forall a b. (Eq a) => a -> Term_Rewriting.Term a b -> Term_Rewriting.Term a b;
unblock_term f (Term_Rewriting.Fun g ts) =
  (if all (has_unary_root f) ts
    then Term_Rewriting.Fun g (map (strip_unary_root f) ts)
    else Term_Rewriting.Fun g ts);
unblock_term f (Term_Rewriting.Var v) = Term_Rewriting.Var v;

unblock_rule ::
  forall a b.
    (Eq a) => a -> (Term_Rewriting.Term a b, Term_Rewriting.Term a b) ->
                     (Term_Rewriting.Term a b, Term_Rewriting.Term a b);
unblock_rule f r = (unblock_term f (fst r), unblock_term f (snd r));

}
