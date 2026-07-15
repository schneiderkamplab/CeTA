{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module SPO_Impl(mspo_rel_impl) where {

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
import qualified Term_Order;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified HOL;
import qualified Complexity;
import qualified Sum_Type;
import qualified Compare;
import qualified Arith;
import qualified Shows_Literal;
import qualified Lexicographic_Extension;
import qualified Term_Rewriting;

spo_ub ::
  forall a b.
    (Eq a,
      Eq b) => (Term_Rewriting.Term a b -> Term_Rewriting.Term a b -> Bool) ->
                 (Term_Rewriting.Term a b -> Term_Rewriting.Term a b -> Bool) ->
                   Term_Rewriting.Term a b -> Term_Rewriting.Term a b -> Bool;
spo_ub cS cNS (Term_Rewriting.Var uu) uv = False;
spo_ub cS cNS (Term_Rewriting.Fun f ss) t =
  any (\ si -> Term_Rewriting.equal_term si t || spo_ub cS cNS si t) ss ||
    (case t of {
      Term_Rewriting.Var _ -> False;
      Term_Rewriting.Fun _ ts ->
        all (spo_ub cS cNS (Term_Rewriting.Fun f ss)) ts &&
          (cS (Term_Rewriting.Fun f ss) t ||
            cNS (Term_Rewriting.Fun f ss) t &&
              fst (Lexicographic_Extension.lex_ext_unbounded
                    (\ s ta ->
                      (spo_ub cS cNS s ta, Term_Rewriting.equal_term s ta))
                    ss ts));
    });

mspo_ub ::
  forall a b.
    (Eq a,
      Eq b) => (Term_Rewriting.Term a b -> Term_Rewriting.Term a b -> Bool) ->
                 (Term_Rewriting.Term a b -> Term_Rewriting.Term a b -> Bool) ->
                   (Term_Rewriting.Term a b ->
                     Term_Rewriting.Term a b -> Bool) ->
                     Term_Rewriting.Term a b -> Term_Rewriting.Term a b -> Bool;
mspo_ub cS cNS cH s t = cH s t && spo_ub cS cNS s t;

mspo_rel_impl ::
  forall a.
    (Compare.Compare_order a, Eq a,
      Shows_Literal.Showl a) => Term_Rewriting.Rel_impl_ext a [Arith.Char] () ->
                                  Term_Rewriting.Rel_impl_ext a [Arith.Char] ();
mspo_rel_impl rt =
  let {
    s = (\ l r -> Error_Monad.isOK (Term_Rewriting.s rt (l, r)));
    ns = (\ l r -> Error_Monad.isOK (Term_Rewriting.nst rt (l, r)));
    h = (\ l r -> Error_Monad.isOK (Term_Rewriting.ns rt (l, r)));
    mspo_s =
      (\ lr ->
        Check_Monad.check (mspo_ub s ns h (fst lr) (snd lr))
          (Shows_Literal.showsl_lit "cannot strictly orient " .
            Shows_Literal.showsl_prod lr));
    mspo_ns =
      (\ (l, r) ->
        Check_Monad.check (Term_Rewriting.equal_term l r || mspo_ub s ns h l r)
          (Shows_Literal.showsl_lit "cannot weakly orient " .
            Shows_Literal.showsl_prod (l, r)));
  } in Term_Rewriting.Rel_impl_ext
         (Term_Rewriting.rel_impl_quasi_reduction_triple rt) (Sum_Type.Inr ())
         (Shows_Literal.showsl_lit
            "MSPO over the following quasi-reduction triple:\n" .
           Term_Rewriting.desc rt)
         mspo_s mspo_ns mspo_ns Term_Order.full_af Term_Order.full_af
         (Sum_Type.Inr ()) (Sum_Type.Inr ())
         (Sum_Type.Inl (Shows_Literal.showsl_lit "ce is not supported by MSPO"))
         (Sum_Type.Inl
           (Shows_Literal.showsl_lit "co rewrite is not supported by MSPO"))
         (Sum_Type.Inl
           (Shows_Literal.showsl_lit "top-mono is not supported by MSPO"))
         (Sum_Type.Inl
           (Shows_Literal.showsl_lit "top-refl is not supported by MSPO"))
         Term_Order.empty_af (\ _ -> Sum_Type.Inr ()) Nothing Nothing
         Term_Rewriting.no_complexity_check ();

}
