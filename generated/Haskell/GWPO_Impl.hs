{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module GWPO_Impl(gwpo_rel_impl) where {

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
import qualified Sum_Type;
import qualified Sharp_Syntax;
import qualified Term_Rewriting;
import qualified Option_Util;
import qualified Map_Choice;
import qualified Compare;
import qualified Compare_Order_Instances;
import qualified Arith;

prc ::
  forall a.
    (Compare.Compare_order a) => [((a, Arith.Nat), Arith.Nat)] ->
                                   (a, Arith.Nat) ->
                                     (a, Arith.Nat) -> (Bool, Bool);
prc pr_list =
  Term_Rewriting.prc_nat
    (Option_Util.fun_of_map (Map_Choice.ceta_map_of pr_list) Arith.zero_nat);

gwpo_s ::
  forall a b.
    (Term_Rewriting.Term a b -> Term_Rewriting.Term a b -> Bool) ->
      (Term_Rewriting.Term a b -> Term_Rewriting.Term a b -> Bool) ->
        ((a, Arith.Nat) -> (a, Arith.Nat) -> (Bool, Bool)) ->
          (a -> a) ->
            Term_Rewriting.Term a b -> Term_Rewriting.Term a b -> Bool;
gwpo_s cS cNS prc shp l r =
  not (Term_Rewriting.is_Var l) &&
    not (Term_Rewriting.is_Var r) &&
      (cS (Sharp_Syntax.sharp_term shp l) (Sharp_Syntax.sharp_term shp r) ||
        cNS (Sharp_Syntax.sharp_term shp l) (Sharp_Syntax.sharp_term shp r) &&
          fst (prc (Arith.the (Term_Rewriting.root l))
                (Arith.the (Term_Rewriting.root r))));

gwpo_ns ::
  forall a b.
    (Eq a,
      Eq b) => (Term_Rewriting.Term a b -> Term_Rewriting.Term a b -> Bool) ->
                 (Term_Rewriting.Term a b -> Term_Rewriting.Term a b -> Bool) ->
                   ((a, Arith.Nat) -> (a, Arith.Nat) -> (Bool, Bool)) ->
                     (a -> a) ->
                       Term_Rewriting.Term a b ->
                         Term_Rewriting.Term a b -> Bool;
gwpo_ns cS cNS prc shp l r =
  Term_Rewriting.equal_term l r ||
    not (Term_Rewriting.is_Var l) &&
      not (Term_Rewriting.is_Var r) &&
        (cS (Sharp_Syntax.sharp_term shp l) (Sharp_Syntax.sharp_term shp r) ||
          cNS (Sharp_Syntax.sharp_term shp l) (Sharp_Syntax.sharp_term shp r) &&
            snd (prc (Arith.the (Term_Rewriting.root l))
                  (Arith.the (Term_Rewriting.root r))));

showsl_gwpo_params ::
  forall a.
    (Term_Rewriting.Showl a) => ([((a, Arith.Nat), Arith.Nat)], a -> a) ->
                                  String -> String;
showsl_gwpo_params params =
  Term_Rewriting.showsl_lit "precedence:\n" .
    Term_Rewriting.showsl_sep
      (\ (f, p) ->
        (((Term_Rewriting.showsl_lit "precedence(" .
            Term_Rewriting.showsl_funa f) .
           Term_Rewriting.showsl_lit ") = ") .
          Term_Rewriting.showsl_nat p) .
          Term_Rewriting.showsl_literal "\n")
      (Term_Rewriting.showsl_literal "\n") (fst params);

gwpo_rel_impl ::
  forall a.
    (Compare.Compare_order a, Eq a,
      Term_Rewriting.Showl a) => Term_Rewriting.Rel_impl_ext a [Arith.Char]
                                   () ->
                                   ([((a, Arith.Nat), Arith.Nat)], a -> a) ->
                                     Term_Rewriting.Rel_impl_ext a [Arith.Char]
                                       ();
gwpo_rel_impl rt params =
  (case params of {
    (pr_list, shp) ->
      let {
        s = (\ l r -> Error_Monad.isOK (Term_Rewriting.s rt (l, r)));
        ns = (\ l r -> Error_Monad.isOK (Term_Rewriting.ns rt (l, r)));
      } in Term_Rewriting.Rel_impl_ext (Term_Rewriting.rel_impl_redpair rt)
             (Sum_Type.Inl
               (Term_Rewriting.showsl_lit "standard is not supported by GWPO"))
             (((Term_Rewriting.showsl_lit
                  "quasi-reduction triple for GWPO with " .
                 showsl_gwpo_params params) .
                Term_Rewriting.showsl_lit
                  "\nover the following reduction pair:\n") .
               Term_Rewriting.desc rt)
             (\ (l, r) ->
               Check_Monad.check (gwpo_s s ns (prc pr_list) shp l r)
                 (Term_Rewriting.showsl_lit "cannot strictly orient " .
                   Term_Rewriting.showsl_prod (l, r)))
             (\ (l, r) ->
               Check_Monad.check (ns l r)
                 (Term_Rewriting.showsl_lit "cannot weakly orient (nst)" .
                   Term_Rewriting.showsl_prod (l, r)))
             (\ (l, r) ->
               Check_Monad.check (gwpo_ns s ns (prc pr_list) shp l r)
                 (Term_Rewriting.showsl_lit "cannot weakly orient (ns)" .
                   Term_Rewriting.showsl_prod (l, r)))
             Term_Order.full_af Term_Order.full_af (Sum_Type.Inr ())
             (Sum_Type.Inr ())
             (Sum_Type.Inl
               (Term_Rewriting.showsl_lit "ce is not supported by GWPO"))
             (Sum_Type.Inl
               (Term_Rewriting.showsl_lit
                 "co rewrite is not supported by GWPO"))
             (Sum_Type.Inr ()) (Sum_Type.Inr ()) Term_Order.empty_af
             (\ _ ->
               Sum_Type.Inl
                 (Term_Rewriting.showsl_lit "mono is not supported by GWPO"))
             Nothing Nothing Term_Rewriting.no_complexity_check ();
  });

}
