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
import qualified Product_Type;
import qualified Term_Order;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified HOL;
import qualified Complexity;
import qualified Sum_Type;
import qualified Set;
import qualified Str;
import qualified Term_More;
import qualified Shows_Literal;
import qualified Sharp_Syntax;
import qualified Option;
import qualified Term;
import qualified Term_Order_Impl;
import qualified Option_Util;
import qualified Map_Choice;
import qualified Arith;
import qualified Compare;
import qualified Compare_Order_Instances;
import qualified Compare_Instances;

prc ::
  forall a.
    (Compare.Compare_order a) => [((a, Arith.Nat), Arith.Nat)] ->
                                   (a, Arith.Nat) ->
                                     (a, Arith.Nat) -> (Bool, Bool);
prc pr_list =
  Term_Order_Impl.prc_nat
    (Option_Util.fun_of_map (Map_Choice.ceta_map_of pr_list) Arith.zero_nat);

gwpo_s ::
  forall a b.
    (Term.Term a b -> Term.Term a b -> Bool) ->
      (Term.Term a b -> Term.Term a b -> Bool) ->
        ((a, Arith.Nat) -> (a, Arith.Nat) -> (Bool, Bool)) ->
          (a -> a) -> Term.Term a b -> Term.Term a b -> Bool;
gwpo_s cS cNS prc shp l r =
  not (Term.is_Var l) &&
    not (Term.is_Var r) &&
      (cS (Sharp_Syntax.sharp_term shp l) (Sharp_Syntax.sharp_term shp r) ||
        cNS (Sharp_Syntax.sharp_term shp l) (Sharp_Syntax.sharp_term shp r) &&
          fst (prc (Option.the (Term.root l)) (Option.the (Term.root r))));

gwpo_ns ::
  forall a b.
    (Eq a,
      Eq b) => (Term.Term a b -> Term.Term a b -> Bool) ->
                 (Term.Term a b -> Term.Term a b -> Bool) ->
                   ((a, Arith.Nat) -> (a, Arith.Nat) -> (Bool, Bool)) ->
                     (a -> a) -> Term.Term a b -> Term.Term a b -> Bool;
gwpo_ns cS cNS prc shp l r =
  Term.equal_term l r ||
    not (Term.is_Var l) &&
      not (Term.is_Var r) &&
        (cS (Sharp_Syntax.sharp_term shp l) (Sharp_Syntax.sharp_term shp r) ||
          cNS (Sharp_Syntax.sharp_term shp l) (Sharp_Syntax.sharp_term shp r) &&
            snd (prc (Option.the (Term.root l)) (Option.the (Term.root r))));

showsl_gwpo_params ::
  forall a.
    (Shows_Literal.Showl a) => ([((a, Arith.Nat), Arith.Nat)], a -> a) ->
                                 String -> String;
showsl_gwpo_params params =
  Shows_Literal.showsl_lit "precedence:\n" .
    Shows_Literal.showsl_sep
      (\ (f, p) ->
        (((Shows_Literal.showsl_lit "precedence(" .
            Term_Order_Impl.showsl_funa f) .
           Shows_Literal.showsl_lit ") = ") .
          Shows_Literal.showsl_nat p) .
          Shows_Literal.showsl_literal "\n")
      (Shows_Literal.showsl_literal "\n") (fst params);

gwpo_rel_impl ::
  forall a.
    (Compare.Compare_order a, Eq a,
      Shows_Literal.Showl a) => Term_Order_Impl.Rel_impl_ext a [Str.Char] () ->
                                  ([((a, Arith.Nat), Arith.Nat)], a -> a) ->
                                    Term_Order_Impl.Rel_impl_ext a [Str.Char]
                                      ();
gwpo_rel_impl rt params =
  (case params of {
    (pr_list, shp) ->
      let {
        s = (\ l r -> Error_Monad.isOK (Term_Order_Impl.s rt (l, r)));
        ns = (\ l r -> Error_Monad.isOK (Term_Order_Impl.ns rt (l, r)));
      } in Term_Order_Impl.Rel_impl_ext (Term_Order_Impl.rel_impl_redpair rt)
             (Sum_Type.Inl
               (Shows_Literal.showsl_lit "standard is not supported by GWPO"))
             (((Shows_Literal.showsl_lit
                  "quasi-reduction triple for GWPO with " .
                 showsl_gwpo_params params) .
                Shows_Literal.showsl_lit
                  "\nover the following reduction pair:\n") .
               Term_Order_Impl.desc rt)
             (\ (l, r) ->
               Check_Monad.check (gwpo_s s ns (prc pr_list) shp l r)
                 (Shows_Literal.showsl_lit "cannot strictly orient " .
                   Shows_Literal.showsl_prod (l, r)))
             (\ (l, r) ->
               Check_Monad.check (ns l r)
                 (Shows_Literal.showsl_lit "cannot weakly orient (nst)" .
                   Shows_Literal.showsl_prod (l, r)))
             (\ (l, r) ->
               Check_Monad.check (gwpo_ns s ns (prc pr_list) shp l r)
                 (Shows_Literal.showsl_lit "cannot weakly orient (ns)" .
                   Shows_Literal.showsl_prod (l, r)))
             Term_Order.full_af Term_Order.full_af (Sum_Type.Inr ())
             (Sum_Type.Inr ())
             (Sum_Type.Inl
               (Shows_Literal.showsl_lit "ce is not supported by GWPO"))
             (Sum_Type.Inl
               (Shows_Literal.showsl_lit "co rewrite is not supported by GWPO"))
             (Sum_Type.Inr ()) (Sum_Type.Inr ()) Term_Order.empty_af
             (\ _ ->
               Sum_Type.Inl
                 (Shows_Literal.showsl_lit "mono is not supported by GWPO"))
             Nothing Nothing Term_Order_Impl.no_complexity_check ();
  });

}
