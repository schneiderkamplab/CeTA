{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  CSR_Checker(Csr_dp_termination_proof(..), Csr_termination_proof(..),
               check_csr_termination_proof)
  where {

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
import qualified QDP_Framework_Impl;
import qualified FOR_Preliminaries;
import qualified Termination_Problem_Spec;
import qualified Countable;
import qualified Mapping;
import qualified Usable_Rules_Impl;
import qualified Dependency_Pair_Problem_Spec;
import qualified Map_Choice;
import qualified Set_Interval;
import qualified List_Order_Implementations;
import qualified Matrix_Core_Order_Impl;
import qualified Max_Polynomial;
import qualified Max_Monus;
import qualified Polynomials;
import qualified WPO;
import qualified Matrix;
import qualified Compare_Order_Instances;
import qualified Linear_Poly_Order;
import qualified Matrix_Poly;
import qualified Linear_Poly_Complexity;
import qualified Ordered_Semiring;
import qualified Congruence;
import qualified Group;
import qualified Ring;
import qualified Usable_Replacement_Map_Impl;
import qualified Error_Monad;
import qualified Check_Monad;
import qualified Sum_Type;
import qualified Context_Sensitive_Impl;
import qualified Sharp_Syntax;
import qualified HOL;
import qualified Compare;
import qualified Check_Termination;
import qualified Subterm_Criterion_Impl;
import qualified Arith;
import qualified Reduction_Pair_Implementations;
import qualified Labelings;
import qualified Term_Rewriting;

data Csr_dp_termination_proof a b c = CSR_DP_P_is_Empty
  | CSR_DP_Ordinary_Proof (Check_Termination.Dp_termination_proof a b c)
  | CSR_DP_Subterm_Criterion_Proc
      (Subterm_Criterion_Impl.ProjL (Labelings.Lab a b))
      [((Term_Rewriting.Term (Labelings.Lab a b) c,
          Term_Rewriting.Term (Labelings.Lab a b) c),
         [([Arith.Nat],
            ((Term_Rewriting.Term (Labelings.Lab a b) c,
               Term_Rewriting.Term (Labelings.Lab a b) c),
              Term_Rewriting.Term (Labelings.Lab a b) c))])]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Csr_dp_termination_proof a b c)
  | CSR_DP_Gen_Subterm_Criterion_Proc
      [((Labelings.Lab a b, Arith.Nat), [Arith.Nat])]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Csr_dp_termination_proof a b c)
  | CSR_DP_Usable_Rules_Proc
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Csr_dp_termination_proof a b c)
  | CSR_DP_Dep_Graph_Proc
      [(Maybe (Csr_dp_termination_proof a b c),
         [(Term_Rewriting.Term (Labelings.Lab a b) c,
            Term_Rewriting.Term (Labelings.Lab a b) c)])]
  | CSR_DP_Size_Change_Subterm_Proc
      [((Term_Rewriting.Term (Labelings.Lab a b) c,
          Term_Rewriting.Term (Labelings.Lab a b) c),
         ([(Arith.Nat, Arith.Nat)], [(Arith.Nat, Arith.Nat)]))];

data Csr_termination_proof a b c = CSR_R_is_Empty
  | CSR_Rule_Removal
      (Reduction_Pair_Implementations.Redtriple_impl (Labelings.Lab a b))
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Csr_termination_proof a b c)
  | CSR_Dependency_Pairs
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Csr_dp_termination_proof a b c);

is_sharp_lab :: forall a b. Labelings.Lab a b -> Bool;
is_sharp_lab (Labelings.Sharp f) = True;
is_sharp_lab (Labelings.UnLab f) = False;
is_sharp_lab (Labelings.Lab f l) = False;
is_sharp_lab (Labelings.FunLab f ls) = False;

mu_fun_poss_list ::
  forall a b.
    (Eq a) => [((a, Arith.Nat), [Arith.Nat])] ->
                Term_Rewriting.Term a b -> [[Arith.Nat]];
mu_fun_poss_list mu (Term_Rewriting.Var x) = [];
mu_fun_poss_list mu (Term_Rewriting.Fun f ts) =
  [] : concat
         (Arith.map_filter
           (\ x ->
             (if Arith.member x
                   (Context_Sensitive_Impl.mu_of mu (f, Arith.size_list ts))
               then Just (map (\ a -> x : a)
                           (mu_fun_poss_list mu (Arith.nth ts x)))
               else Nothing))
           (Arith.upt Arith.zero_nat (Arith.size_list ts)));

mu_poss_list ::
  forall a b.
    (Eq a) => [((a, Arith.Nat), [Arith.Nat])] ->
                Term_Rewriting.Term a b -> [[Arith.Nat]];
mu_poss_list mu (Term_Rewriting.Var x) = [[]];
mu_poss_list mu (Term_Rewriting.Fun f ts) =
  [] : concat
         (Arith.map_filter
           (\ x ->
             (if Arith.member x
                   (Context_Sensitive_Impl.mu_of mu (f, Arith.size_list ts))
               then Just (map (\ a -> x : a) (mu_poss_list mu (Arith.nth ts x)))
               else Nothing))
           (Arith.upt Arith.zero_nat (Arith.size_list ts)));

mu_supt_list ::
  forall a b.
    (Eq a) => [((a, Arith.Nat), [Arith.Nat])] ->
                Term_Rewriting.Term a b -> [Term_Rewriting.Term a b];
mu_supt_list mu s =
  Arith.map_filter
    (\ x ->
      (if not (null x) then Just (Term_Rewriting.subt_at s x) else Nothing))
    (mu_poss_list mu s);

mu_CSDP_list ::
  forall a b.
    (Compare.Compare_order a, Eq a, Term_Rewriting.Showl a,
      Eq b) => (a -> a) ->
                 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                   [((a, Arith.Nat), [Arith.Nat])] ->
                     [(a, Arith.Nat)] ->
                       [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
mu_CSDP_list shp r mu d_list =
  concatMap
    (\ lr ->
      let {
        l = fst lr;
        ra = snd lr;
        s = Sharp_Syntax.sharp_term shp l;
      } in Arith.map_filter
             (\ x ->
               (if not (Arith.membera (mu_supt_list mu l)
                         (Term_Rewriting.subt_at ra x)) &&
                     (case Term_Rewriting.subt_at ra x of {
                       Term_Rewriting.Var _ -> False;
                       Term_Rewriting.Fun f ts ->
                         Arith.membera d_list (f, Arith.size_list ts);
                     })
                 then Just (s, Sharp_Syntax.sharp_term shp
                                 (Term_Rewriting.subt_at ra x))
                 else Nothing))
             (mu_fun_poss_list mu ra))
    r;

safe_CSDP_list ::
  forall a b.
    (Compare.Compare_order a, Eq a, Term_Rewriting.Showl a,
      Eq b) => (a -> a) ->
                 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                   [(a, Arith.Nat)] ->
                     [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
safe_CSDP_list shp r d_list =
  concatMap
    (\ lr ->
      let {
        l = fst lr;
        s = Sharp_Syntax.sharp_term shp l;
      } in Arith.map_filter
             (\ x ->
               (if not (Term_Rewriting.supt_impl l x) &&
                     not (Term_Rewriting.is_Var x) &&
                       Arith.membera d_list (Arith.the (Term_Rewriting.root x))
                 then Just (s, Sharp_Syntax.sharp_term shp x) else Nothing))
             (Term_Rewriting.supteq_list (snd lr)))
    r;

csr_mu_mono_check ::
  forall a.
    (Compare.Compare_order a, Eq a,
      Term_Rewriting.Showl a) => [((a, Arith.Nat), [Arith.Nat])] ->
                                   ((a, Arith.Nat) -> Arith.Set Arith.Nat) ->
                                     [(a, Arith.Nat)] ->
                                       Sum_Type.Sum (String -> String) ();
csr_mu_mono_check mu monof fs =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ f ->
        Check_Monad.check
          (Arith.less_eq_set (Context_Sensitive_Impl.mu_of mu f) (monof f))
          (((((Term_Rewriting.showsl_lit
                 "error in CSR monotonicity: replacement map for " .
                Term_Rewriting.showsl_prod f) .
               Term_Rewriting.showsl_lit " is ") .
              Usable_Replacement_Map_Impl.showsl_position_set f
                (Context_Sensitive_Impl.mu_of mu f)) .
             Term_Rewriting.showsl_lit
               "\nbut the order is monotone only in positions ") .
            Usable_Replacement_Map_Impl.showsl_position_set f (monof f)))
      fs)
    (\ x -> Sum_Type.Inl (snd x));

mu_vars_term_list ::
  forall a b.
    (Eq a) => [((a, Arith.Nat), [Arith.Nat])] -> Term_Rewriting.Term a b -> [b];
mu_vars_term_list mu (Term_Rewriting.Var x) = [x];
mu_vars_term_list mu (Term_Rewriting.Fun f ts) =
  concat
    (Arith.map_filter
      (\ x ->
        (if Arith.member x
              (Context_Sensitive_Impl.mu_of mu (f, Arith.size_list ts))
          then Just (mu_vars_term_list mu (Arith.nth ts x)) else Nothing))
      (Arith.upt Arith.zero_nat (Arith.size_list ts)));

csr_sharp_mu_entry_ok ::
  forall a b. ((Labelings.Lab a b, Arith.Nat), [Arith.Nat]) -> Bool;
csr_sharp_mu_entry_ok e =
  (case e of {
    ((f, n), is) ->
      not (is_sharp_lab f) &&
        Arith.less_eq_set (Arith.set is)
          (Set_Interval.atLeastLessThan Arith.zero_nat n);
  });

csr_sharp_mu_check ::
  forall a b.
    (Compare.Compare_order a, Term_Rewriting.Showl a,
      Term_Rewriting.Showl b) => [((Labelings.Lab a b, Arith.Nat),
                                    [Arith.Nat])] ->
                                   Sum_Type.Sum (String -> String) ();
csr_sharp_mu_check mu =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ e ->
        Check_Monad.check (csr_sharp_mu_entry_ok e)
          (case e of {
            ((f, n), _) ->
              ((Term_Rewriting.showsl_lit
                  "invalid replacement map entry for CSR-DP sharp side steps: " .
                 Term_Rewriting.showsl_lab f) .
                Term_Rewriting.showsl_lit "/") .
                Term_Rewriting.showsl_nat n;
          }))
      mu)
    (\ x -> Sum_Type.Inl (snd x));

csr_int_mu_mono_check ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Compare.Compare_order b, Eq b,
      Term_Rewriting.Showl b) => HOL.Itself a ->
                                   HOL.Itself b ->
                                     [((b, Arith.Nat),
(Arith.Int, [Arith.Int]))] ->
                                       [((b, Arith.Nat), [Arith.Nat])] ->
 Sum_Type.Sum (String -> String) ();
csr_int_mu_mono_check HOL.Type uu i mu =
  csr_mu_mono_check mu
    (Term_Rewriting.mono_af
      ((Linear_Poly_Order.create_poly_rel_impl ::
         Congruence.Partial_object_ext Arith.Int
           (Group.Monoid_ext Arith.Int
             (Ring.Ring_ext Arith.Int
               (Ordered_Semiring.Ordered_semiring_ext Arith.Int
                 (Linear_Poly_Complexity.Lpoly_order_semiring_ext Arith.Int
                   ())))) ->
           Sum_Type.Sum (String -> String) () ->
             [((b, Arith.Nat), (Arith.Int, [Arith.Int]))] ->
               Term_Rewriting.Rel_impl_ext b a ())
        (Matrix_Poly.class_lpoly_order Arith.one_int Term_Rewriting.int_mono
          (\ x y -> Arith.less_int y x))
        (Sum_Type.Inr ()) i))
    (Arith.remdups (map fst i ++ map fst mu));

csr_rule_removal_af_tt ::
  forall a b.
    (Compare.Compare_order a, Eq a, Term_Rewriting.Showl a,
      Compare.Compare_order b,
      Term_Rewriting.Showl b) => Term_Rewriting.Rel_impl_ext a b () ->
                                   [(a, Arith.Nat)] ->
                                     [((a, Arith.Nat), [Arith.Nat])] ->
                                       [(Term_Rewriting.Term a b,
  Term_Rewriting.Term a b)] ->
 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
   Sum_Type.Sum (String -> String)
     [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
csr_rule_removal_af_tt rp fs mu rremove r =
  let {
    rr = Map_Choice.ceta_list_diff r rremove;
  } in (case Error_Monad.catch_error
               (Error_Monad.bind (Term_Rewriting.rel_impl_redpair rp)
                 (\ _ ->
                   Error_Monad.bind
                     (Error_Monad.catch_error
                       (Error_Monad.forallM
                         (\ f ->
                           Check_Monad.check
                             (Arith.less_eq_set
                               (Context_Sensitive_Impl.mu_of mu f)
                               (Term_Rewriting.mono_af rp f))
                             (((((Term_Rewriting.showsl_lit
                                    "error in CSR monotonicity: replacement map for " .
                                   Term_Rewriting.showsl_prod f) .
                                  Term_Rewriting.showsl_lit " is ") .
                                 Usable_Replacement_Map_Impl.showsl_position_set
                                   f (Context_Sensitive_Impl.mu_of mu f)) .
                                Term_Rewriting.showsl_lit
                                  "\nbut the order is monotone only in positions ") .
                               Usable_Replacement_Map_Impl.showsl_position_set f
                                 (Term_Rewriting.mono_af rp f)))
                         fs)
                       (\ x -> Sum_Type.Inl (snd x)))
                     (\ _ ->
                       Error_Monad.bind
                         (Error_Monad.catch_error
                           (Term_Rewriting.rel_impl_s rp rremove)
                           (\ x ->
                             Sum_Type.Inl
                               (Term_Rewriting.showsl_lit
                                  "problem when orienting strict CSR rules\n" .
                                 x)))
                         (\ _ ->
                           Error_Monad.catch_error
                             (Term_Rewriting.rel_impl_ns rp rr)
                             (\ x ->
                               Sum_Type.Inl
                                 (Term_Rewriting.showsl_lit
                                    "problem when orienting remaining CSR rules\n" .
                                   x))))))
               (\ x ->
                 Sum_Type.Inl
                   (((Term_Rewriting.showsl_lit
                        "could not apply the CSR rule removal processor with replacement-map monotonicity and the following\n" .
                       Term_Rewriting.desc rp) .
                      Term_Rewriting.showsl_literal "\n") .
                     x))
         of {
         Sum_Type.Inl a -> Sum_Type.Inl a;
         Sum_Type.Inr _ -> Sum_Type.Inr rr;
       });

csr_int_rule_removal_tt ::
  forall a b.
    (Compare.Compare_order a, Eq a, Term_Rewriting.Showl a,
      Compare.Compare_order b, Eq b,
      Term_Rewriting.Showl b) => [((a, Arith.Nat), (Arith.Int, [Arith.Int]))] ->
                                   [((a, Arith.Nat), [Arith.Nat])] ->
                                     [(Term_Rewriting.Term a b,
Term_Rewriting.Term a b)] ->
                                       [(Term_Rewriting.Term a b,
  Term_Rewriting.Term a b)] ->
 Sum_Type.Sum (String -> String)
   [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
csr_int_rule_removal_tt i mu rremove r =
  let {
    fs = Arith.remdups (map fst i ++ map fst mu);
    rp = Linear_Poly_Order.create_poly_rel_impl
           (Matrix_Poly.class_lpoly_order Arith.one_int Term_Rewriting.int_mono
             (\ x y -> Arith.less_int y x))
           (Sum_Type.Inr ()) i;
  } in Error_Monad.bind
         ((csr_int_mu_mono_check ::
            HOL.Itself a ->
              HOL.Itself a ->
                [((a, Arith.Nat), (Arith.Int, [Arith.Int]))] ->
                  [((a, Arith.Nat), [Arith.Nat])] ->
                    Sum_Type.Sum (String -> String) ())
           HOL.Type HOL.Type i mu)
         (\ _ -> csr_rule_removal_af_tt rp fs mu rremove r);

csr_rule_removal_impl ::
  forall a.
    (Compare.Compare_order a, Eq a,
      Term_Rewriting.Showl a) => Reduction_Pair_Implementations.Redtriple_impl
                                   a ->
                                   [((a, Arith.Nat), [Arith.Nat])] ->
                                     [(Term_Rewriting.Term a [Arith.Char],
Term_Rewriting.Term a [Arith.Char])] ->
                                       [(Term_Rewriting.Term a [Arith.Char],
  Term_Rewriting.Term a [Arith.Char])] ->
 Sum_Type.Sum (String -> String)
   [(Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char])];
csr_rule_removal_impl (Reduction_Pair_Implementations.Int_carrier i) mu rremove
  r = csr_int_rule_removal_tt i mu rremove r;
csr_rule_removal_impl (Reduction_Pair_Implementations.Int_nl_carrier v) mu
  rremove r =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit "unsupported CSR rule-removal redpair");
csr_rule_removal_impl (Reduction_Pair_Implementations.Neg_Integer_Poly v) mu
  rremove r =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit "unsupported CSR rule-removal redpair");
csr_rule_removal_impl (Reduction_Pair_Implementations.Rat_carrier v) mu rremove
  r = Sum_Type.Inl
        (Term_Rewriting.showsl_lit "unsupported CSR rule-removal redpair");
csr_rule_removal_impl (Reduction_Pair_Implementations.Rat_nl_carrier v va) mu
  rremove r =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit "unsupported CSR rule-removal redpair");
csr_rule_removal_impl (Reduction_Pair_Implementations.Real_carrier v) mu rremove
  r = Sum_Type.Inl
        (Term_Rewriting.showsl_lit "unsupported CSR rule-removal redpair");
csr_rule_removal_impl (Reduction_Pair_Implementations.Real_nl_carrier v va) mu
  rremove r =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit "unsupported CSR rule-removal redpair");
csr_rule_removal_impl (Reduction_Pair_Implementations.Arctic_carrier v) mu
  rremove r =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit "unsupported CSR rule-removal redpair");
csr_rule_removal_impl (Reduction_Pair_Implementations.Arctic_rat_carrier v) mu
  rremove r =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit "unsupported CSR rule-removal redpair");
csr_rule_removal_impl (Reduction_Pair_Implementations.Int_mat_carrier v va vb)
  mu rremove r =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit "unsupported CSR rule-removal redpair");
csr_rule_removal_impl (Reduction_Pair_Implementations.Rat_mat_carrier v va vb)
  mu rremove r =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit "unsupported CSR rule-removal redpair");
csr_rule_removal_impl (Reduction_Pair_Implementations.Real_mat_carrier v va vb)
  mu rremove r =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit "unsupported CSR rule-removal redpair");
csr_rule_removal_impl (Reduction_Pair_Implementations.Core_matrix v) mu rremove
  r = Sum_Type.Inl
        (Term_Rewriting.showsl_lit "unsupported CSR rule-removal redpair");
csr_rule_removal_impl (Reduction_Pair_Implementations.Core_matrix_delta v va) mu
  rremove r =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit "unsupported CSR rule-removal redpair");
csr_rule_removal_impl (Reduction_Pair_Implementations.Arctic_mat_carrier v va)
  mu rremove r =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit "unsupported CSR rule-removal redpair");
csr_rule_removal_impl
  (Reduction_Pair_Implementations.Arctic_rat_mat_carrier v va) mu rremove r =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit "unsupported CSR rule-removal redpair");
csr_rule_removal_impl (Reduction_Pair_Implementations.RPO v va) mu rremove r =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit "unsupported CSR rule-removal redpair");
csr_rule_removal_impl (Reduction_Pair_Implementations.KBO v va) mu rremove r =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit "unsupported CSR rule-removal redpair");
csr_rule_removal_impl (Reduction_Pair_Implementations.ACKBO v va) mu rremove r =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit "unsupported CSR rule-removal redpair");
csr_rule_removal_impl (Reduction_Pair_Implementations.WPO v va) mu rremove r =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit "unsupported CSR rule-removal redpair");
csr_rule_removal_impl (Reduction_Pair_Implementations.GWPO v va) mu rremove r =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit "unsupported CSR rule-removal redpair");
csr_rule_removal_impl (Reduction_Pair_Implementations.MSPO v) mu rremove r =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit "unsupported CSR rule-removal redpair");
csr_rule_removal_impl (Reduction_Pair_Implementations.COWPO v va) mu rremove r =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit "unsupported CSR rule-removal redpair");
csr_rule_removal_impl (Reduction_Pair_Implementations.Max_poly v) mu rremove r =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit "unsupported CSR rule-removal redpair");
csr_rule_removal_impl (Reduction_Pair_Implementations.Max_monus v) mu rremove r
  = Sum_Type.Inl
      (Term_Rewriting.showsl_lit "unsupported CSR rule-removal redpair");
csr_rule_removal_impl (Reduction_Pair_Implementations.Filtered_Redtriple v va)
  mu rremove r =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit "unsupported CSR rule-removal redpair");
csr_rule_removal_impl (Reduction_Pair_Implementations.SCNP v va vb) mu rremove r
  = Sum_Type.Inl
      (Term_Rewriting.showsl_lit "unsupported CSR rule-removal redpair");

csr_mu_usable_rules_proc ::
  forall a b c.
    (Compare.Compare_order b, Eq b, Term_Rewriting.Showl b,
      Compare.Compare_order c, Eq c,
      Term_Rewriting.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b c
                                   () ->
                                   [((b, Arith.Nat), [Arith.Nat])] ->
                                     [(Term_Rewriting.Term b c,
Term_Rewriting.Term b c)] ->
                                       a -> Sum_Type.Sum (String -> String) a;
csr_mu_usable_rules_proc j mu u dpp =
  (case Error_Monad.bind
          (Error_Monad.catch_error
            (Error_Monad.forallM
              (\ (l, _) ->
                Check_Monad.check (not (Term_Rewriting.is_Var l))
                  (Term_Rewriting.showsl_lit "variables as lhss not allowed"))
              (Dependency_Pair_Problem_Spec.rules j dpp))
            (\ x -> Sum_Type.Inl (snd x)))
          (\ _ ->
            Error_Monad.catch_error
              (Usable_Rules_Impl.check_ur_P_closed_rm_af
                (Dependency_Pair_Problem_Spec.rules_map j dpp) u
                (Context_Sensitive_Impl.mu_of mu)
                (Dependency_Pair_Problem_Spec.pairs j dpp))
              (\ x ->
                Sum_Type.Inl
                  (Term_Rewriting.showsl_lit
                     "error when checking CSR usable-rule closure\n" .
                    x)))
    of {
    Sum_Type.Inl a -> Sum_Type.Inl a;
    Sum_Type.Inr _ ->
      Sum_Type.Inr (Dependency_Pair_Problem_Spec.intersect_rules j dpp u);
  });

rhs_mu_vars_condition_list ::
  forall a b.
    (Eq a,
      Eq b) => [((a, Arith.Nat), [Arith.Nat])] ->
                 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] -> Bool;
rhs_mu_vars_condition_list mu r =
  all (\ (l, ra) ->
        all (Arith.membera (mu_vars_term_list mu l)) (mu_vars_term_list mu ra))
    r;

mu_csr_dependency_pairs_tt ::
  forall a b c.
    (Compare.Compare_order a, Eq a, Term_Rewriting.Showl a, Arith.Ccompare c,
      Compare.Compare_order c, Eq c, Mapping.Mapping_impl c,
      Term_Rewriting.Showl c) => (a -> a) ->
                                   Dependency_Pair_Problem_Spec.Dpp_ops_ext b a
                                     c () ->
                                     [((a, Arith.Nat), [Arith.Nat])] ->
                                       [(Term_Rewriting.Term a c,
  Term_Rewriting.Term a c)] ->
 [(Term_Rewriting.Term a c, Term_Rewriting.Term a c)] ->
   Sum_Type.Sum (String -> String) b;
mu_csr_dependency_pairs_tt shp j mu r p =
  let {
    d = Term_Rewriting.defined_list r;
  } in (case Error_Monad.catch_error
               (Error_Monad.bind (Term_Rewriting.check_wf_trs r)
                 (\ _ ->
                   Error_Monad.bind
                     (Check_Monad.check (rhs_mu_vars_condition_list mu r)
                       (Term_Rewriting.showsl_lit
                         "the RHS of a CSR rule contains a variable in an active position that is not active in the LHS\n"))
                     (\ _ ->
                       Error_Monad.bind
                         (Error_Monad.catch_error
                           (Error_Monad.forallM
                             (\ (f, n) ->
                               Check_Monad.check
                                 (not (Arith.membera d (shp f, n)))
                                 (((Term_Rewriting.showsl_lit "sharping " .
                                     Term_Rewriting.showsl f) .
                                    Term_Rewriting.showsl_lit
                                      " yields the defined symbol ") .
                                   Term_Rewriting.showsl (shp f)))
                             d)
                           (\ x -> Sum_Type.Inl (snd x)))
                         (\ _ ->
                           let {
                             pa = Arith.set p;
                           } in Error_Monad.catch_error
                                  (Error_Monad.catch_error
                                    (Error_Monad.forallM
                                      (\ x ->
(if Arith.member x pa || any (Term_Rewriting.eq_rule_mod_vars x) p
  then Sum_Type.Inr () else Sum_Type.Inl x))
                                      (mu_CSDP_list shp r mu d))
                                    (\ x -> Sum_Type.Inl (snd x)))
                                  (\ x ->
                                    Sum_Type.Inl
                                      ((Term_Rewriting.showsl_lit
  "the replacement-map-specific CS-DP " .
 Term_Rewriting.showsl_rule x) .
Term_Rewriting.showsl_lit " does not appear in the DP problem\n"))))))
               (\ x ->
                 Sum_Type.Inl
                   (Term_Rewriting.showsl_lit
                      "the replacement-map-specific CS-DP transformation is not applied correctly.\n" .
                     x))
         of {
         Sum_Type.Inl a -> Sum_Type.Inl a;
         Sum_Type.Inr _ ->
           Sum_Type.Inr
             (Dependency_Pair_Problem_Spec.mk j False False p [] [] [] r);
       });

dp_proof_of_csr_dp_termination_proof ::
  forall a b c.
    Csr_dp_termination_proof a b c ->
      Check_Termination.Dp_termination_proof a b c;
dp_proof_of_csr_dp_termination_proof CSR_DP_P_is_Empty =
  Check_Termination.P_is_Empty;
dp_proof_of_csr_dp_termination_proof (CSR_DP_Ordinary_Proof prf) = prf;
dp_proof_of_csr_dp_termination_proof
  (CSR_DP_Subterm_Criterion_Proc p rseq pr prf) =
  Check_Termination.Subterm_Criterion_Proc p rseq pr
    (dp_proof_of_csr_dp_termination_proof prf);
dp_proof_of_csr_dp_termination_proof
  (CSR_DP_Gen_Subterm_Criterion_Proc p pr prf) =
  Check_Termination.Gen_Subterm_Criterion_Proc p pr
    (dp_proof_of_csr_dp_termination_proof prf);
dp_proof_of_csr_dp_termination_proof (CSR_DP_Usable_Rules_Proc u prf) =
  Check_Termination.Usable_Rules_Proc u
    (dp_proof_of_csr_dp_termination_proof prf);
dp_proof_of_csr_dp_termination_proof (CSR_DP_Dep_Graph_Proc edpts) =
  Check_Termination.Dep_Graph_Proc
    (map (\ (prf, a) ->
           (Arith.map_option dp_proof_of_csr_dp_termination_proof prf, a))
      edpts);
dp_proof_of_csr_dp_termination_proof (CSR_DP_Size_Change_Subterm_Proc graphs) =
  Check_Termination.Size_Change_Subterm_Proc graphs;

check_csr_dp_termination_proof ::
  forall a b c.
    (Compare.Compare_order b, Countable.Countable b, Eq b,
      Term_Rewriting.Showl b) => Termination_Problem_Spec.Tp_ops_ext a
                                   (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                   () ->
                                   Dependency_Pair_Problem_Spec.Dpp_ops_ext c
                                     (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                     () ->
                                     Bool ->
                                       (String -> String) ->
 c -> Csr_dp_termination_proof b [Arith.Nat] [Arith.Char] ->
        Sum_Type.Sum (String -> String) ();
check_csr_dp_termination_proof ia j a i dpp prf =
  Check_Termination.check_dp_termination_proof ia j a i dpp
    (dp_proof_of_csr_dp_termination_proof prf);

check_csr_dp_termination_proof_core ::
  forall a b c.
    (Compare.Compare_order b, Countable.Countable b, Eq b,
      Term_Rewriting.Showl b) => Termination_Problem_Spec.Tp_ops_ext a
                                   (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                   () ->
                                   Dependency_Pair_Problem_Spec.Dpp_ops_ext c
                                     (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                     () ->
                                     [((Labelings.Lab b [Arith.Nat], Arith.Nat),
[Arith.Nat])] ->
                                       Bool ->
 (String -> String) ->
   c -> Csr_dp_termination_proof b [Arith.Nat] [Arith.Char] ->
          Sum_Type.Sum (String -> String) ();
check_csr_dp_termination_proof_core ia j mu a i dpp CSR_DP_P_is_Empty =
  FOR_Preliminaries.debug i "CSR-DP P is empty"
    (if null (Dependency_Pair_Problem_Spec.pairs j dpp) then Sum_Type.Inr ()
      else Sum_Type.Inl
             ((i . Term_Rewriting.showsl_lit
                     ": CSR-DP P is not empty in the following DP-problem\n") .
               QDP_Framework_Impl.showsl_dpp j dpp));
check_csr_dp_termination_proof_core ia j mu a i dpp (CSR_DP_Ordinary_Proof prf)
  = check_csr_dp_termination_proof ia j a i dpp (CSR_DP_Ordinary_Proof prf);
check_csr_dp_termination_proof_core ia j mu a i dpp
  (CSR_DP_Subterm_Criterion_Proc p rseq pr prf) =
  check_csr_dp_termination_proof ia j a i dpp
    (CSR_DP_Subterm_Criterion_Proc p rseq pr prf);
check_csr_dp_termination_proof_core ia j mu a i dpp
  (CSR_DP_Gen_Subterm_Criterion_Proc p pr prf) =
  check_csr_dp_termination_proof ia j a i dpp
    (CSR_DP_Gen_Subterm_Criterion_Proc p pr prf);
check_csr_dp_termination_proof_core ia j mu a i dpp
  (CSR_DP_Usable_Rules_Proc u prf) =
  FOR_Preliminaries.debug i "CSR-DP usable rules"
    (Error_Monad.bind
      (Error_Monad.catch_error (csr_mu_usable_rules_proc j mu u dpp)
        (\ x ->
          Sum_Type.Inl
            ((i . Term_Rewriting.showsl_lit
                    ": error when applying CSR usable rules\n") .
              x)))
      (\ dppa ->
        Error_Monad.bind
          (Error_Monad.catch_error
            (Error_Monad.forallM
              (\ lr ->
                Check_Monad.check (Arith.membera u lr)
                  ((i . Term_Rewriting.showsl_lit
                          ": conservative CSR usable-rules checker requires the usable rules to contain ") .
                    Term_Rewriting.showsl_rule lr))
              (Dependency_Pair_Problem_Spec.rules j dpp))
            (\ x -> Sum_Type.Inl (snd x)))
          (\ _ ->
            Error_Monad.catch_error
              (check_csr_dp_termination_proof_core ia j mu a
                (Term_Rewriting.add_index i Arith.one_nat) dppa prf)
              (\ x ->
                Sum_Type.Inl
                  ((i . Term_Rewriting.showsl_lit
                          ": error below CSR usable rules\n") .
                    x)))));
check_csr_dp_termination_proof_core ia j mu a i dpp
  (CSR_DP_Dep_Graph_Proc edpts) =
  check_csr_dp_termination_proof ia j a i dpp (CSR_DP_Dep_Graph_Proc edpts);
check_csr_dp_termination_proof_core ia j mu a i dpp
  (CSR_DP_Size_Change_Subterm_Proc graphs) =
  check_csr_dp_termination_proof ia j a i dpp
    (CSR_DP_Size_Change_Subterm_Proc graphs);

safe_csr_dependency_pairs_tt ::
  forall a b c.
    (Compare.Compare_order a, Eq a, Term_Rewriting.Showl a, Arith.Ccompare c,
      Compare.Compare_order c, Eq c, Mapping.Mapping_impl c,
      Term_Rewriting.Showl c) => (a -> a) ->
                                   Dependency_Pair_Problem_Spec.Dpp_ops_ext b a
                                     c () ->
                                     [((a, Arith.Nat), [Arith.Nat])] ->
                                       [(Term_Rewriting.Term a c,
  Term_Rewriting.Term a c)] ->
 [(Term_Rewriting.Term a c, Term_Rewriting.Term a c)] ->
   Sum_Type.Sum (String -> String) b;
safe_csr_dependency_pairs_tt shp j mu r p =
  let {
    d = Term_Rewriting.defined_list r;
  } in (case Error_Monad.catch_error
               (Error_Monad.bind (Term_Rewriting.check_wf_trs r)
                 (\ _ ->
                   Error_Monad.bind
                     (Error_Monad.catch_error
                       (Error_Monad.forallM
                         (\ (f, n) ->
                           Check_Monad.check (not (Arith.membera d (shp f, n)))
                             (((Term_Rewriting.showsl_lit "sharping " .
                                 Term_Rewriting.showsl f) .
                                Term_Rewriting.showsl_lit
                                  " yields the defined symbol ") .
                               Term_Rewriting.showsl (shp f)))
                         d)
                       (\ x -> Sum_Type.Inl (snd x)))
                     (\ _ ->
                       let {
                         pa = Arith.set p;
                       } in Error_Monad.catch_error
                              (Error_Monad.catch_error
                                (Error_Monad.forallM
                                  (\ x ->
                                    (if Arith.member x pa ||
  any (Term_Rewriting.eq_rule_mod_vars x) p
                                      then Sum_Type.Inr () else Sum_Type.Inl x))
                                  (safe_CSDP_list shp r d))
                                (\ x -> Sum_Type.Inl (snd x)))
                              (\ x ->
                                Sum_Type.Inl
                                  ((Term_Rewriting.showsl_lit
                                      "the safe CS-DP " .
                                     Term_Rewriting.showsl_rule x) .
                                    Term_Rewriting.showsl_lit
                                      " does not appear in the DP problem\n")))))
               (\ x ->
                 Sum_Type.Inl
                   (Term_Rewriting.showsl_lit
                      "the safe CS-DP transformation is not applied correctly.\n" .
                     x))
         of {
         Sum_Type.Inl a -> Sum_Type.Inl a;
         Sum_Type.Inr _ ->
           Sum_Type.Inr
             (Dependency_Pair_Problem_Spec.mk j False True p [] [] [] r);
       });

check_csr_termination_proof ::
  forall a b c.
    (Compare.Compare_order b, Countable.Countable b, Eq b,
      Term_Rewriting.Showl b) => Termination_Problem_Spec.Tp_ops_ext a
                                   (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                   () ->
                                   Dependency_Pair_Problem_Spec.Dpp_ops_ext c
                                     (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                     () ->
                                     Bool ->
                                       (String -> String) ->
 [((Labelings.Lab b [Arith.Nat], Arith.Nat), [Arith.Nat])] ->
   [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
      Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
     Csr_termination_proof b [Arith.Nat] [Arith.Char] ->
       Sum_Type.Sum (String -> String) ();
check_csr_termination_proof ia j a i mu r CSR_R_is_Empty =
  FOR_Preliminaries.debug i "CSR R is empty"
    (if null r then Sum_Type.Inr ()
      else Sum_Type.Inl (i . Term_Rewriting.showsl_lit ": CSR R is not empty"));
check_csr_termination_proof ia j a i mu r (CSR_Rule_Removal redp rr prf) =
  FOR_Preliminaries.debug i "CSR rule removal"
    (case csr_rule_removal_impl redp mu rr r of {
      Sum_Type.Inl aa -> Sum_Type.Inl aa;
      Sum_Type.Inr r2 -> check_csr_termination_proof ia j a i mu r2 prf;
    });
check_csr_termination_proof ia j a i mu r (CSR_Dependency_Pairs p prf) =
  FOR_Preliminaries.debug i "CSR dependency pairs"
    (Error_Monad.bind
      (Error_Monad.catch_error (csr_sharp_mu_check mu)
        (\ x ->
          Sum_Type.Inl
            ((i . Term_Rewriting.showsl_lit
                    ": invalid replacement map for CSR dependency pairs\n") .
              x)))
      (\ _ ->
        (case mu_csr_dependency_pairs_tt Labelings.Sharp j mu r p of {
          Sum_Type.Inl _ ->
            Error_Monad.bind
              (Error_Monad.catch_error
                (safe_csr_dependency_pairs_tt Labelings.Sharp j mu r p)
                (\ x ->
                  Sum_Type.Inl
                    ((((((i . Term_Rewriting.showsl_lit
                                ": error when switching from CSR to a safe CS-DP problem\n") .
                          Term_Rewriting.showsl_rules r) .
                         Term_Rewriting.showsl_lit "\nwith pairs\n") .
                        Term_Rewriting.showsl_rules p) .
                       Term_Rewriting.showsl_literal "\n") .
                      x)))
              (\ dpp ->
                Error_Monad.catch_error
                  (check_csr_dp_termination_proof ia j False
                    (Term_Rewriting.add_index i Arith.one_nat) dpp prf)
                  (\ x ->
                    Sum_Type.Inl
                      ((i . Term_Rewriting.showsl_lit
                              ": error below safe CSR dependency pairs\n") .
                        x)));
          Sum_Type.Inr dpp ->
            Error_Monad.catch_error
              (check_csr_dp_termination_proof_core ia j mu False
                (Term_Rewriting.add_index i Arith.one_nat) dpp prf)
              (\ x ->
                Sum_Type.Inl
                  ((i . Term_Rewriting.showsl_lit
                          ": error below replacement-map-specific CSR dependency pairs\n") .
                    x));
        })));

}
