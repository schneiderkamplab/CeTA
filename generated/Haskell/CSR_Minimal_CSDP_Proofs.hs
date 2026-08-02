{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  CSR_Minimal_CSDP_Proofs(csr_u3_mixed_term_check, csr_instantiation_proc,
                           csr_qcs_usable_rules_proc,
                           check_csr_dp_termination_proof_min,
                           check_csr_termination_proof_min)
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
import qualified Name;
import qualified Sharp_Syntax;
import qualified Size_Change_Termination_Processors;
import qualified Missing_List;
import qualified Size_Change_Termination;
import qualified Product_Lexorder;
import qualified Compare_Order_Instances;
import qualified CSR_Checker;
import qualified FOR_Preliminaries;
import qualified Complex_Constant_Removal_Impl;
import qualified Reduction_Pair_Implementations;
import qualified Check_Termination_Common;
import qualified Termination_Problem_Spec;
import qualified Bounded_Increase_Impl;
import qualified Semantic_Labeling_Carrier;
import qualified Check_Termination;
import qualified Critical_Pairs_Impl;
import qualified Subterm_Criterion_Impl;
import qualified Countable;
import qualified Context_Sensitive_Impl;
import qualified Mapping;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified HOL;
import qualified Dependency_Pair_Problem_Spec;
import qualified Sum_Type;
import qualified CSR_Checker_Base;
import qualified Arith;
import qualified Compare;
import qualified Labelings;
import qualified Term_Rewriting;

csr_sct_sharp_term ::
  forall a b c. Term_Rewriting.Term (Labelings.Lab a b) c -> Bool;
csr_sct_sharp_term (Term_Rewriting.Fun (Labelings.Sharp f) ts) = True;
csr_sct_sharp_term (Term_Rewriting.Var v) = False;
csr_sct_sharp_term (Term_Rewriting.Fun (Labelings.Lab vb vc) va) = False;
csr_sct_sharp_term (Term_Rewriting.Fun (Labelings.FunLab vb vc) va) = False;
csr_sct_sharp_term (Term_Rewriting.Fun (Labelings.UnLab vb) va) = False;

csr_rta08_collapsing_CSDP_list ::
  forall a b.
    (Eq a,
      Eq b) => (a -> a) ->
                 [((a, Arith.Nat), [Arith.Nat])] ->
                   [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                     [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
csr_rta08_collapsing_CSDP_list shp mu r =
  concatMap
    (\ (l, ra) ->
      Arith.map_filter
        (\ x ->
          (if not (Arith.membera (CSR_Checker_Base.mu_vars_term_list mu l) x)
            then Just (Sharp_Syntax.sharp_term shp l, Term_Rewriting.Var x)
            else Nothing))
        (Arith.remdups (CSR_Checker_Base.mu_vars_term_list mu ra)))
    r;

csr_rta08_CSDP_list ::
  forall a b.
    (Compare.Compare_order a, Eq a, Term_Rewriting.Showl a,
      Eq b) => (a -> a) ->
                 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                   [((a, Arith.Nat), [Arith.Nat])] ->
                     [(a, Arith.Nat)] ->
                       [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
csr_rta08_CSDP_list shp r mu d =
  CSR_Checker_Base.mu_CSDP_list shp r mu d ++
    csr_rta08_collapsing_CSDP_list shp mu r;

csr_sct_index_check ::
  forall a b c. Term_Rewriting.Term (Labelings.Lab a b) c -> Arith.Nat -> Bool;
csr_sct_index_check (Term_Rewriting.Fun (Labelings.Sharp f) ts) i =
  Arith.less_nat Arith.zero_nat i && Arith.less_eq_nat i (Arith.size_list ts);
csr_sct_index_check (Term_Rewriting.Var v) i = False;
csr_sct_index_check (Term_Rewriting.Fun (Labelings.Lab vb vc) va) i = False;
csr_sct_index_check (Term_Rewriting.Fun (Labelings.FunLab vb vc) va) i = False;
csr_sct_index_check (Term_Rewriting.Fun (Labelings.UnLab vb) va) i = False;

csr_u3_root_rules_check ::
  forall a b c d.
    (Eq a, Eq b,
      Eq c) => [(Term_Rewriting.Term a b, c)] ->
                 [(Term_Rewriting.Term a b, c)] ->
                   Term_Rewriting.Term a d -> [[Arith.Nat]] -> Bool;
csr_u3_root_rules_check r u t ps =
  all (\ p ->
        (case Term_Rewriting.root (Term_Rewriting.subt_at t p) of {
          Nothing -> True;
          Just f ->
            all (\ lr ->
                  not (Term_Rewriting.root (fst lr) == Just f) ||
                    Arith.membera u lr)
              r;
        }))
    ps;

csr_u3_inactive_root_rules_check ::
  forall a b c d.
    (Eq a, Eq b,
      Eq c) => [(Term_Rewriting.Term a b, c)] ->
                 [(Term_Rewriting.Term a b, c)] ->
                   [((a, Arith.Nat), [Arith.Nat])] ->
                     Term_Rewriting.Term a d -> Bool;
csr_u3_inactive_root_rules_check r u mu t =
  csr_u3_root_rules_check r u t
    (filter
      (\ p -> not (Arith.membera (CSR_Checker_Base.mu_fun_poss_list mu t) p))
      (Term_Rewriting.fun_poss_list t));

csr_u3_all_root_rules_check ::
  forall a b c d.
    (Eq a, Eq b,
      Eq c) => [(Term_Rewriting.Term a b, c)] ->
                 [(Term_Rewriting.Term a b, c)] ->
                   Term_Rewriting.Term a d -> Bool;
csr_u3_all_root_rules_check r u t =
  csr_u3_root_rules_check r u t (Term_Rewriting.fun_poss_list t);

csr_u3_usable_rules_check ::
  forall a b c d e.
    (Eq a, Eq b,
      Eq c) => [(Term_Rewriting.Term a b, Term_Rewriting.Term a c)] ->
                 [(Term_Rewriting.Term a b, Term_Rewriting.Term a c)] ->
                   [((a, Arith.Nat), [Arith.Nat])] ->
                     [(Term_Rewriting.Term a d, Term_Rewriting.Term a e)] ->
                       Bool;
csr_u3_usable_rules_check r u mu p =
  all (Arith.membera r) u &&
    all (\ dp ->
          csr_u3_inactive_root_rules_check r u mu (fst dp) &&
            csr_u3_all_root_rules_check r u (snd dp))
      p &&
      all (\ lr -> csr_u3_inactive_root_rules_check r u mu (snd lr)) r &&
        all (\ lr ->
              csr_u3_inactive_root_rules_check r u mu (fst lr) &&
                csr_u3_all_root_rules_check r u (snd lr))
          u;

csr_u3_mixed_term_check ::
  forall a b c.
    (Eq a,
      Eq b) => Labelings.Lab a b ->
                 Term_Rewriting.Term (Labelings.Lab a b) c -> Bool;
csr_u3_mixed_term_check h (Term_Rewriting.Var x) = False;
csr_u3_mixed_term_check h (Term_Rewriting.Fun f ts) =
  CSR_Checker_Base.is_sharp_lab f || Labelings.equal_lab f h;

csr_u3_mixed_pairs_check ::
  forall a b c d.
    (Eq a,
      Eq b) => [(Term_Rewriting.Term (Labelings.Lab a b) c,
                  Term_Rewriting.Term (Labelings.Lab a b) c)] ->
                 [(Term_Rewriting.Term (Labelings.Lab a b) d,
                    Term_Rewriting.Term (Labelings.Lab a b) d)] ->
                   Bool;
csr_u3_mixed_pairs_check r p =
  any (\ h ->
        not (CSR_Checker_Base.is_sharp_lab h) &&
          all (\ (f, _) -> not (Labelings.equal_lab f h))
            (Term_Rewriting.funas_trs_list r) &&
            all (\ (l, ra) ->
                  csr_u3_mixed_term_check h l && csr_u3_mixed_term_check h ra)
              p)
    (map fst (Term_Rewriting.funas_trs_list p));

csr_sharp_pairs_check ::
  forall a b c d e f.
    [(Term_Rewriting.Term (Labelings.Lab a b) c,
       Term_Rewriting.Term (Labelings.Lab d e) f)] ->
      Bool;
csr_sharp_pairs_check p =
  all (\ (l, r) ->
        (case Term_Rewriting.root l of {
          Nothing -> False;
          Just (Labelings.Lab _ _, _) -> False;
          Just (Labelings.FunLab _ _, _) -> False;
          Just (Labelings.UnLab _, _) -> False;
          Just (Labelings.Sharp _, _) -> True;
        }) &&
          (case Term_Rewriting.root r of {
            Nothing -> False;
            Just (Labelings.Lab _ _, _) -> False;
            Just (Labelings.FunLab _ _, _) -> False;
            Just (Labelings.UnLab _, _) -> False;
            Just (Labelings.Sharp _, _) -> True;
          }))
    p;

csr_u3_redpair_proc ::
  forall a b c d.
    (Compare.Compare_order b, Eq b, Term_Rewriting.Showl b, Eq c,
      Term_Rewriting.Showl c, Eq d,
      Term_Rewriting.Showl d) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a
                                   (Labelings.Lab b c) d () ->
                                   [((Labelings.Lab b c, Arith.Nat),
                                      [Arith.Nat])] ->
                                     Term_Rewriting.Rel_impl_ext
                                       (Labelings.Lab b c) d () ->
                                       [(Term_Rewriting.Term (Labelings.Lab b c)
   d,
  Term_Rewriting.Term (Labelings.Lab b c) d)] ->
 [(Term_Rewriting.Term (Labelings.Lab b c) d,
    Term_Rewriting.Term (Labelings.Lab b c) d)] ->
   a -> Sum_Type.Sum (String -> String) a;
csr_u3_redpair_proc j mu rp premove u dpp =
  (case Error_Monad.bind (Term_Rewriting.rel_impl_redpair rp)
          (\ _ ->
            Error_Monad.bind (CSR_Checker_Base.csr_sharp_mu_check mu)
              (\ _ ->
                (case Dependency_Pair_Problem_Spec.split_pairs j dpp premove of
                  {
                  (ps, pns) ->
                    Error_Monad.bind
                      (Check_Monad.check
                        (csr_sharp_pairs_check
                           (Dependency_Pair_Problem_Spec.pairs j dpp) ||
                          csr_u3_mixed_pairs_check
                            (Dependency_Pair_Problem_Spec.rules j dpp)
                            (Dependency_Pair_Problem_Spec.pairs j dpp))
                        (Term_Rewriting.showsl_lit
                          "U3 reduction pair requires marked or fresh-unhiding CS-DPs"))
                      (\ _ ->
                        Error_Monad.bind
                          (Check_Monad.check
                            (csr_u3_usable_rules_check
                              (Dependency_Pair_Problem_Spec.rules j dpp) u mu
                              (Dependency_Pair_Problem_Spec.pairs j dpp))
                            (Term_Rewriting.showsl_lit
                              "supplied rules are not a closed U3 set"))
                          (\ _ ->
                            Error_Monad.bind
                              (Error_Monad.catch_error
                                (Term_Rewriting.ce_compat rp)
                                (\ x ->
                                  Sum_Type.Inl
                                    (Term_Rewriting.showsl_lit
                                       "U3 reduction pair requires C-epsilon compatibility\n" .
                                      x)))
                              (\ _ ->
                                Error_Monad.bind
                                  (Error_Monad.catch_error
                                    (Term_Rewriting.rel_impl_ns rp (u ++ pns))
                                    (\ x ->
                                      Sum_Type.Inl
(Term_Rewriting.showsl_lit
   "problem weakly orienting U3 rules or retained CS-DPs\n" .
  x)))
                                  (\ _ ->
                                    Error_Monad.catch_error
                                      (Term_Rewriting.rel_impl_s rp ps)
                                      (\ x ->
Sum_Type.Inl
  (Term_Rewriting.showsl_lit "problem strictly orienting removed CS-DPs\n" .
    x))))));
                })))
    of {
    Sum_Type.Inl a -> Sum_Type.Inl a;
    Sum_Type.Inr _ ->
      Sum_Type.Inr
        (Dependency_Pair_Problem_Spec.delete_P_Pw j dpp premove premove);
  });

csr_instantiation_cap ::
  forall a b c.
    (Compare.Compare a, Eq a, Term_Rewriting.Showl a, Compare.Compare b, Eq b,
      Term_Rewriting.Showl b,
      Eq c) => ((Labelings.Lab a b, Arith.Nat) -> Arith.Set Arith.Nat) ->
                 [(Term_Rewriting.Term (Labelings.Lab a b) c,
                    Term_Rewriting.Term (Labelings.Lab a b) c)] ->
                   Term_Rewriting.Term (Labelings.Lab a b) c ->
                     Term_Rewriting.Gctxt (Labelings.Lab a b) c;
csr_instantiation_cap mu r (Term_Rewriting.Var x) = Term_Rewriting.GCHole;
csr_instantiation_cap mu r (Term_Rewriting.Fun f ts) =
  CSR_Checker_Base.csr_root_tcap (CSR_Checker_Base.csr_dp_root_mu mu) r
    (Term_Rewriting.Fun f ts);

csr_instantiation_proc ::
  forall a b c.
    (Compare.Compare_order b, Eq b, Term_Rewriting.Showl b,
      Compare.Compare_order c, Eq c,
      Term_Rewriting.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a
                                   (Labelings.Lab b c) [Arith.Char] () ->
                                   [((Labelings.Lab b c, Arith.Nat),
                                      [Arith.Nat])] ->
                                     (Term_Rewriting.Term (Labelings.Lab b c)
[Arith.Char],
                                       Term_Rewriting.Term (Labelings.Lab b c)
 [Arith.Char]) ->
                                       [(Term_Rewriting.Term (Labelings.Lab b c)
   [Arith.Char],
  Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char])] ->
 a -> Sum_Type.Sum (String -> String) a;
csr_instantiation_proc j mu st sts dpp =
  (case Error_Monad.bind
          (Check_Monad.check
            (Arith.membera (Dependency_Pair_Problem_Spec.pairs j dpp) st)
            (Term_Rewriting.showsl_lit "selected CS-DP is not present"))
          (\ _ ->
            Error_Monad.bind
              (Error_Monad.catch_error
                (Error_Monad.forallM
                  (\ sta ->
                    Check_Monad.check (Term_Rewriting.instance_rule sta st)
                      (Term_Rewriting.showsl_lit
                         "supplied CS-DP is not an instance of the selected pair" .
                        Term_Rewriting.showsl_rule sta))
                  sts)
                (\ x -> Sum_Type.Inl (snd x)))
              (\ _ ->
                (case st of {
                  (s, t) ->
                    Error_Monad.catch_error
                      (Error_Monad.forallM
                        (\ (_, v) ->
                          Error_Monad.bind
                            (Check_Monad.check
                              (case Term_Rewriting.root v of {
                                Nothing -> True;
                                Just fn ->
                                  not (Arith.membera
(Term_Rewriting.defined_list (Dependency_Pair_Problem_Spec.rules j dpp)) fn);
                              })
                              (Term_Rewriting.showsl_lit
                                "predecessor right-hand side has a defined root"))
                            (\ _ ->
                              (case Term_Rewriting.gc_matcher
                                      (csr_instantiation_cap
(Context_Sensitive_Impl.mu_of mu) (Dependency_Pair_Problem_Spec.rules j dpp) v)
                                      s
                                of {
                                Nothing -> Sum_Type.Inr ();
                                Just sigma ->
                                  Check_Monad.check
                                    (any (Term_Rewriting.instance_rule
   (Term_Rewriting.eval_term Term_Rewriting.Fun s sigma,
     Term_Rewriting.eval_term Term_Rewriting.Fun t sigma))
                                      sts)
                                    (Term_Rewriting.showsl_lit
                                       "missing replacement-map-aware instance of pair " .
                                      Term_Rewriting.showsl_rule
(Term_Rewriting.eval_term Term_Rewriting.Fun s sigma,
  Term_Rewriting.eval_term Term_Rewriting.Fun t sigma));
                              })))
                        (Dependency_Pair_Problem_Spec.pairs j dpp))
                      (\ x -> Sum_Type.Inl (snd x));
                })))
    of {
    Sum_Type.Inl a -> Sum_Type.Inl a;
    Sum_Type.Inr _ ->
      Sum_Type.Inr (Dependency_Pair_Problem_Spec.replace_pair j dpp st sts);
  });

csr_rta08_projection_rules_list ::
  forall a.
    (Eq a) => [((a, Arith.Nat), [Arith.Nat])] ->
                [(a, Arith.Nat)] ->
                  [(Term_Rewriting.Term a [Arith.Char],
                     Term_Rewriting.Term a [Arith.Char])];
csr_rta08_projection_rules_list mu f =
  concatMap
    (\ (fa, n) ->
      let {
        xs = map Term_Rewriting.Var (Name.x_1_to_x_n n);
      } in Arith.map_filter
             (\ x ->
               (if Arith.member x (Context_Sensitive_Impl.mu_of mu (fa, n))
                 then Just (Term_Rewriting.Fun fa xs, Arith.nth xs x)
                 else Nothing))
             (Arith.upt Arith.zero_nat n))
    f;

csr_rta08_marking_rules_list ::
  forall a.
    (a -> a) ->
      [(a, Arith.Nat)] ->
        [(Term_Rewriting.Term a [Arith.Char],
           Term_Rewriting.Term a [Arith.Char])];
csr_rta08_marking_rules_list shp d =
  map (\ (f, n) ->
        let {
          xs = map Term_Rewriting.Var (Name.x_1_to_x_n n);
        } in (Term_Rewriting.Fun f xs,
               Sharp_Syntax.sharp_term shp (Term_Rewriting.Fun f xs)))
    d;

csr_rta08_redpair_proc ::
  forall a b c.
    (Eq b, Term_Rewriting.Showl b, Eq c,
      Term_Rewriting.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a
                                   (Labelings.Lab b c) [Arith.Char] () ->
                                   [((Labelings.Lab b c, Arith.Nat),
                                      [Arith.Nat])] ->
                                     Term_Rewriting.Rel_impl_ext
                                       (Labelings.Lab b c) [Arith.Char] () ->
                                       [(Term_Rewriting.Term (Labelings.Lab b c)
   [Arith.Char],
  Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char])] ->
 a -> Sum_Type.Sum (String -> String) a;
csr_rta08_redpair_proc j mu rp premove dpp =
  (case (case Term_Rewriting.not_wst rp of {
          Nothing ->
            Sum_Type.Inl
              (Term_Rewriting.showsl_lit
                "RTA08 reduction pair does not expose weak-subterm exceptions");
          Just f ->
            Error_Monad.bind (Term_Rewriting.rel_impl_redpair rp)
              (\ _ ->
                let {
                  d = Term_Rewriting.defined_list
                        (Dependency_Pair_Problem_Spec.rules j dpp);
                } in (case Dependency_Pair_Problem_Spec.split_pairs j dpp
                             premove
                       of {
                       (ps, pns) ->
                         Error_Monad.bind
                           (Error_Monad.catch_error
                             (Error_Monad.forallM
                               (\ (l, r) ->
                                 Check_Monad.check
                                   (not (Term_Rewriting.is_Var r) ||
                                     Arith.membera premove (l, r))
                                   (Term_Rewriting.showsl_lit
                                     "RTA08 case 2(b) must remove every collapsing pair"))
                               (Dependency_Pair_Problem_Spec.pairs j dpp))
                             (\ x -> Sum_Type.Inl (snd x)))
                           (\ _ ->
                             Error_Monad.bind
                               (Error_Monad.catch_error
                                 (Term_Rewriting.rel_impl_ns rp
                                   (Dependency_Pair_Problem_Spec.rules j dpp ++
                                     csr_rta08_projection_rules_list mu f ++
                                       filter (Term_Rewriting.is_Var . snd)
 ps ++
 pns))
                                 (\ x ->
                                   Sum_Type.Inl
                                     (Term_Rewriting.showsl_lit
"problem weakly orienting RTA08 rules, projections, or pairs\n" .
                                       x)))
                               (\ _ ->
                                 Error_Monad.catch_error
                                   (Term_Rewriting.rel_impl_s rp
                                     (filter
((\ t -> not (Term_Rewriting.is_Var t)) . snd) ps ++
                                       csr_rta08_marking_rules_list
 Labelings.Sharp d))
                                   (\ x ->
                                     Sum_Type.Inl
                                       (Term_Rewriting.showsl_lit
  "problem strictly orienting RTA08 pairs or marking rules\n" .
 x))));
                     }));
        })
    of {
    Sum_Type.Inl a -> Sum_Type.Inl a;
    Sum_Type.Inr _ ->
      Sum_Type.Inr
        (Dependency_Pair_Problem_Spec.delete_P_Pw j dpp premove premove);
  });

qcs_ur_closed_term_check ::
  forall a b c d.
    (Eq a, Eq b,
      Eq c) => [(Term_Rewriting.Term a b, c)] ->
                 [(Term_Rewriting.Term a b, c)] ->
                   [((a, Arith.Nat), [Arith.Nat])] ->
                     Term_Rewriting.Term a d -> Bool;
qcs_ur_closed_term_check r u mu (Term_Rewriting.Var x) =
  all (Arith.membera u) r;
qcs_ur_closed_term_check r u mu (Term_Rewriting.Fun f ts) =
  all (\ lr ->
        not (Term_Rewriting.root (fst lr) == Just (f, Arith.size_list ts)) ||
          Arith.membera u lr)
    r &&
    all (\ (i, t) ->
          not (Arith.member i
                (Context_Sensitive_Impl.mu_of mu (f, Arith.size_list ts))) ||
            qcs_ur_closed_term_check r u mu t)
      (zip (Arith.upt Arith.zero_nat (Arith.size_list ts)) ts);

qcs_ur_closed_dp_rhs_check ::
  forall a b c d e.
    (Eq a, Eq b, Eq c,
      Eq d) => [(Term_Rewriting.Term (Labelings.Lab a b) c, d)] ->
                 [(Term_Rewriting.Term (Labelings.Lab a b) c, d)] ->
                   [((Labelings.Lab a b, Arith.Nat), [Arith.Nat])] ->
                     Term_Rewriting.Term (Labelings.Lab a b) e -> Bool;
qcs_ur_closed_dp_rhs_check r u mu (Term_Rewriting.Var x) = False;
qcs_ur_closed_dp_rhs_check r u mu (Term_Rewriting.Fun (Labelings.Sharp f) ts) =
  all (\ (i, t) ->
        not (Arith.member i
              (Context_Sensitive_Impl.mu_of mu (f, Arith.size_list ts))) ||
          qcs_ur_closed_term_check r u mu t)
    (zip (Arith.upt Arith.zero_nat (Arith.size_list ts)) ts);
qcs_ur_closed_dp_rhs_check r u mu (Term_Rewriting.Fun (Labelings.Lab v va) ts) =
  False;
qcs_ur_closed_dp_rhs_check r u mu
  (Term_Rewriting.Fun (Labelings.FunLab v va) ts) = False;
qcs_ur_closed_dp_rhs_check r u mu (Term_Rewriting.Fun (Labelings.UnLab v) ts) =
  False;

qcs_csr_ur_closed_check ::
  forall a b c d e f.
    (Eq a, Eq b, Eq c,
      Eq d) => [(Term_Rewriting.Term (Labelings.Lab a b) c,
                  Term_Rewriting.Term (Labelings.Lab a b) d)] ->
                 [(Term_Rewriting.Term (Labelings.Lab a b) c,
                    Term_Rewriting.Term (Labelings.Lab a b) d)] ->
                   [((Labelings.Lab a b, Arith.Nat), [Arith.Nat])] ->
                     [(e, Term_Rewriting.Term (Labelings.Lab a b) f)] -> Bool;
qcs_csr_ur_closed_check r u mu p =
  all (Arith.membera r) u &&
    all (\ lr -> qcs_ur_closed_term_check r u mu (snd lr)) u &&
      all (\ dp -> qcs_ur_closed_dp_rhs_check r u mu (snd dp)) p;

check_csr_rta08_dp_first ::
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
                                       (String -> String) ->
 c -> CSR_Checker_Base.Csr_dp_termination_proof b [Arith.Nat] [Arith.Char] ->
        Sum_Type.Sum (String -> String) ();
check_csr_rta08_dp_first ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_UR_Proc redp pr u subprf))
  = FOR_Preliminaries.debug i "RTA08 collapsing reduction pair"
      (Error_Monad.bind
        (Error_Monad.catch_error
          (csr_rta08_redpair_proc j mu
            (Reduction_Pair_Implementations.get_rel_impl redp) pr dpp)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error when applying RTA08 collapsing reduction pair\n") .
                x)))
        (\ dppa ->
          Error_Monad.catch_error
            (CSR_Checker.check_csr_dp_termination_proof_core ia j mu False
              (Term_Rewriting.add_index i Arith.one_nat) dppa
              (CSR_Checker_Base.CSR_DP_Ordinary_Proof subprf))
            (\ x ->
              Sum_Type.Inl
                ((i . Term_Rewriting.showsl_lit
                        ": error below RTA08 collapsing reduction pair\n") .
                  x))));
check_csr_rta08_dp_first ia j mu i dpp CSR_Checker_Base.CSR_DP_P_is_Empty =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": RTA08 collapsing CS-DPs require an initial reduction-pair processor");
check_csr_rta08_dp_first ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof Check_Termination.P_is_Empty) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": RTA08 collapsing CS-DPs require an initial reduction-pair processor");
check_csr_rta08_dp_first ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Subterm_Criterion_Proc va vb vc vd))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": RTA08 collapsing CS-DPs require an initial reduction-pair processor");
check_csr_rta08_dp_first ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Gen_Subterm_Criterion_Proc va vb vc))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": RTA08 collapsing CS-DPs require an initial reduction-pair processor");
check_csr_rta08_dp_first ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_Proc va vb vc))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": RTA08 collapsing CS-DPs require an initial reduction-pair processor");
check_csr_rta08_dp_first ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Usable_Rules_Proc va vb))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": RTA08 collapsing CS-DPs require an initial reduction-pair processor");
check_csr_rta08_dp_first ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof (Check_Termination.Dep_Graph_Proc va))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": RTA08 collapsing CS-DPs require an initial reduction-pair processor");
check_csr_rta08_dp_first ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Mono_Redpair_Proc va vb vc vd))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": RTA08 collapsing CS-DPs require an initial reduction-pair processor");
check_csr_rta08_dp_first ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Mono_URM_Redpair_Proc va vb vc vd))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": RTA08 collapsing CS-DPs require an initial reduction-pair processor");
check_csr_rta08_dp_first ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Mono_Redpair_UR_Proc va vb vc vd ve))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": RTA08 collapsing CS-DPs require an initial reduction-pair processor");
check_csr_rta08_dp_first ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Size_Change_Subterm_Proc va))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": RTA08 collapsing CS-DPs require an initial reduction-pair processor");
check_csr_rta08_dp_first ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Size_Change_Redpair_Proc va vb vc))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": RTA08 collapsing CS-DPs require an initial reduction-pair processor");
check_csr_rta08_dp_first ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Uncurry_Proc va vb vc vd ve))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": RTA08 collapsing CS-DPs require an initial reduction-pair processor");
check_csr_rta08_dp_first ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Fcc_Proc va vb vc vd ve))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": RTA08 collapsing CS-DPs require an initial reduction-pair processor");
check_csr_rta08_dp_first ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Split_Proc va vb vc vd))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": RTA08 collapsing CS-DPs require an initial reduction-pair processor");
check_csr_rta08_dp_first ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Semlab_Proc va vb vc vd ve))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": RTA08 collapsing CS-DPs require an initial reduction-pair processor");
check_csr_rta08_dp_first ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Switch_Innermost_Proc va vb))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": RTA08 collapsing CS-DPs require an initial reduction-pair processor");
check_csr_rta08_dp_first ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Rewriting_Proc va vb vc vd ve vf vg))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": RTA08 collapsing CS-DPs require an initial reduction-pair processor");
check_csr_rta08_dp_first ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Instantiation_Proc va vb vc))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": RTA08 collapsing CS-DPs require an initial reduction-pair processor");
check_csr_rta08_dp_first ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Forward_Instantiation_Proc va vb vc vd))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": RTA08 collapsing CS-DPs require an initial reduction-pair processor");
check_csr_rta08_dp_first ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Narrowing_Proc va vb vc vd))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": RTA08 collapsing CS-DPs require an initial reduction-pair processor");
check_csr_rta08_dp_first ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Assume_Finite va vb))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": RTA08 collapsing CS-DPs require an initial reduction-pair processor");
check_csr_rta08_dp_first ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Q_Reduction_Proc va vb))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": RTA08 collapsing CS-DPs require an initial reduction-pair processor");
check_csr_rta08_dp_first ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Complex_Constant_Removal_Proc va vb))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": RTA08 collapsing CS-DPs require an initial reduction-pair processor");
check_csr_rta08_dp_first ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.General_Redpair_Proc va vb vc vd ve))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": RTA08 collapsing CS-DPs require an initial reduction-pair processor");
check_csr_rta08_dp_first ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof (Check_Termination.To_Trs_Proc va)) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": RTA08 collapsing CS-DPs require an initial reduction-pair processor");
check_csr_rta08_dp_first ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Subterm_Criterion_Proc v va vb vc) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": RTA08 collapsing CS-DPs require an initial reduction-pair processor");
check_csr_rta08_dp_first ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Gen_Subterm_Criterion_Proc v va vb) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": RTA08 collapsing CS-DPs require an initial reduction-pair processor");
check_csr_rta08_dp_first ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Usable_Rules_Proc v va) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": RTA08 collapsing CS-DPs require an initial reduction-pair processor");
check_csr_rta08_dp_first ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Dep_Graph_Proc v) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": RTA08 collapsing CS-DPs require an initial reduction-pair processor");
check_csr_rta08_dp_first ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Instantiation_Proc v va vb) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": RTA08 collapsing CS-DPs require an initial reduction-pair processor");
check_csr_rta08_dp_first ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Size_Change_Subterm_Proc v) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": RTA08 collapsing CS-DPs require an initial reduction-pair processor");

check_csr_dp_ordinary_min ::
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
   c -> Check_Termination.Dp_termination_proof b [Arith.Nat] [Arith.Char] ->
          Sum_Type.Sum (String -> String) ();
check_csr_dp_ordinary_min ia j mu a i dpp prf =
  (case prf of {
    Check_Termination.P_is_Empty ->
      CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof prf);
    Check_Termination.Subterm_Criterion_Proc _ _ _ _ ->
      CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof prf);
    Check_Termination.Gen_Subterm_Criterion_Proc _ _ _ ->
      CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof prf);
    Check_Termination.Redpair_Proc _ _ _ ->
      CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof prf);
    Check_Termination.Redpair_UR_Proc redp pr u subprf ->
      FOR_Preliminaries.debug i "CSR U3 reduction pair"
        (Error_Monad.bind
          (Error_Monad.catch_error
            (csr_u3_redpair_proc j mu
              (Reduction_Pair_Implementations.get_rel_impl redp) pr u dpp)
            (\ x ->
              Sum_Type.Inl
                ((i . Term_Rewriting.showsl_lit
                        ": error when applying CSR U3 reduction pair\n") .
                  x)))
          (\ dppa ->
            Error_Monad.catch_error
              (CSR_Checker.check_csr_dp_termination_proof_core ia j mu a
                (Term_Rewriting.add_index i Arith.one_nat) dppa
                (CSR_Checker_Base.CSR_DP_Ordinary_Proof subprf))
              (\ x ->
                Sum_Type.Inl
                  ((i . Term_Rewriting.showsl_lit
                          ": error below CSR U3 reduction pair\n") .
                    x))));
    Check_Termination.Usable_Rules_Proc _ _ ->
      CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof prf);
    Check_Termination.Dep_Graph_Proc _ ->
      CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof prf);
    Check_Termination.Mono_Redpair_Proc _ _ _ _ ->
      CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof prf);
    Check_Termination.Mono_URM_Redpair_Proc _ _ _ _ ->
      CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof prf);
    Check_Termination.Mono_Redpair_UR_Proc _ _ _ _ _ ->
      CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof prf);
    Check_Termination.Size_Change_Subterm_Proc _ ->
      CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof prf);
    Check_Termination.Size_Change_Redpair_Proc _ _ _ ->
      CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof prf);
    Check_Termination.Uncurry_Proc _ _ _ _ _ ->
      CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof prf);
    Check_Termination.Fcc_Proc _ _ _ _ _ ->
      CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof prf);
    Check_Termination.Split_Proc _ _ _ _ ->
      CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof prf);
    Check_Termination.Semlab_Proc _ _ _ _ _ ->
      CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof prf);
    Check_Termination.Switch_Innermost_Proc _ _ ->
      CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof prf);
    Check_Termination.Rewriting_Proc _ _ _ _ _ _ _ ->
      CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof prf);
    Check_Termination.Instantiation_Proc _ _ _ ->
      CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof prf);
    Check_Termination.Forward_Instantiation_Proc _ _ _ _ ->
      CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof prf);
    Check_Termination.Narrowing_Proc _ _ _ _ ->
      CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof prf);
    Check_Termination.Assume_Finite _ _ ->
      CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof prf);
    Check_Termination.Q_Reduction_Proc _ _ ->
      CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof prf);
    Check_Termination.Complex_Constant_Removal_Proc _ _ ->
      CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof prf);
    Check_Termination.General_Redpair_Proc _ _ _ _ _ ->
      CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof prf);
    Check_Termination.To_Trs_Proc _ ->
      CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof prf);
  });

csr_qcs_usable_rules_proc ::
  forall a b c d.
    (Compare.Compare_order b, Eq b, Term_Rewriting.Showl b,
      Compare.Compare_order c, Eq c, Term_Rewriting.Showl c,
      Compare.Compare_order d, Eq d,
      Term_Rewriting.Showl d) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a
                                   (Labelings.Lab b c) d () ->
                                   [((Labelings.Lab b c, Arith.Nat),
                                      [Arith.Nat])] ->
                                     [(Term_Rewriting.Term (Labelings.Lab b c)
 d,
Term_Rewriting.Term (Labelings.Lab b c) d)] ->
                                       a -> Sum_Type.Sum (String -> String) a;
csr_qcs_usable_rules_proc j mu u dpp =
  (case Check_Monad.check
          (qcs_csr_ur_closed_check (Dependency_Pair_Problem_Spec.rules j dpp) u
            mu (Dependency_Pair_Problem_Spec.pairs j dpp))
          (Term_Rewriting.showsl_lit
            "error when checking QCS usable-rule closure")
    of {
    Sum_Type.Inl a -> Sum_Type.Inl a;
    Sum_Type.Inr _ ->
      Sum_Type.Inr (Dependency_Pair_Problem_Spec.intersect_rules j dpp u);
  });

csr_sct_active_index_check ::
  forall a b c.
    (Eq a,
      Eq b) => [((Labelings.Lab a b, Arith.Nat), [Arith.Nat])] ->
                 Term_Rewriting.Term (Labelings.Lab a b) c -> Arith.Nat -> Bool;
csr_sct_active_index_check mu (Term_Rewriting.Fun (Labelings.Sharp f) ts) i =
  Arith.less_nat Arith.zero_nat i &&
    Arith.less_eq_nat i (Arith.size_list ts) &&
      Arith.member (Arith.minus_nat i Arith.one_nat)
        (Context_Sensitive_Impl.mu_of mu (f, Arith.size_list ts));
csr_sct_active_index_check mu (Term_Rewriting.Var v) i = False;
csr_sct_active_index_check mu (Term_Rewriting.Fun (Labelings.Lab vb vc) va) i =
  False;
csr_sct_active_index_check mu (Term_Rewriting.Fun (Labelings.FunLab vb vc) va) i
  = False;
csr_sct_active_index_check mu (Term_Rewriting.Fun (Labelings.UnLab vb) va) i =
  False;

csr_rules_sharp_fresh_check ::
  forall a b c.
    [(Term_Rewriting.Term (Labelings.Lab a b) c,
       Term_Rewriting.Term (Labelings.Lab a b) c)] ->
      Sum_Type.Sum (String -> String) ();
csr_rules_sharp_fresh_check r =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ (f, _) ->
        Check_Monad.check (not (CSR_Checker_Base.is_sharp_lab f))
          (Term_Rewriting.showsl_lit "source CSR defines a sharp symbol"))
      (Term_Rewriting.defined_list r))
    (\ x -> Sum_Type.Inl (snd x));

csr_sct_active_subterm_proc ::
  forall a b c.
    (Compare.Compare_order b, Eq b, Term_Rewriting.Showl b,
      Compare.Compare_order c, Eq c,
      Term_Rewriting.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a
                                   (Labelings.Lab b c) [Arith.Char] () ->
                                   [((Labelings.Lab b c, Arith.Nat),
                                      [Arith.Nat])] ->
                                     [((Term_Rewriting.Term (Labelings.Lab b c)
  [Arith.Char],
 Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char]),
([(Arith.Nat, Arith.Nat)], [(Arith.Nat, Arith.Nat)]))] ->
                                       a -> Sum_Type.Sum (String -> String) ();
csr_sct_active_subterm_proc j mu gs dpp =
  let {
    p = Dependency_Pair_Problem_Spec.pairs j dpp;
    r = Dependency_Pair_Problem_Spec.rules j dpp;
  } in Error_Monad.bind
         (Error_Monad.catch_error (Check_Monad.check_subseteq p (map fst gs))
           (\ x ->
             Sum_Type.Inl
               (Term_Rewriting.showsl_lit
                  "there is no CSR size-change graph for pair " .
                 Term_Rewriting.showsl_rule x)))
         (\ _ ->
           let {
             gGs = filter (\ g -> Arith.membera p (fst g)) gs;
           } in Error_Monad.bind
                  (Error_Monad.catch_error
                    (Error_Monad.forallM
                      (\ (a, b) ->
                        (case a of {
                          (s, t) ->
                            (\ (stri, nstri) ->
                              Error_Monad.bind
                                (Check_Monad.check
                                  (csr_sct_sharp_term s && csr_sct_sharp_term t)
                                  (Term_Rewriting.showsl_lit
                                    "CSR size-change pair is not sharp-rooted"))
                                (\ _ ->
                                  Error_Monad.bind
                                    (Error_Monad.catch_error
                                      (Error_Monad.forallM
(\ (i, ja) ->
  Check_Monad.check
    (csr_sct_active_index_check mu s i &&
      csr_sct_index_check t ja &&
        Arith.membera
          (CSR_Checker_Base.mu_supt_list mu
            (Size_Change_Termination_Processors.get_arg s i))
          (Size_Change_Termination_Processors.get_arg t ja))
    (Term_Rewriting.showsl_lit "invalid strict CSR size-change edge"))
stri)
                                      (\ x -> Sum_Type.Inl (snd x)))
                                    (\ _ ->
                                      Error_Monad.catch_error
(Error_Monad.forallM
  (\ (i, ja) ->
    Check_Monad.check
      (csr_sct_index_check s i &&
        csr_sct_index_check t ja &&
          (Term_Rewriting.equal_term
             (Size_Change_Termination_Processors.get_arg s i)
             (Size_Change_Termination_Processors.get_arg t ja) ||
            csr_sct_active_index_check mu s i &&
              Arith.membera
                (CSR_Checker_Base.mu_supt_list mu
                  (Size_Change_Termination_Processors.get_arg s i))
                (Size_Change_Termination_Processors.get_arg t ja)))
      (Term_Rewriting.showsl_lit "invalid non-strict CSR size-change edge"))
  nstri)
(\ x -> Sum_Type.Inl (snd x)))));
                        })
                          b)
                      gGs)
                    (\ x -> Sum_Type.Inl (snd x)))
                  (\ _ ->
                    let {
                      conn =
                        (\ st uv ->
                          CSR_Checker_Base.csr_dep_graph_edge_check
                            (CSR_Checker_Base.csr_dp_root_mu
                              (Context_Sensitive_Impl.mu_of mu))
                            r ((st, ()), (uv, ())));
                    } in Check_Monad.check
                           (Size_Change_Termination.check_SCT conn
                             (map (\ (st, (stri, nstri)) ->
                                    Size_Change_Termination.Scg st st
                                      (Missing_List.remdups_sort stri)
                                      (Missing_List.remdups_sort nstri))
                               gGs))
                           (Term_Rewriting.showsl_lit
                             "CSR size-change analysis failed")));

csr_rta08_dependency_pairs_tt ::
  forall a b.
    (Compare.Compare_order b, Eq b,
      Term_Rewriting.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a
                                   (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                   () ->
                                   [((Labelings.Lab b [Arith.Nat], Arith.Nat),
                                      [Arith.Nat])] ->
                                     [(Term_Rewriting.Term
 (Labelings.Lab b [Arith.Nat]) [Arith.Char],
Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
                                       [(Term_Rewriting.Term
   (Labelings.Lab b [Arith.Nat]) [Arith.Char],
  Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
 Sum_Type.Sum (String -> String) a;
csr_rta08_dependency_pairs_tt j mu r p =
  let {
    d = Term_Rewriting.defined_list r;
    g = csr_rta08_CSDP_list Labelings.Sharp r mu d;
  } in (case Error_Monad.bind (Term_Rewriting.check_wf_trs r)
               (\ _ ->
                 Error_Monad.bind
                   (Error_Monad.catch_error
                     (Error_Monad.forallM
                       (\ (f, n) ->
                         Check_Monad.check
                           (not (Arith.membera d (Labelings.Sharp f, n)))
                           (Term_Rewriting.showsl_lit
                             "sharping yields a defined symbol"))
                       d)
                     (\ x -> Sum_Type.Inl (snd x)))
                   (\ _ ->
                     Error_Monad.bind
                       (Error_Monad.catch_error
                         (Error_Monad.catch_error
                           (Error_Monad.forallM
                             (\ x ->
                               (if Arith.membera p x then Sum_Type.Inr ()
                                 else Sum_Type.Inl x))
                             g)
                           (\ x -> Sum_Type.Inl (snd x)))
                         (\ _ ->
                           Sum_Type.Inl
                             (Term_Rewriting.showsl_lit
                               "missing RTA08 context-sensitive dependency pair")))
                       (\ _ ->
                         Error_Monad.catch_error
                           (Error_Monad.catch_error
                             (Error_Monad.forallM
                               (\ x ->
                                 (if Arith.membera g x then Sum_Type.Inr ()
                                   else Sum_Type.Inl x))
                               p)
                             (\ x -> Sum_Type.Inl (snd x)))
                           (\ _ ->
                             Sum_Type.Inl
                               (Term_Rewriting.showsl_lit
                                 "unexpected RTA08 context-sensitive dependency pair")))))
         of {
         Sum_Type.Inl a -> Sum_Type.Inl a;
         Sum_Type.Inr _ ->
           Sum_Type.Inr
             (Dependency_Pair_Problem_Spec.mk j False False p [] [] [] r);
       });

check_csr_dp_termination_proof_min ::
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
   c -> CSR_Checker_Base.Csr_dp_termination_proof b [Arith.Nat] [Arith.Char] ->
          Sum_Type.Sum (String -> String) ();
check_csr_dp_termination_proof_min ia j mu a i dpp
  CSR_Checker_Base.CSR_DP_P_is_Empty =
  CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
    CSR_Checker_Base.CSR_DP_P_is_Empty;
check_csr_dp_termination_proof_min ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof prf) =
  check_csr_dp_ordinary_min ia j mu a i dpp prf;
check_csr_dp_termination_proof_min ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Subterm_Criterion_Proc p rseq pr prf) =
  CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
    (CSR_Checker_Base.CSR_DP_Subterm_Criterion_Proc p rseq pr prf);
check_csr_dp_termination_proof_min ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Gen_Subterm_Criterion_Proc p pr prf) =
  CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
    (CSR_Checker_Base.CSR_DP_Gen_Subterm_Criterion_Proc p pr prf);
check_csr_dp_termination_proof_min ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Usable_Rules_Proc u prf) =
  FOR_Preliminaries.debug i "QCS usable rules"
    (Error_Monad.bind
      (Error_Monad.catch_error (csr_qcs_usable_rules_proc j mu u dpp)
        (\ x ->
          Sum_Type.Inl
            ((i . Term_Rewriting.showsl_lit
                    ": error when applying QCS usable rules\n") .
              x)))
      (\ dppa ->
        Error_Monad.catch_error
          (check_csr_dp_termination_proof_min ia j mu a
            (Term_Rewriting.add_index i Arith.one_nat) dppa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below QCS usable rules\n") .
                x))));
check_csr_dp_termination_proof_min ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Dep_Graph_Proc edpts) =
  FOR_Preliminaries.debug i "minimal CSR-DP dependency graph"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (CSR_Checker.check_csr_dep_graph_proc j mu dpp edpts)
        (\ x ->
          Sum_Type.Inl
            ((i . Term_Rewriting.showsl_lit
                    ": error when applying minimal CSR dependency graph\n") .
              x)))
      (\ _ ->
        Error_Monad.catch_error
          (check_csr_dp_graph_components_min ia j mu a i dpp edpts)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below minimal CSR dependency graph\n") .
                x))));
check_csr_dp_termination_proof_min ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Instantiation_Proc st sts prf) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": context-sensitive instantiation requires improved CS-DPs");
check_csr_dp_termination_proof_min ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Size_Change_Subterm_Proc graphs) =
  (if Error_Monad.isOK (csr_sct_active_subterm_proc j mu graphs dpp)
    then FOR_Preliminaries.debug i "active CSR size-change" (Sum_Type.Inr ())
    else CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
           (CSR_Checker_Base.CSR_DP_Size_Change_Subterm_Proc graphs));

check_csr_dp_graph_components_min ::
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
   c -> [(Maybe (CSR_Checker_Base.Csr_dp_termination_proof b [Arith.Nat]
                  [Arith.Char]),
           [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
              Term_Rewriting.Term (Labelings.Lab b [Arith.Nat])
                [Arith.Char])])] ->
          Sum_Type.Sum (String -> String) ();
check_csr_dp_graph_components_min ia j mu a i dpp [] = Sum_Type.Inr ();
check_csr_dp_graph_components_min ia j mu a i dpp ((Nothing, p) : rest) =
  check_csr_dp_graph_components_min ia j mu a
    (Term_Rewriting.add_index i Arith.one_nat) dpp rest;
check_csr_dp_graph_components_min ia j mu a i dpp ((Just prf, p) : rest) =
  Error_Monad.bind
    (check_csr_dp_termination_proof_min ia j mu a
      (Term_Rewriting.add_index i Arith.one_nat)
      (Dependency_Pair_Problem_Spec.intersect_pairs j dpp p) prf)
    (\ _ ->
      check_csr_dp_graph_components_min ia j mu a
        (Term_Rewriting.add_index i Arith.one_nat) dpp rest);

check_csr_termination_proof_min ::
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
     CSR_Checker_Base.Csr_termination_proof b [Arith.Nat] [Arith.Char] ->
       Sum_Type.Sum (String -> String) ();
check_csr_termination_proof_min ia j a i mu r CSR_Checker_Base.CSR_R_is_Empty =
  CSR_Checker.check_csr_termination_proof ia j a i mu r
    CSR_Checker_Base.CSR_R_is_Empty;
check_csr_termination_proof_min ia j a i mu r
  (CSR_Checker_Base.CSR_Rule_Removal redp rr prf) =
  FOR_Preliminaries.debug i "CSR rule removal"
    (case CSR_Checker_Base.csr_rule_removal_impl redp mu rr r of {
      Sum_Type.Inl aa -> Sum_Type.Inl aa;
      Sum_Type.Inr r2 -> check_csr_termination_proof_min ia j a i mu r2 prf;
    });
check_csr_termination_proof_min ia j a i mu r
  (CSR_Checker_Base.CSR_Dependency_Pairs p prf) =
  FOR_Preliminaries.debug i "minimal CSR dependency pairs"
    (Error_Monad.bind
      (Error_Monad.catch_error (CSR_Checker_Base.csr_sharp_mu_check mu)
        (\ x ->
          Sum_Type.Inl
            ((i . Term_Rewriting.showsl_lit
                    ": invalid replacement map for CSR dependency pairs\n") .
              x)))
      (\ _ ->
        Error_Monad.bind
          (Error_Monad.catch_error (csr_rules_sharp_fresh_check r)
            (\ x ->
              Sum_Type.Inl
                ((i . Term_Rewriting.showsl_lit
                        ": invalid sharp symbol in source CSR\n") .
                  x)))
          (\ _ ->
            (case CSR_Checker_Base.mu_csr_dependency_pairs_tt Labelings.Sharp j
                    mu r p
              of {
              Sum_Type.Inl _ ->
                (case csr_rta08_dependency_pairs_tt j mu r p of {
                  Sum_Type.Inl _ ->
                    Error_Monad.bind
                      (Error_Monad.catch_error
                        (CSR_Checker_Base.safe_csr_dependency_pairs_tt
                          Labelings.Sharp j mu r p)
                        (\ x ->
                          Sum_Type.Inl
                            ((i . Term_Rewriting.showsl_lit
                                    ": error when switching from CSR to a safe CS-DP problem\n") .
                              x)))
                      (\ dpp ->
                        Error_Monad.catch_error
                          (CSR_Checker_Base.check_csr_dp_termination_proof ia j
                            False (Term_Rewriting.add_index i Arith.one_nat) dpp
                            prf)
                          (\ x ->
                            Sum_Type.Inl
                              ((i . Term_Rewriting.showsl_lit
                                      ": error below safe CSR dependency pairs\n") .
                                x)));
                  Sum_Type.Inr dpp ->
                    Error_Monad.catch_error
                      (check_csr_rta08_dp_first ia j mu
                        (Term_Rewriting.add_index i Arith.one_nat) dpp prf)
                      (\ x ->
                        Sum_Type.Inl
                          ((i . Term_Rewriting.showsl_lit
                                  ": error below RTA08 collapsing CSR dependency pairs\n") .
                            x));
                });
              Sum_Type.Inr dpp ->
                Error_Monad.catch_error
                  (check_csr_dp_termination_proof_min ia j mu False
                    (Term_Rewriting.add_index i Arith.one_nat) dpp prf)
                  (\ x ->
                    Sum_Type.Inl
                      ((i . Term_Rewriting.showsl_lit
                              ": error below replacement-map-specific CSR dependency pairs\n") .
                        x));
            }))));
check_csr_termination_proof_min ia j a i mu r
  (CSR_Checker_Base.CSR_Safe_Dependency_Pairs p prf) =
  CSR_Checker.check_csr_termination_proof ia j a i mu r
    (CSR_Checker_Base.CSR_Safe_Dependency_Pairs p prf);

}
