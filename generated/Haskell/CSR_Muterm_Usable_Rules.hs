{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  CSR_Muterm_Usable_Rules(Muterm_typed_dp_proof(..), muterm_mu_positions_list,
                           muterm_expanded_pairs_list,
                           muterm_qcs_ur_closed_check,
                           muterm_marked_mu_pairs_check,
                           check_muterm_typed_dp_proof,
                           muterm_innermost_ur_closed_check)
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
import qualified CSR_Checker;
import qualified Complex_Constant_Removal_Impl;
import qualified Check_Termination_Common;
import qualified Bounded_Increase_Impl;
import qualified Semantic_Labeling_Carrier;
import qualified Critical_Pairs_Impl;
import qualified Subterm_Criterion_Impl;
import qualified Fun;
import qualified Graph;
import qualified Multi_Map;
import qualified Mapping;
import qualified RenamingN_String;
import qualified FOR_Preliminaries;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Dependency_Pair_Problem_Spec;
import qualified Termination_Problem_Spec;
import qualified Sum_Type;
import qualified Countable;
import qualified Compare;
import qualified Compare_Order_Instances;
import qualified Lists_are_Infinite;
import qualified CSR_Minimal_CSDP_Proofs;
import qualified HOL;
import qualified Missing_List;
import qualified Map;
import qualified Context_Sensitive_Impl;
import qualified RenamingN;
import qualified Arith;
import qualified Fresh;
import qualified Reduction_Pair_Implementations;
import qualified CSR_Checker_Base;
import qualified Check_Termination;
import qualified Labelings;
import qualified Term_Rewriting;

data Muterm_typed_dp_proof a b c = Muterm_Typed_P_Is_Empty
  | Muterm_Typed_Local_Usable
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Check_Termination.Dp_termination_proof a b c)
  | Muterm_Typed_CSR_Proof (CSR_Checker_Base.Csr_dp_termination_proof a b c)
  | Muterm_Typed_Expanded_CSR_Proof
      (CSR_Checker_Base.Csr_dp_termination_proof a b c)
  | Muterm_Typed_Expanded_Local_Usable
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Check_Termination.Dp_termination_proof a b c)
  | Muterm_Typed_Expanded_Strong_Usable
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Reduction_Pair_Implementations.Redtriple_impl (Labelings.Lab a b))
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (CSR_Checker_Base.Csr_dp_termination_proof a b c)
  | Muterm_Typed_Expanded_Ordinary
      (Check_Termination.Dp_termination_proof a b c)
  | Muterm_Typed_Dep_Graph
      [(Maybe (Muterm_typed_dp_proof a b c),
         [(Term_Rewriting.Term (Labelings.Lab a b) c,
            Term_Rewriting.Term (Labelings.Lab a b) c)])];

var_of_term :: forall a b. Term_Rewriting.Term a b -> b;
var_of_term (Term_Rewriting.Var x) = x;
var_of_term (Term_Rewriting.Fun f ts) = error "undefined";

muterm_rename_many ::
  forall a. (Fresh.Infinite a) => RenamingN.RenamingN a -> Arith.Nat -> a -> a;
muterm_rename_many ren i = (\ v -> RenamingN.rename_many ren (i, v));

muterm_dp_mu_poss_list ::
  forall a b.
    (Eq a) => [((a, Arith.Nat), [Arith.Nat])] ->
                Term_Rewriting.Term a b -> [[Arith.Nat]];
muterm_dp_mu_poss_list mu (Term_Rewriting.Var x) = [[]];
muterm_dp_mu_poss_list mu (Term_Rewriting.Fun f ts) =
  [] : concat
         (Arith.map_filter
           (\ x ->
             (if Arith.member x
                   (Context_Sensitive_Impl.mu_of mu (f, Arith.size_list ts))
               then Just (map (\ a -> x : a)
                           (muterm_dp_mu_poss_list mu (Arith.nth ts x)))
               else Nothing))
           (Arith.upt Arith.zero_nat (Arith.size_list ts)));

muterm_compose_collapsing_pair ::
  forall a b c.
    (Fresh.Infinite a,
      Eq a) => RenamingN.RenamingN a ->
                 Term_Rewriting.Term b a ->
                   a -> Term_Rewriting.Term b a ->
                          Term_Rewriting.Term c a ->
                            (Term_Rewriting.Term b a, Term_Rewriting.Term c a);
muterm_compose_collapsing_pair ren l x a b =
  let {
    rp = muterm_rename_many ren Arith.zero_nat;
    rs = RenamingN.rename_single ren;
    la = Term_Rewriting.map_term (\ xa -> xa) rp l;
    aa = Term_Rewriting.map_term (\ xa -> xa) rs a;
    ba = Term_Rewriting.map_term (\ xa -> xa) rs b;
  } in (Term_Rewriting.eval_term Term_Rewriting.Fun la
          (Fun.fun_upd Term_Rewriting.Var (rp x) aa),
         ba);

muterm_expand_one_pair ::
  forall a b c.
    (Fresh.Infinite a,
      Eq a) => RenamingN.RenamingN a ->
                 [(Term_Rewriting.Term b a, Term_Rewriting.Term c a)] ->
                   (Term_Rewriting.Term b a, Term_Rewriting.Term c a) ->
                     [(Term_Rewriting.Term b a, Term_Rewriting.Term c a)];
muterm_expand_one_pair ren s (l, Term_Rewriting.Var x) =
  map (\ (a, b) -> muterm_compose_collapsing_pair ren l x a b) s;
muterm_expand_one_pair ren s (l, Term_Rewriting.Fun f ts) =
  [(Term_Rewriting.map_term (\ x -> x) (muterm_rename_many ren Arith.zero_nat)
      l,
     Term_Rewriting.map_term (\ x -> x) (muterm_rename_many ren Arith.zero_nat)
       (Term_Rewriting.Fun f ts))];

muterm_mu_positions_list ::
  forall a.
    (Eq a) => [((a, Arith.Nat), [Arith.Nat])] -> (a, Arith.Nat) -> [Arith.Nat];
muterm_mu_positions_list mu fn =
  (case Map.map_of mu fn of {
    Nothing -> Arith.upt Arith.zero_nat (snd fn);
    Just a -> Missing_List.remdups_sort a;
  });

muterm_dp_mu_fun_poss_list ::
  forall a b.
    (Eq a) => [((a, Arith.Nat), [Arith.Nat])] ->
                Term_Rewriting.Term a b -> [[Arith.Nat]];
muterm_dp_mu_fun_poss_list mu (Term_Rewriting.Var x) = [];
muterm_dp_mu_fun_poss_list mu (Term_Rewriting.Fun f ts) =
  [] : concat
         (Arith.map_filter
           (\ x ->
             (if Arith.member x
                   (Context_Sensitive_Impl.mu_of mu (f, Arith.size_list ts))
               then Just (map (\ a -> x : a)
                           (muterm_dp_mu_fun_poss_list mu (Arith.nth ts x)))
               else Nothing))
           (Arith.upt Arith.zero_nat (Arith.size_list ts)));

muterm_expanded_pairs_list ::
  forall a b c.
    (Fresh.Infinite a,
      Eq a) => RenamingN.RenamingN a ->
                 [(Term_Rewriting.Term b a, Term_Rewriting.Term c a)] ->
                   [(Term_Rewriting.Term b a, Term_Rewriting.Term c a)] ->
                     [(Term_Rewriting.Term b a, Term_Rewriting.Term c a)];
muterm_expanded_pairs_list ren p s = concatMap (muterm_expand_one_pair ren s) p;

muterm_qcs_ur_closed_check ::
  forall a b c d e f.
    (Eq a, Eq b, Eq c,
      Eq d) => [(Term_Rewriting.Term (Labelings.Lab a b) c,
                  Term_Rewriting.Term (Labelings.Lab a b) d)] ->
                 [(Term_Rewriting.Term (Labelings.Lab a b) c,
                    Term_Rewriting.Term (Labelings.Lab a b) d)] ->
                   [(Term_Rewriting.Term (Labelings.Lab a b) c,
                      Term_Rewriting.Term (Labelings.Lab a b) d)] ->
                     [((Labelings.Lab a b, Arith.Nat), [Arith.Nat])] ->
                       [(e, Term_Rewriting.Term (Labelings.Lab a b) f)] -> Bool;
muterm_qcs_ur_closed_check r s w mu p =
  all (Arith.membera w) s &&
    all (\ lr -> Arith.membera r lr || Arith.membera s lr) w &&
      let {
        u = filter (Arith.membera r) w;
      } in all (\ lr ->
                 CSR_Minimal_CSDP_Proofs.qcs_ur_closed_term_check r u mu
                   (snd lr))
             u &&
             all (\ lr ->
                   CSR_Minimal_CSDP_Proofs.qcs_ur_closed_dp_rhs_check r u mu
                     (snd lr))
               s &&
               all (\ dp ->
                     Term_Rewriting.is_Var (snd dp) ||
                       CSR_Minimal_CSDP_Proofs.qcs_ur_closed_dp_rhs_check r u mu
                         (snd dp))
                 p;

muterm_dp_non_mu_vars_term_list ::
  forall a b.
    (Eq a) => [((a, Arith.Nat), [Arith.Nat])] -> Term_Rewriting.Term a b -> [b];
muterm_dp_non_mu_vars_term_list mu t =
  Arith.map_filter
    (\ x ->
      (if not (Arith.membera (muterm_dp_mu_poss_list mu t) x)
        then Just (var_of_term (Term_Rewriting.subt_at t x)) else Nothing))
    (Term_Rewriting.var_poss_list t);

muterm_dp_mu_vars_term_list ::
  forall a b.
    (Eq a) => [((a, Arith.Nat), [Arith.Nat])] -> Term_Rewriting.Term a b -> [b];
muterm_dp_mu_vars_term_list mu (Term_Rewriting.Var x) = [x];
muterm_dp_mu_vars_term_list mu (Term_Rewriting.Fun f ts) =
  concat
    (Arith.map_filter
      (\ x ->
        (if Arith.member x
              (Context_Sensitive_Impl.mu_of mu (f, Arith.size_list ts))
          then Just (muterm_dp_mu_vars_term_list mu (Arith.nth ts x))
          else Nothing))
      (Arith.upt Arith.zero_nat (Arith.size_list ts)));

muterm_dp_strongly_conservative_check ::
  forall a b.
    (Eq a, Arith.Card_UNIV b, Arith.Ceq b, Arith.Cproper_interval b, Eq b,
      Arith.Set_impl b) => [((a, Arith.Nat), [Arith.Nat])] ->
                             [(Term_Rewriting.Term a b,
                                Term_Rewriting.Term a b)] ->
                               Bool;
muterm_dp_strongly_conservative_check mu t =
  all (\ (l, r) ->
        all (Arith.membera (muterm_dp_mu_vars_term_list mu l))
          (muterm_dp_mu_vars_term_list mu r))
    t &&
    all (\ (l, r) ->
          Arith.is_empty
            (Arith.inf_set (Arith.set (muterm_dp_mu_vars_term_list mu l))
              (Arith.set (muterm_dp_non_mu_vars_term_list mu l))) &&
            Arith.is_empty
              (Arith.inf_set (Arith.set (muterm_dp_mu_vars_term_list mu r))
                (Arith.set (muterm_dp_non_mu_vars_term_list mu r))))
      t;

muterm_dp_active_ur_closed_check ::
  forall a b c d e.
    (Eq a, Eq b,
      Eq c) => [(Term_Rewriting.Term a b, Term_Rewriting.Term a c)] ->
                 [(Term_Rewriting.Term a b, Term_Rewriting.Term a c)] ->
                   [((a, Arith.Nat), [Arith.Nat])] ->
                     [(d, Term_Rewriting.Term a e)] -> Bool;
muterm_dp_active_ur_closed_check r u mu p =
  all (Arith.membera r) u &&
    all (\ dp ->
          Term_Rewriting.is_Var (snd dp) ||
            CSR_Minimal_CSDP_Proofs.csr_u3_root_rules_check r u (snd dp)
              (muterm_dp_mu_fun_poss_list mu (snd dp)))
      p &&
      all (\ lr ->
            CSR_Minimal_CSDP_Proofs.csr_u3_root_rules_check r u (snd lr)
              (muterm_dp_mu_fun_poss_list mu (snd lr)))
        u;

muterm_marked_mu_pairs_check ::
  forall a b c d.
    (Eq a,
      Eq b) => [((Labelings.Lab a b, Arith.Nat), [Arith.Nat])] ->
                 [(Term_Rewriting.Term (Labelings.Lab a b) c,
                    Term_Rewriting.Term (Labelings.Lab a b) d)] ->
                   Bool;
muterm_marked_mu_pairs_check mu p =
  all (\ (l, r) ->
        (case Term_Rewriting.root l of {
          Nothing -> False;
          Just (Labelings.Lab _ _, _) -> False;
          Just (Labelings.FunLab _ _, _) -> False;
          Just (Labelings.UnLab _, _) -> False;
          Just (Labelings.Sharp f, n) ->
            muterm_mu_positions_list mu (Labelings.Sharp f, n) ==
              muterm_mu_positions_list mu (f, n);
        }) &&
          (case Term_Rewriting.root r of {
            Nothing -> False;
            Just (Labelings.Lab _ _, _) -> False;
            Just (Labelings.FunLab _ _, _) -> False;
            Just (Labelings.UnLab _, _) -> False;
            Just (Labelings.Sharp f, n) ->
              muterm_mu_positions_list mu (Labelings.Sharp f, n) ==
                muterm_mu_positions_list mu (f, n);
          }))
    p;

muterm_strong_ur_redpair_proc ::
  forall a b c d.
    (Eq b, Term_Rewriting.Showl b, Eq c, Term_Rewriting.Showl c,
      Arith.Card_UNIV d, Arith.Ceq d, Arith.Cproper_interval d, Eq d,
      Arith.Set_impl d,
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
muterm_strong_ur_redpair_proc j mu rp premove u dpp =
  (case Error_Monad.bind (Term_Rewriting.rel_impl_redpair rp)
          (\ _ ->
            (case Dependency_Pair_Problem_Spec.split_pairs j dpp premove of {
              (ps, pns) ->
                Error_Monad.bind
                  (Check_Monad.check
                    (CSR_Minimal_CSDP_Proofs.csr_sharp_pairs_check
                      (Dependency_Pair_Problem_Spec.pairs j dpp))
                    (Term_Rewriting.showsl_lit
                      "strong MU-TERM usable-rule processor requires marked pairs"))
                  (\ _ ->
                    Error_Monad.bind
                      (Check_Monad.check
                        (muterm_marked_mu_pairs_check mu
                          (Dependency_Pair_Problem_Spec.pairs j dpp))
                        (Term_Rewriting.showsl_lit
                          "marked replacement-map entries differ from their source symbols"))
                      (\ _ ->
                        Error_Monad.bind
                          (Check_Monad.check
                            (muterm_dp_active_ur_closed_check
                              (Dependency_Pair_Problem_Spec.rules j dpp) u mu
                              (Dependency_Pair_Problem_Spec.pairs j dpp))
                            (Term_Rewriting.showsl_lit
                              "supplied rules are not a closed active MU-TERM set"))
                          (\ _ ->
                            Error_Monad.bind
                              (Check_Monad.check
                                (muterm_dp_strongly_conservative_check mu
                                  (Dependency_Pair_Problem_Spec.pairs j dpp ++
                                    u))
                                (Term_Rewriting.showsl_lit
                                  "strong MU-TERM conservativity condition failed"))
                              (\ _ ->
                                Error_Monad.bind (Term_Rewriting.ce_compat rp)
                                  (\ _ ->
                                    Error_Monad.bind
                                      (Term_Rewriting.rel_impl_ns rp (u ++ pns))
                                      (\ _ ->
Term_Rewriting.rel_impl_s rp ps))))));
            }))
    of {
    Sum_Type.Inl a -> Sum_Type.Inl a;
    Sum_Type.Inr _ ->
      Sum_Type.Inr
        (Dependency_Pair_Problem_Spec.delete_P_Pw j dpp premove premove);
  });

check_muterm_expanded_csr_proof ::
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
check_muterm_expanded_csr_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Dep_Graph_Proc edpts) =
  FOR_Preliminaries.debug i "expanded MU-TERM CSR dependency graph"
    (Error_Monad.bind (CSR_Checker.check_csr_dep_graph_proc j mu dpp edpts)
      (\ _ -> check_muterm_expanded_csr_components ia j mu i dpp edpts));
check_muterm_expanded_csr_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_UR_Proc redp pr u subprf))
  = (case muterm_strong_ur_redpair_proc j mu
            (Reduction_Pair_Implementations.get_rel_impl redp) pr u dpp
      of {
      Sum_Type.Inl _ ->
        CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False
          i dpp
          (CSR_Checker_Base.CSR_DP_Ordinary_Proof
            (Check_Termination.Redpair_UR_Proc redp pr u subprf));
      Sum_Type.Inr dppa ->
        FOR_Preliminaries.debug i
          "expanded strong MU-TERM usable-rule reduction pair"
          (CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu
            False (Term_Rewriting.add_index i Arith.one_nat) dppa
            (CSR_Checker_Base.CSR_DP_Ordinary_Proof subprf));
    });
check_muterm_expanded_csr_proof ia j mu i dpp CSR_Checker_Base.CSR_DP_P_is_Empty
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False i
      dpp CSR_Checker_Base.CSR_DP_P_is_Empty;
check_muterm_expanded_csr_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof Check_Termination.P_is_Empty) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False i dpp
    (CSR_Checker_Base.CSR_DP_Ordinary_Proof Check_Termination.P_is_Empty);
check_muterm_expanded_csr_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Subterm_Criterion_Proc va vb vc vd))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False i
      dpp (CSR_Checker_Base.CSR_DP_Ordinary_Proof
            (Check_Termination.Subterm_Criterion_Proc va vb vc vd));
check_muterm_expanded_csr_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Gen_Subterm_Criterion_Proc va vb vc))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False i
      dpp (CSR_Checker_Base.CSR_DP_Ordinary_Proof
            (Check_Termination.Gen_Subterm_Criterion_Proc va vb vc));
check_muterm_expanded_csr_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_Proc va vb vc))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False i
      dpp (CSR_Checker_Base.CSR_DP_Ordinary_Proof
            (Check_Termination.Redpair_Proc va vb vc));
check_muterm_expanded_csr_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Usable_Rules_Proc va vb))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False i
      dpp (CSR_Checker_Base.CSR_DP_Ordinary_Proof
            (Check_Termination.Usable_Rules_Proc va vb));
check_muterm_expanded_csr_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof (Check_Termination.Dep_Graph_Proc va))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False i
      dpp (CSR_Checker_Base.CSR_DP_Ordinary_Proof
            (Check_Termination.Dep_Graph_Proc va));
check_muterm_expanded_csr_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Mono_Redpair_Proc va vb vc vd))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False i
      dpp (CSR_Checker_Base.CSR_DP_Ordinary_Proof
            (Check_Termination.Mono_Redpair_Proc va vb vc vd));
check_muterm_expanded_csr_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Mono_URM_Redpair_Proc va vb vc vd))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False i
      dpp (CSR_Checker_Base.CSR_DP_Ordinary_Proof
            (Check_Termination.Mono_URM_Redpair_Proc va vb vc vd));
check_muterm_expanded_csr_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Mono_Redpair_UR_Proc va vb vc vd ve))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False i
      dpp (CSR_Checker_Base.CSR_DP_Ordinary_Proof
            (Check_Termination.Mono_Redpair_UR_Proc va vb vc vd ve));
check_muterm_expanded_csr_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Size_Change_Subterm_Proc va))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False i
      dpp (CSR_Checker_Base.CSR_DP_Ordinary_Proof
            (Check_Termination.Size_Change_Subterm_Proc va));
check_muterm_expanded_csr_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Size_Change_Redpair_Proc va vb vc))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False i
      dpp (CSR_Checker_Base.CSR_DP_Ordinary_Proof
            (Check_Termination.Size_Change_Redpair_Proc va vb vc));
check_muterm_expanded_csr_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Uncurry_Proc va vb vc vd ve))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False i
      dpp (CSR_Checker_Base.CSR_DP_Ordinary_Proof
            (Check_Termination.Uncurry_Proc va vb vc vd ve));
check_muterm_expanded_csr_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Fcc_Proc va vb vc vd ve))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False i
      dpp (CSR_Checker_Base.CSR_DP_Ordinary_Proof
            (Check_Termination.Fcc_Proc va vb vc vd ve));
check_muterm_expanded_csr_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Split_Proc va vb vc vd))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False i
      dpp (CSR_Checker_Base.CSR_DP_Ordinary_Proof
            (Check_Termination.Split_Proc va vb vc vd));
check_muterm_expanded_csr_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Semlab_Proc va vb vc vd ve))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False i
      dpp (CSR_Checker_Base.CSR_DP_Ordinary_Proof
            (Check_Termination.Semlab_Proc va vb vc vd ve));
check_muterm_expanded_csr_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Switch_Innermost_Proc va vb))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False i
      dpp (CSR_Checker_Base.CSR_DP_Ordinary_Proof
            (Check_Termination.Switch_Innermost_Proc va vb));
check_muterm_expanded_csr_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Rewriting_Proc va vb vc vd ve vf vg))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False i
      dpp (CSR_Checker_Base.CSR_DP_Ordinary_Proof
            (Check_Termination.Rewriting_Proc va vb vc vd ve vf vg));
check_muterm_expanded_csr_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Instantiation_Proc va vb vc))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False i
      dpp (CSR_Checker_Base.CSR_DP_Ordinary_Proof
            (Check_Termination.Instantiation_Proc va vb vc));
check_muterm_expanded_csr_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Forward_Instantiation_Proc va vb vc vd))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False i
      dpp (CSR_Checker_Base.CSR_DP_Ordinary_Proof
            (Check_Termination.Forward_Instantiation_Proc va vb vc vd));
check_muterm_expanded_csr_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Narrowing_Proc va vb vc vd))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False i
      dpp (CSR_Checker_Base.CSR_DP_Ordinary_Proof
            (Check_Termination.Narrowing_Proc va vb vc vd));
check_muterm_expanded_csr_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Assume_Finite va vb))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False i
      dpp (CSR_Checker_Base.CSR_DP_Ordinary_Proof
            (Check_Termination.Assume_Finite va vb));
check_muterm_expanded_csr_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Q_Reduction_Proc va vb))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False i
      dpp (CSR_Checker_Base.CSR_DP_Ordinary_Proof
            (Check_Termination.Q_Reduction_Proc va vb));
check_muterm_expanded_csr_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Complex_Constant_Removal_Proc va vb))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False i
      dpp (CSR_Checker_Base.CSR_DP_Ordinary_Proof
            (Check_Termination.Complex_Constant_Removal_Proc va vb));
check_muterm_expanded_csr_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.General_Redpair_Proc va vb vc vd ve))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False i
      dpp (CSR_Checker_Base.CSR_DP_Ordinary_Proof
            (Check_Termination.General_Redpair_Proc va vb vc vd ve));
check_muterm_expanded_csr_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof (Check_Termination.To_Trs_Proc va)) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False i dpp
    (CSR_Checker_Base.CSR_DP_Ordinary_Proof (Check_Termination.To_Trs_Proc va));
check_muterm_expanded_csr_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Subterm_Criterion_Proc v va vb vc) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False i dpp
    (CSR_Checker_Base.CSR_DP_Subterm_Criterion_Proc v va vb vc);
check_muterm_expanded_csr_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Gen_Subterm_Criterion_Proc v va vb) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False i dpp
    (CSR_Checker_Base.CSR_DP_Gen_Subterm_Criterion_Proc v va vb);
check_muterm_expanded_csr_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Usable_Rules_Proc v va) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False i dpp
    (CSR_Checker_Base.CSR_DP_Usable_Rules_Proc v va);
check_muterm_expanded_csr_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Instantiation_Proc v va vb) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False i dpp
    (CSR_Checker_Base.CSR_DP_Instantiation_Proc v va vb);
check_muterm_expanded_csr_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Forward_Instantiation_Proc v va vb) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False i dpp
    (CSR_Checker_Base.CSR_DP_Forward_Instantiation_Proc v va vb);
check_muterm_expanded_csr_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Redpair_UR_Proc v va vb vc) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False i dpp
    (CSR_Checker_Base.CSR_DP_Redpair_UR_Proc v va vb vc);
check_muterm_expanded_csr_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Size_Change_Subterm_Proc v) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False i dpp
    (CSR_Checker_Base.CSR_DP_Size_Change_Subterm_Proc v);

check_muterm_expanded_csr_components ::
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
 c -> [(Maybe (CSR_Checker_Base.Csr_dp_termination_proof b [Arith.Nat]
                [Arith.Char]),
         [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
            Term_Rewriting.Term (Labelings.Lab b [Arith.Nat])
              [Arith.Char])])] ->
        Sum_Type.Sum (String -> String) ();
check_muterm_expanded_csr_components ia j mu i dpp [] = Sum_Type.Inr ();
check_muterm_expanded_csr_components ia j mu i dpp ((Nothing, c) : rest) =
  check_muterm_expanded_csr_components ia j mu
    (Term_Rewriting.add_index i Arith.one_nat) dpp rest;
check_muterm_expanded_csr_components ia j mu i dpp ((Just prf, c) : rest) =
  Error_Monad.bind
    (check_muterm_expanded_csr_proof ia j mu
      (Term_Rewriting.add_index i Arith.one_nat)
      (Dependency_Pair_Problem_Spec.intersect_pairs j dpp c) prf)
    (\ _ ->
      check_muterm_expanded_csr_components ia j mu
        (Term_Rewriting.add_index i Arith.one_nat) dpp rest);

check_muterm_typed_dep_graph ::
  forall a b c d.
    (Compare.Compare a, Eq a, Term_Rewriting.Showl a, Compare.Compare b, Eq b,
      Term_Rewriting.Showl b, Compare.Compare_order c, Eq c,
      Term_Rewriting.Showl c) => [((Labelings.Lab a b, Arith.Nat),
                                    [Arith.Nat])] ->
                                   [(Term_Rewriting.Term (Labelings.Lab a b) c,
                                      Term_Rewriting.Term (Labelings.Lab a b)
c)] ->
                                     [(Term_Rewriting.Term (Labelings.Lab a b)
 c,
Term_Rewriting.Term (Labelings.Lab a b) c)] ->
                                       [(Term_Rewriting.Term (Labelings.Lab a b)
   c,
  Term_Rewriting.Term (Labelings.Lab a b) c)] ->
 [(Maybe d,
    [(Term_Rewriting.Term (Labelings.Lab a b) c,
       Term_Rewriting.Term (Labelings.Lab a b) c)])] ->
   Sum_Type.Sum (String -> String) ();
check_muterm_typed_dep_graph mu r s p dps =
  Error_Monad.bind (Term_Rewriting.check_wf_trs (r ++ s))
    (\ _ ->
      Error_Monad.bind
        (Error_Monad.catch_error
          (Check_Monad.check_subseteq p (concatMap snd dps))
          (\ x ->
            Sum_Type.Inl
              ((Term_Rewriting.showsl_lit "typed MU-TERM dependency pair " .
                 Term_Rewriting.showsl_rule x) .
                Term_Rewriting.showsl_lit " is missing in decomposition\n")))
        (\ _ ->
          Graph.check_graph_decomp (Term_Rewriting.showsl_prod . fst)
            (Multi_Map.empty ((Term_Rewriting.root . fst) . fst))
            CSR_Checker_Base.graph_approx_csr_rt Multi_Map.insert
            (CSR_Checker_Base.csr_dep_graph_edge_check
              (CSR_Checker_Base.csr_dp_root_mu
                (Context_Sensitive_Impl.mu_of mu))
              (r ++ s))
            (map (\ (real, cs) ->
                   (not (Arith.is_none real),
                     map (\ (sa, t) -> ((sa, t), ())) cs))
              dps)));

check_muterm_typed_dp_proof ::
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
 [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
    Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
   [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
      Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
     [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
        Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
       Muterm_typed_dp_proof b [Arith.Nat] [Arith.Char] ->
         Sum_Type.Sum (String -> String) ();
check_muterm_typed_dp_proof ia j mu i r s p Muterm_Typed_P_Is_Empty =
  Check_Monad.check (null p)
    (i . Term_Rewriting.showsl_lit ": MU-TERM dependency pairs are not empty");
check_muterm_typed_dp_proof ia j mu i r s p (Muterm_Typed_Local_Usable u prf) =
  FOR_Preliminaries.debug i "MU-TERM ordinary reduction-pair continuation"
    (Error_Monad.bind
      (Check_Monad.check (all (Arith.membera u) s)
        (i . Term_Rewriting.showsl_lit
               ": MU-TERM usable rules omit an unhiding rule"))
      (\ _ ->
        Error_Monad.bind
          (Check_Monad.check
            (all (\ lr -> Arith.membera r lr || Arith.membera s lr) u)
            (i . Term_Rewriting.showsl_lit ": extraneous MU-TERM usable rule"))
          (\ _ ->
            let {
              ur = filter (Arith.membera r) u;
            } in Error_Monad.bind
                   (Check_Monad.check
                     (all (\ lr ->
                            CSR_Minimal_CSDP_Proofs.qcs_ur_closed_term_check r
                              ur mu (snd lr))
                       ur)
                     (i . Term_Rewriting.showsl_lit
                            ": ordinary MU-TERM rule closure failed"))
                   (\ _ ->
                     Error_Monad.bind
                       (Check_Monad.check
                         (all (\ lr ->
                                CSR_Minimal_CSDP_Proofs.qcs_ur_closed_dp_rhs_check
                                  r ur mu (snd lr))
                           s)
                         (i . Term_Rewriting.showsl_lit
                                ": MU-TERM unhiding closure failed"))
                       (\ _ ->
                         Error_Monad.bind
                           (Check_Monad.check
                             (all (\ dp ->
                                    Term_Rewriting.is_Var (snd dp) ||
                                      CSR_Minimal_CSDP_Proofs.qcs_ur_closed_dp_rhs_check
r ur mu (snd dp))
                               p)
                             (i . Term_Rewriting.showsl_lit
                                    ": MU-TERM pair closure failed"))
                           (\ _ ->
                             Check_Termination.check_dp_termination_proof ia j
                               False (Term_Rewriting.add_index i Arith.one_nat)
                               (Dependency_Pair_Problem_Spec.mk j False False p
                                 [] [] [] u)
                               prf))))));
check_muterm_typed_dp_proof ia j mu i r s p (Muterm_Typed_CSR_Proof prf) =
  FOR_Preliminaries.debug i "MU-TERM noncollapsing CSR component"
    (Error_Monad.bind
      (Check_Monad.check (all ((\ t -> not (Term_Rewriting.is_Var t)) . snd) p)
        (i . Term_Rewriting.showsl_lit
               ": collapsing pair requires the typed MU-TERM processor"))
      (\ _ ->
        let {
          dpp = Dependency_Pair_Problem_Spec.mk j False False p [] [] [] r;
        } in CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu
               False (Term_Rewriting.add_index i Arith.one_nat) dpp prf));
check_muterm_typed_dp_proof ia j mu i r s p
  (Muterm_Typed_Expanded_CSR_Proof prf) =
  FOR_Preliminaries.debug i "expanded typed MU-TERM CSR component"
    (let {
       e = muterm_expanded_pairs_list RenamingN_String.string_renameN p s;
       dpp = Dependency_Pair_Problem_Spec.mk j False False e [] [] [] r;
     } in check_muterm_expanded_csr_proof ia j mu
            (Term_Rewriting.add_index i Arith.one_nat) dpp prf);
check_muterm_typed_dp_proof ia j mu i r s p
  (Muterm_Typed_Expanded_Local_Usable u prf) =
  FOR_Preliminaries.debug i
    "expanded MU-TERM ordinary reduction-pair continuation"
    (Error_Monad.bind
      (Check_Monad.check (all (Arith.membera r) u)
        (i . Term_Rewriting.showsl_lit ": extraneous MU-TERM usable rule"))
      (\ _ ->
        Error_Monad.bind
          (Check_Monad.check
            (all (\ lr ->
                   CSR_Minimal_CSDP_Proofs.qcs_ur_closed_term_check r u mu
                     (snd lr))
              u)
            (i . Term_Rewriting.showsl_lit
                   ": ordinary MU-TERM rule closure failed"))
          (\ _ ->
            Error_Monad.bind
              (Check_Monad.check
                (all (\ lr ->
                       CSR_Minimal_CSDP_Proofs.qcs_ur_closed_dp_rhs_check r u mu
                         (snd lr))
                  s)
                (i . Term_Rewriting.showsl_lit
                       ": MU-TERM unhiding closure failed"))
              (\ _ ->
                Error_Monad.bind
                  (Check_Monad.check
                    (all (\ dp ->
                           Term_Rewriting.is_Var (snd dp) ||
                             CSR_Minimal_CSDP_Proofs.qcs_ur_closed_dp_rhs_check
                               r u mu (snd dp))
                      p)
                    (i . Term_Rewriting.showsl_lit
                           ": MU-TERM pair closure failed"))
                  (\ _ ->
                    let {
                      e = muterm_expanded_pairs_list
                            RenamingN_String.string_renameN p s;
                    } in Check_Termination.check_dp_termination_proof ia j False
                           (Term_Rewriting.add_index i Arith.one_nat)
                           (Dependency_Pair_Problem_Spec.mk j False False e []
                             [] [] u)
                           prf)))));
check_muterm_typed_dp_proof ia j mu i r s p
  (Muterm_Typed_Expanded_Strong_Usable u redp pr prf) =
  FOR_Preliminaries.debug i "expanded strong MU-TERM usable-rule reduction pair"
    (let {
       e = muterm_expanded_pairs_list RenamingN_String.string_renameN p s;
       dpp = Dependency_Pair_Problem_Spec.mk j False False e [] [] [] r;
     } in Error_Monad.bind
            (muterm_strong_ur_redpair_proc j mu
              (Reduction_Pair_Implementations.get_rel_impl redp) pr u dpp)
            (\ dppa ->
              CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu
                False (Term_Rewriting.add_index i Arith.one_nat) dppa prf));
check_muterm_typed_dp_proof ia j mu i r s p (Muterm_Typed_Expanded_Ordinary prf)
  = FOR_Preliminaries.debug i "expanded MU-TERM ordinary DP continuation"
      (let {
         e = muterm_expanded_pairs_list RenamingN_String.string_renameN p s;
       } in Check_Termination.check_dp_termination_proof ia j False
              (Term_Rewriting.add_index i Arith.one_nat)
              (Dependency_Pair_Problem_Spec.mk j False False e [] [] [] r) prf);
check_muterm_typed_dp_proof ia j mu i r s p (Muterm_Typed_Dep_Graph edps) =
  FOR_Preliminaries.debug i "typed MU-TERM dependency graph"
    (Error_Monad.bind (check_muterm_typed_dep_graph mu r s p edps)
      (\ _ -> check_muterm_typed_graph_components ia j mu i r s p edps));

check_muterm_typed_graph_components ::
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
 [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
    Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
   [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
      Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
     [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
        Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
       [(Maybe (Muterm_typed_dp_proof b [Arith.Nat] [Arith.Char]),
          [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
             Term_Rewriting.Term (Labelings.Lab b [Arith.Nat])
               [Arith.Char])])] ->
         Sum_Type.Sum (String -> String) ();
check_muterm_typed_graph_components ia j mu i r s p [] = Sum_Type.Inr ();
check_muterm_typed_graph_components ia j mu i r s p ((Nothing, c) : rest) =
  check_muterm_typed_graph_components ia j mu
    (Term_Rewriting.add_index i Arith.one_nat) r s p rest;
check_muterm_typed_graph_components ia j mu i r s p ((Just prf, c) : rest) =
  Error_Monad.bind
    (check_muterm_typed_dp_proof ia j mu
      (Term_Rewriting.add_index i Arith.one_nat) r s
      (filter (Arith.membera c) p) prf)
    (\ _ ->
      check_muterm_typed_graph_components ia j mu
        (Term_Rewriting.add_index i Arith.one_nat) r s p rest);

muterm_innermost_ur_closed_check ::
  forall a b c d e.
    (Eq a, Eq b,
      Eq c) => [(Term_Rewriting.Term a b, Term_Rewriting.Term a c)] ->
                 [(Term_Rewriting.Term a b, Term_Rewriting.Term a c)] ->
                   [((a, Arith.Nat), [Arith.Nat])] ->
                     [(d, Term_Rewriting.Term a e)] -> Bool;
muterm_innermost_ur_closed_check r u mu p =
  all (Arith.membera r) u &&
    all (\ dp ->
          Term_Rewriting.is_Var (snd dp) ||
            CSR_Minimal_CSDP_Proofs.csr_rta08_active_root_rules_check r u mu
              (snd dp))
      p &&
      all (\ lr ->
            CSR_Minimal_CSDP_Proofs.csr_rta08_active_root_rules_check r u mu
              (snd lr))
        u;

}
