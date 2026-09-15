{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  CSR_Guarded_List_Checker(Csr_guarded_ovcons_witness(..),
                            Guarded_csr_dp_proof(..),
                            Guarded_csr_termination_proof(..),
                            check_guarded_improved_csr_dp_proof,
                            check_guarded_csr_termination_proof)
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
import qualified CSR_Conservative_Checker;
import qualified CSR_Improved_CSDP_Proofs;
import qualified Mapping;
import qualified CSR_Guarded_List_Generic_Checker;
import qualified CSR_Guarded_List_Measure;
import qualified Context_Sensitive_Impl;
import qualified Check_Monad;
import qualified Phantom_Type;
import qualified CSR_Minimal_CSDP_Proofs;
import qualified CSR_Checker;
import qualified FOR_Preliminaries;
import qualified Error_Monad;
import qualified Dependency_Pair_Problem_Spec;
import qualified Termination_Problem_Spec;
import qualified Sum_Type;
import qualified Compare;
import qualified Countable;
import qualified Compare_Order_Instances;
import qualified Arith;
import qualified Reduction_Pair_Implementations;
import qualified CSR_Checker_Base;
import qualified Labelings;
import qualified Term_Rewriting;

data Csr_guarded_ovcons_witness a b =
  CSR_Guarded_OvCons_Witness a a a a a a a a a a a a a a a b b b b b b b b;

data Guarded_csr_dp_proof a b c =
  Guarded_CSR_DP_Existing (CSR_Checker_Base.Csr_dp_termination_proof a b c)
  | Guarded_CSR_DP_Dep_Graph
      [(Maybe (Guarded_csr_dp_proof a b c),
         [(Term_Rewriting.Term (Labelings.Lab a b) c,
            Term_Rewriting.Term (Labelings.Lab a b) c)])]
  | Guarded_CSR_DP_OvCons (Csr_guarded_ovcons_witness (Labelings.Lab a b) c);

data Guarded_csr_termination_proof a b c =
  Guarded_CSR_Rule_Removal
    (Reduction_Pair_Implementations.Redtriple_impl (Labelings.Lab a b))
    [(Term_Rewriting.Term (Labelings.Lab a b) c,
       Term_Rewriting.Term (Labelings.Lab a b) c)]
    (Guarded_csr_termination_proof a b c)
  | Guarded_CSR_Dependency_Pairs
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Guarded_csr_dp_proof a b c)
  | Guarded_CSR_Improved_Dependency_Pairs (Labelings.Lab a b)
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Guarded_csr_dp_proof a b c);

check_csr_guarded_ovcons_terminal ::
  forall a b.
    (Compare.Compare_order b, Eq b,
      Term_Rewriting.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a
                                   (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                   () ->
                                   [((Labelings.Lab b [Arith.Nat], Arith.Nat),
                                      [Arith.Nat])] ->
                                     a -> Csr_guarded_ovcons_witness
    (Labelings.Lab b [Arith.Nat]) [Arith.Char] ->
    Sum_Type.Sum (String -> String) ();
check_csr_guarded_ovcons_terminal j mu dpp
  (CSR_Guarded_OvCons_Witness tt a natp listp ilistp u11 u21 u31 z su len ni co
    ta zs x l il m n v v1 v2)
  = FOR_Preliminaries.debug id "guarded-list CSR component"
      (Error_Monad.bind
        (Check_Monad.check (CSR_Checker_Base.plain_csr_dpp j dpp)
          (Term_Rewriting.showsl_lit
            "guarded component is not a plain CSR-DP problem"))
        (\ _ ->
          Error_Monad.bind
            (Check_Monad.check
              (Arith.distinct
                [tt, a, natp, listp, ilistp, u11, u21, u31, z, su, len, ni, co,
                  ta, zs])
              (Term_Rewriting.showsl_lit
                "guarded component symbols are not distinct"))
            (\ _ ->
              Error_Monad.bind
                (Check_Monad.check
                  (not (Arith.membera [a, u11, u21, u31]
                         (Labelings.Sharp u11)) &&
                    not (Arith.membera [a, u11, u21, u31]
                          (Labelings.Sharp len)) &&
                      not (Labelings.equal_lab (Labelings.Sharp u11)
                            (Labelings.Sharp len)))
                  (Term_Rewriting.showsl_lit
                    "guarded component marked symbols are not fresh"))
                (\ _ ->
                  Error_Monad.bind
                    (Check_Monad.check
                      (CSR_Guarded_List_Generic_Checker.csr_guard_rules_check tt
                        a natp listp ilistp u11 u21 u31 z su len ni co ta zs
                        (Dependency_Pair_Problem_Spec.rules j dpp))
                      (Term_Rewriting.showsl_lit
                        "guarded residual violates semantic-rank obligations"))
                    (\ _ ->
                      Error_Monad.bind
                        (Check_Monad.check
                          (Arith.set_eq
                            (Arith.set
                              (Dependency_Pair_Problem_Spec.pairs j dpp))
                            (Arith.insert
                              (CSR_Guarded_List_Measure.csr_guard_strict_pair
                                (Labelings.Sharp len) co (Labelings.Sharp u11) a
                                listp natp n l)
                              (Arith.insert
                                (CSR_Guarded_List_Measure.csr_guard_weak_pair
                                  (Labelings.Sharp u11) tt (Labelings.Sharp len)
                                  l)
                                (Arith.set_empty
                                  (Phantom_Type.of_phantom
                                    (Arith.set_impl_prod ::
                                      Phantom_Type.Phantom
(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
  Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])
Arith.Set_impla))))))
                          (Term_Rewriting.showsl_lit
                            "guarded component does not contain the exact two pairs"))
                        (\ _ ->
                          Error_Monad.bind
                            (Term_Rewriting.check_wf_trs
                              (Dependency_Pair_Problem_Spec.rules j dpp))
                            (\ _ ->
                              Error_Monad.bind
                                (Check_Monad.check
                                  (all (\ aa ->
 (case aa of {
   (Labelings.Lab _ _, _) -> True;
   (Labelings.FunLab _ _, _) -> True;
   (Labelings.UnLab _, _) -> True;
   (Labelings.Sharp _, _) -> False;
 }))
                                    (Term_Rewriting.defined_list
                                      (Dependency_Pair_Problem_Spec.rules j
dpp)))
                                  (Term_Rewriting.showsl_lit
                                    "guarded residual defines a reserved marked symbol"))
                                (\ _ ->
                                  Error_Monad.bind
                                    (Check_Monad.check
                                      (not
(Arith.member Arith.one_nat
  (Context_Sensitive_Impl.mu_of mu (u11, Arith.nat_of_integer (2 :: Integer)))))
                                      (Term_Rewriting.showsl_lit
"guarded continuation tail is not frozen"))
                                    (\ _ ->
                                      Check_Monad.check
(Arith.less_eq_set
   (Context_Sensitive_Impl.mu_of mu (a, Arith.nat_of_integer (2 :: Integer)))
   (Arith.insert Arith.zero_nat
     (Arith.set_empty (Phantom_Type.of_phantom Arith.set_impl_nat))) &&
  Arith.set_eq (Context_Sensitive_Impl.mu_of mu (natp, Arith.one_nat))
    (Arith.set_empty (Phantom_Type.of_phantom Arith.set_impl_nat)) &&
    Arith.set_eq (Context_Sensitive_Impl.mu_of mu (listp, Arith.one_nat))
      (Arith.set_empty (Phantom_Type.of_phantom Arith.set_impl_nat)) &&
      Arith.set_eq (Context_Sensitive_Impl.mu_of mu (ilistp, Arith.one_nat))
        (Arith.set_empty (Phantom_Type.of_phantom Arith.set_impl_nat)))
(Term_Rewriting.showsl_lit
  "guard recognizer replacement map is invalid"))))))))));

check_guarded_csr_dp_proof ::
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
 c -> Guarded_csr_dp_proof b [Arith.Nat] [Arith.Char] ->
        Sum_Type.Sum (String -> String) ();
check_guarded_csr_dp_proof ia j mu i dpp (Guarded_CSR_DP_Existing prf) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu False i dpp
    prf;
check_guarded_csr_dp_proof ia j mu i dpp (Guarded_CSR_DP_Dep_Graph edpts) =
  FOR_Preliminaries.debug i "guarded CSR-DP dependency graph"
    (Error_Monad.bind (CSR_Checker.check_csr_dep_graph_proc j mu dpp edpts)
      (\ _ -> check_guarded_csr_dp_components ia j mu i dpp edpts));
check_guarded_csr_dp_proof ia j mu i dpp (Guarded_CSR_DP_OvCons witness) =
  check_csr_guarded_ovcons_terminal j mu dpp witness;

check_guarded_csr_dp_components ::
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
 c -> [(Maybe (Guarded_csr_dp_proof b [Arith.Nat] [Arith.Char]),
         [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
            Term_Rewriting.Term (Labelings.Lab b [Arith.Nat])
              [Arith.Char])])] ->
        Sum_Type.Sum (String -> String) ();
check_guarded_csr_dp_components ia j mu i dpp [] = Sum_Type.Inr ();
check_guarded_csr_dp_components ia j mu i dpp ((Nothing, p) : rest) =
  check_guarded_csr_dp_components ia j mu
    (Term_Rewriting.add_index i Arith.one_nat) dpp rest;
check_guarded_csr_dp_components ia j mu i dpp ((Just prf, p) : rest) =
  Error_Monad.bind
    (check_guarded_csr_dp_proof ia j mu
      (Term_Rewriting.add_index i Arith.one_nat)
      (Dependency_Pair_Problem_Spec.intersect_pairs j dpp p) prf)
    (\ _ ->
      check_guarded_csr_dp_components ia j mu
        (Term_Rewriting.add_index i Arith.one_nat) dpp rest);

check_guarded_improved_csr_dp_proof ::
  forall a b c.
    (Compare.Compare_order b, Countable.Countable b, Eq b,
      Term_Rewriting.Showl b) => Termination_Problem_Spec.Tp_ops_ext a
                                   (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                   () ->
                                   Dependency_Pair_Problem_Spec.Dpp_ops_ext c
                                     (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                     () ->
                                     Labelings.Lab b [Arith.Nat] ->
                                       [((Labelings.Lab b [Arith.Nat],
   Arith.Nat),
  [Arith.Nat])] ->
 (String -> String) ->
   c -> Guarded_csr_dp_proof b [Arith.Nat] [Arith.Char] ->
          Sum_Type.Sum (String -> String) ();
check_guarded_improved_csr_dp_proof ia j u mu i dpp
  (Guarded_CSR_DP_Existing prf) =
  CSR_Conservative_Checker.check_improved_csr_dp_termination_proof ia j u mu
    False i dpp prf;
check_guarded_improved_csr_dp_proof ia j u mu i dpp
  (Guarded_CSR_DP_Dep_Graph edpts) =
  FOR_Preliminaries.debug i "guarded improved CSR-DP dependency graph"
    (Error_Monad.bind (CSR_Checker.check_csr_dep_graph_proc j mu dpp edpts)
      (\ _ -> check_guarded_improved_csr_dp_components ia j u mu i dpp edpts));
check_guarded_improved_csr_dp_proof ia j u mu i dpp
  (Guarded_CSR_DP_OvCons witness) =
  check_csr_guarded_ovcons_terminal j mu dpp witness;

check_guarded_improved_csr_dp_components ::
  forall a b c.
    (Compare.Compare_order b, Countable.Countable b, Eq b,
      Term_Rewriting.Showl b) => Termination_Problem_Spec.Tp_ops_ext a
                                   (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                   () ->
                                   Dependency_Pair_Problem_Spec.Dpp_ops_ext c
                                     (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                     () ->
                                     Labelings.Lab b [Arith.Nat] ->
                                       [((Labelings.Lab b [Arith.Nat],
   Arith.Nat),
  [Arith.Nat])] ->
 (String -> String) ->
   c -> [(Maybe (Guarded_csr_dp_proof b [Arith.Nat] [Arith.Char]),
           [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
              Term_Rewriting.Term (Labelings.Lab b [Arith.Nat])
                [Arith.Char])])] ->
          Sum_Type.Sum (String -> String) ();
check_guarded_improved_csr_dp_components ia j u mu i dpp [] = Sum_Type.Inr ();
check_guarded_improved_csr_dp_components ia j u mu i dpp ((Nothing, p) : rest) =
  check_guarded_improved_csr_dp_components ia j u mu
    (Term_Rewriting.add_index i Arith.one_nat) dpp rest;
check_guarded_improved_csr_dp_components ia j u mu i dpp ((Just prf, p) : rest)
  = Error_Monad.bind
      (check_guarded_improved_csr_dp_proof ia j u mu
        (Term_Rewriting.add_index i Arith.one_nat)
        (Dependency_Pair_Problem_Spec.intersect_pairs j dpp p) prf)
      (\ _ ->
        check_guarded_improved_csr_dp_components ia j u mu
          (Term_Rewriting.add_index i Arith.one_nat) dpp rest);

check_guarded_csr_termination_proof ::
  forall a b c.
    (Compare.Compare_order b, Countable.Countable b, Eq b,
      Term_Rewriting.Showl b) => Termination_Problem_Spec.Tp_ops_ext a
                                   (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                   () ->
                                   Dependency_Pair_Problem_Spec.Dpp_ops_ext c
                                     (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                     () ->
                                     (String -> String) ->
                                       [((Labelings.Lab b [Arith.Nat],
   Arith.Nat),
  [Arith.Nat])] ->
 [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
    Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
   Guarded_csr_termination_proof b [Arith.Nat] [Arith.Char] ->
     Sum_Type.Sum (String -> String) ();
check_guarded_csr_termination_proof ia j i mu r
  (Guarded_CSR_Rule_Removal redp rr prf) =
  FOR_Preliminaries.debug i "guarded CSR rule removal"
    (case CSR_Checker_Base.csr_rule_removal_impl redp mu rr r of {
      Sum_Type.Inl a -> Sum_Type.Inl a;
      Sum_Type.Inr r2 ->
        check_guarded_csr_termination_proof ia j
          (Term_Rewriting.add_index i Arith.one_nat) mu r2 prf;
    });
check_guarded_csr_termination_proof ia j i mu r
  (Guarded_CSR_Dependency_Pairs p prf) =
  FOR_Preliminaries.debug i "guarded CSR dependency pairs"
    (Error_Monad.bind (CSR_Checker_Base.csr_sharp_mu_check mu)
      (\ _ ->
        Error_Monad.bind
          (Check_Monad.check
            (all (\ a -> (case a of {
                           (Labelings.Lab _ _, _) -> True;
                           (Labelings.FunLab _ _, _) -> True;
                           (Labelings.UnLab _, _) -> True;
                           (Labelings.Sharp _, _) -> False;
                         }))
              (Term_Rewriting.defined_list r))
            (Term_Rewriting.showsl_lit
              "guarded CSR source defines a reserved marked symbol"))
          (\ _ ->
            Error_Monad.bind
              (CSR_Checker_Base.mu_csr_dependency_pairs_tt Labelings.Sharp j mu
                r p)
              (\ dpp ->
                check_guarded_csr_dp_proof ia j mu
                  (Term_Rewriting.add_index i Arith.one_nat) dpp prf))));
check_guarded_csr_termination_proof ia j i mu r
  (Guarded_CSR_Improved_Dependency_Pairs u p prf) =
  FOR_Preliminaries.debug i "guarded improved CSR dependency pairs"
    (Error_Monad.bind
      (CSR_Improved_CSDP_Proofs.improved_csr_dependency_pairs_tt j u mu r p)
      (\ dpp ->
        check_guarded_improved_csr_dp_proof ia j u mu
          (Term_Rewriting.add_index i Arith.one_nat) dpp prf));

}
