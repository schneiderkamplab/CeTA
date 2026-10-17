{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  CSR_Standalone_DP_Checker(check_standalone_improved_csr_dp,
                             check_standalone_muterm_typed_dp)
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
import qualified CSR_Innermost_Unhiding_Proofs;
import qualified CSR_Muterm_Typed_Checker;
import qualified CSR_Innermost_Switch;
import qualified CSR_Muterm_Usable_Rules;
import qualified CSR_Checker_Base;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Dependency_Pair_Problem_Spec;
import qualified CSR_Guarded_List_Checker;
import qualified Termination_Problem_Spec;
import qualified Labelings;
import qualified Sum_Type;
import qualified Compare;
import qualified Countable;
import qualified Term_Rewriting;
import qualified Arith;

check_standalone_minimal_csr_dp ::
  forall a b c.
    (Compare.Compare_order b, Countable.Countable b, Eq b,
      Term_Rewriting.Showl b) => Termination_Problem_Spec.Tp_ops_ext a
                                   (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                   () ->
                                   Dependency_Pair_Problem_Spec.Dpp_ops_ext c
                                     (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                     () ->
                                     (String -> String) ->
                                       Bool ->
 Labelings.Lab b [Arith.Nat] ->
   [((Labelings.Lab b [Arith.Nat], Arith.Nat), [Arith.Nat])] ->
     [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
        Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
       [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
          Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
         CSR_Guarded_List_Checker.Guarded_csr_dp_proof b [Arith.Nat]
           [Arith.Char] ->
           Sum_Type.Sum (String -> String) ();
check_standalone_minimal_csr_dp ia j i m u mu p r prf =
  Error_Monad.bind
    (Check_Monad.check m
      (Term_Rewriting.showsl_lit
        "standalone improved CSR-DPs require CSR minimality"))
    (\ _ ->
      Error_Monad.bind (Term_Rewriting.check_wf_trs r)
        (\ _ ->
          Error_Monad.bind
            (Error_Monad.catch_error
              (Error_Monad.forallM
                (\ (f, _) ->
                  Check_Monad.check
                    (not (CSR_Checker_Base.is_sharp_lab f) &&
                      not (Labelings.equal_lab f u))
                    (Term_Rewriting.showsl_lit
                      "standalone CSR rules define a marked or unhiding symbol"))
                (Term_Rewriting.defined_list r))
              (\ x -> Sum_Type.Inl (snd x)))
            (\ _ ->
              Error_Monad.bind
                (Check_Monad.check (not (CSR_Checker_Base.is_sharp_lab u))
                  (Term_Rewriting.showsl_lit
                    "unhiding symbol must not be sharp"))
                (\ _ ->
                  CSR_Guarded_List_Checker.check_guarded_improved_csr_dp_proof
                    ia j u mu i
                    (Dependency_Pair_Problem_Spec.mk j False False p [] [] [] r)
                    prf))));

check_standalone_nonminimal_csr_dp ::
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
   [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
      Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
     CSR_Guarded_List_Checker.Guarded_csr_dp_proof b [Arith.Nat] [Arith.Char] ->
       Sum_Type.Sum (String -> String) ();
check_standalone_nonminimal_csr_dp ia j i mu p r prf =
  (case prf of {
    CSR_Guarded_List_Checker.Guarded_CSR_DP_Existing a ->
      CSR_Checker.check_csr_dp_termination_proof_core ia j mu False i
        (Dependency_Pair_Problem_Spec.mk j False False p [] [] [] r) a;
    CSR_Guarded_List_Checker.Guarded_CSR_DP_Dep_Graph _ ->
      Sum_Type.Inl
        (Term_Rewriting.showsl_lit "this CSR processor requires minimality");
    CSR_Guarded_List_Checker.Guarded_CSR_DP_OvCons _ ->
      Sum_Type.Inl
        (Term_Rewriting.showsl_lit "this CSR processor requires minimality");
  });

check_standalone_improved_csr_dp ::
  forall a b c.
    (Compare.Compare_order b, Countable.Countable b, Eq b,
      Term_Rewriting.Showl b) => Termination_Problem_Spec.Tp_ops_ext a
                                   (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                   () ->
                                   Dependency_Pair_Problem_Spec.Dpp_ops_ext c
                                     (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                     () ->
                                     (String -> String) ->
                                       Bool ->
 Labelings.Lab b [Arith.Nat] ->
   [((Labelings.Lab b [Arith.Nat], Arith.Nat), [Arith.Nat])] ->
     [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
        Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
       [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
          Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
         CSR_Guarded_List_Checker.Guarded_csr_dp_proof b [Arith.Nat]
           [Arith.Char] ->
           Sum_Type.Sum (String -> String) ();
check_standalone_improved_csr_dp ia j i m u mu p r prf =
  (if m then check_standalone_minimal_csr_dp ia j i m u mu p r prf
    else check_standalone_nonminimal_csr_dp ia j i mu p r prf);

check_standalone_muterm_typed_dp ::
  forall a b c.
    (Compare.Compare_order b, Countable.Countable b, Eq b,
      Term_Rewriting.Showl b) => Termination_Problem_Spec.Tp_ops_ext a
                                   (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                   () ->
                                   Dependency_Pair_Problem_Spec.Dpp_ops_ext c
                                     (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                     () ->
                                     (String -> String) ->
                                       Bool ->
 [((Labelings.Lab b [Arith.Nat], Arith.Nat), [Arith.Nat])] ->
   [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
      Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
     [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
        Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
       [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
          Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
         CSR_Muterm_Usable_Rules.Muterm_typed_dp_proof b [Arith.Nat]
           [Arith.Char] ->
           Sum_Type.Sum (String -> String) ();
check_standalone_muterm_typed_dp ia j i m mu p r b prf =
  Error_Monad.bind
    (Check_Monad.check m
      (Term_Rewriting.showsl_lit
        "typed MU-TERM input requires its minimal-chain invariant"))
    (\ _ ->
      Error_Monad.bind (Term_Rewriting.check_wf_trs r)
        (\ _ ->
          Error_Monad.bind (CSR_Innermost_Switch.check_csr_orthogonal r)
            (\ _ ->
              Error_Monad.bind
                (Check_Monad.check
                  (all (\ (f, _) -> not (CSR_Checker_Base.is_sharp_lab f))
                    (Term_Rewriting.funas_trs_list r))
                  (Term_Rewriting.showsl_lit
                    "typed MU-TERM source signature contains marked symbols"))
                (\ _ ->
                  Error_Monad.bind
                    (Check_Monad.check
                      (Arith.set_eq (Arith.set b)
                        (Arith.set
                          (CSR_Innermost_Unhiding_Proofs.muterm_exact_unhiding_rules_list
                            Labelings.Sharp mu (Term_Rewriting.defined_list r)
                            r)))
                      (Term_Rewriting.showsl_lit
                        "standalone typed MU-TERM unhiding rules are not exact"))
                    (\ _ ->
                      Error_Monad.bind
                        (Check_Monad.check
                          (CSR_Muterm_Usable_Rules.muterm_marked_mu_equal_check
                            mu)
                          (Term_Rewriting.showsl_lit
                            "typed MU-TERM marked replacement map differs from source"))
                        (\ _ ->
                          CSR_Muterm_Typed_Checker.check_muterm_i4_root_proof ia
                            j mu i r b p prf))))));

}
