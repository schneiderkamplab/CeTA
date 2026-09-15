{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Proof_Checker(Proof(..), Cert_result(..), certify_cert_problem) where {

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
import qualified CSR_Standalone_DP_Checker;
import qualified IA_Instance;
import qualified CSR_Check_Loops;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified AC_Dependency_Pair_Problem_Spec;
import qualified AC_Termination_Problem_Spec;
import qualified Monadic_Rewriting_Impl;
import qualified Dependency_Pair_Problem_Spec;
import qualified Nontermination_Impl;
import qualified Termination_Problem_Spec;
import qualified Not_WN_Tree_Automaton_Impl;
import qualified Nonloop_SRS;
import qualified Uncurry_Impl;
import qualified Critical_Pairs_Impl;
import qualified Nonloop_Impl;
import qualified Loops_Impl;
import qualified Ceta_Problem_Spec;
import qualified Phantom_Type;
import qualified Sum_Type;
import qualified Countable;
import qualified HOL;
import qualified Compare;
import qualified Check_Termination_Common;
import qualified Mapping;
import qualified Compare_Order_Instances;
import qualified List_Lexorder;
import qualified Lists_are_Infinite;
import qualified GM04_Complete_Checker;
import qualified CSR_GM_Transformation;
import qualified Outermost_RZ_Checker;
import qualified Ordered_Completion_Impl;
import qualified Reduction_Pair_Implementations;
import qualified CSR_Guarded_List_Checker;
import qualified Check_Quasi_Reductive;
import qualified Check_Conditional_CRP;
import qualified Check_AC_Termination;
import qualified LTS_Termination_Prover;
import qualified Check_Equational_Proof;
import qualified Check_Completion_Proof;
import qualified Check_Nontermination;
import qualified Check_Infeasibility;
import qualified Check_Complexity;
import qualified Term_Rewriting;
import qualified Check_Termination;
import qualified Tree_Automata_Impl;
import qualified LTS_Safety_Prover;
import qualified IA_Checker;
import qualified Check_CRP;
import qualified Labelings;
import qualified Arith;

data Proof a b c =
  TRS_Termination_Proof (Check_Termination.Trs_termination_proof a b c)
  | Complexity_Proof (Check_Complexity.Complexity_proof a b c)
  | DP_Termination_Proof (Check_Termination.Dp_termination_proof a b c)
  | Relative_DP_Termination_Proof (Check_Termination.Dp_termination_proof a b c)
  | DP_Nontermination_Proof (Check_Nontermination.Dp_nontermination_proof a b c)
  | TRS_Nontermination_Proof
      (Check_Nontermination.Trs_nontermination_proof a b c)
  | FP_Termination_Proof (Check_Termination.Fptrs_termination_proof a b c)
  | Outermost_RZ_Termination_Proof
      (Outermost_RZ_Checker.Outermost_rz_termination_proof a b c)
  | CSR_Termination_Proof
      (CSR_GM_Transformation.Gm_extended_csr_termination_proof a b c)
  | CSR_Improved_DP_Proof (CSR_Guarded_List_Checker.Guarded_csr_dp_proof a b c)
  | GM04_Complete_TRS_Proof
      (GM04_Complete_Checker.Gm04_complete_transformation_proof a b c)
  | GM04_Complete_TRS_Nontermination_Proof
      (GM04_Complete_Checker.Gm04_complete_nontermination_proof a b c)
  | FP_Nontermination_Proof
      (Check_Nontermination.Fp_trs_nontermination_proof a b c)
  | Relative_TRS_Nontermination_Proof
      (Check_Nontermination.Reltrs_nontermination_proof a b c)
  | TRS_Confluence_Proof (Check_CRP.Cr_proof a b c)
  | TRS_Non_Confluence_Proof (Check_CRP.Ncr_proof a b c c)
  | TRS_Non_Commutation_Proof (Check_CRP.Ncomm_proof a b c c)
  | TRS_Commutation_Proof (Check_CRP.Comm_proof a b c)
  | Completion_Proof (Check_Completion_Proof.Completion_proof a b c)
  | Ordered_Completion_Proof
      (Ordered_Completion_Impl.Ordered_completion_proof (Labelings.Lab a b) c)
  | Equational_Proof (Check_Equational_Proof.Equational_proof a b c)
  | Equational_Disproof (Check_Equational_Proof.Equational_disproof a b c)
  | Quasi_Reductive_Proof (Check_Quasi_Reductive.Quasi_reductive_proof a b c)
  | Conditional_CR_Proof
      (Check_Conditional_CRP.Conditional_cr_proof a b c
        (Reduction_Pair_Implementations.Redtriple_impl (Labelings.Lab a b)))
  | Conditional_Non_CR_Proof
      (Check_Conditional_CRP.Conditional_ncr_proof a b c c
        (Reduction_Pair_Implementations.Redtriple_impl (Labelings.Lab a b)))
  | Tree_Automata_Closed_Proof (Tree_Automata_Impl.Ta_relation [Arith.Char])
  | AC_Termination_Proof (Check_AC_Termination.Ac_termination_proof a b c)
  | LTS_Termination_Proof
      (LTS_Termination_Prover.Termination_proof Term_Rewriting.Sig c
        Term_Rewriting.Ty [Arith.Char] [Arith.Char] IA_Checker.La_solver_type)
  | LTS_Safety_Proof
      (LTS_Safety_Prover.Safety_proof Term_Rewriting.Sig c Term_Rewriting.Ty
        [Arith.Char] [Arith.Char] [Arith.Char] IA_Checker.La_solver_type)
  | Infeasibility_Proof
      (Check_Infeasibility.Infeasibility_proof a c
        (Reduction_Pair_Implementations.Redtriple_impl (Labelings.Lab a b)) b)
  | Feasibility_Proof
      (Check_Infeasibility.Feasibility_proof (Labelings.Lab a b) c)
  | Unknown_Proof (Check_Termination.Unknown_proof a b c)
  | Unknown_Disproof (Check_Nontermination.Neg_unknown_proof a b c);

data Cert_result = Certified | Unsupported String | Error String;

proof_to_string :: forall a b c. Proof a b c -> String;
proof_to_string proof =
  (case proof of {
    TRS_Termination_Proof _ -> "TRS termination proof";
    Complexity_Proof _ -> "complexity proof";
    DP_Termination_Proof _ -> "DP termination proof";
    Relative_DP_Termination_Proof _ -> "relative DP termination proof";
    DP_Nontermination_Proof _ -> "DP nontermination proof";
    TRS_Nontermination_Proof _ -> "TRS nontermination proof";
    FP_Termination_Proof _ -> "FP TRS termination proof";
    Outermost_RZ_Termination_Proof _ ->
      "Raffelsieper-Zantema outermost termination proof";
    CSR_Termination_Proof _ -> "CSR termination proof";
    CSR_Improved_DP_Proof _ -> "standalone improved CSR-DP proof";
    GM04_Complete_TRS_Proof _ -> "complete GM04 inverse-transformation proof";
    GM04_Complete_TRS_Nontermination_Proof _ ->
      "complete GM04 nontermination-transformation proof";
    FP_Nontermination_Proof _ -> "FP TRS nontermination proof";
    Relative_TRS_Nontermination_Proof _ -> "relative TRS nontermination proof";
    TRS_Confluence_Proof _ -> "TRS confluence proof";
    TRS_Non_Confluence_Proof _ -> "TRS nonconfluence proof";
    TRS_Non_Commutation_Proof _ -> "TRS noncommutation proof";
    TRS_Commutation_Proof _ -> "TRS commutation proof";
    Completion_Proof _ -> "completion proof";
    Ordered_Completion_Proof _ -> "ordered completion proof";
    Equational_Proof _ -> "equational proof";
    Equational_Disproof _ -> "equational disproof";
    Quasi_Reductive_Proof _ -> "quasi-reductive proof";
    Conditional_CR_Proof _ -> "conditional confluence proof";
    Conditional_Non_CR_Proof _ -> "conditional nonconfluence proof";
    Tree_Automata_Closed_Proof _ -> "tree automata closed proof";
    AC_Termination_Proof _ -> "AC termination proof";
    LTS_Termination_Proof _ -> "LTS termination proof";
    LTS_Safety_Proof _ -> "LTS safety proof";
    Infeasibility_Proof _ -> "Infeasibility proof";
    Feasibility_Proof _ -> "Feasibility proof";
    Unknown_Proof _ -> "unknown proof";
    Unknown_Disproof _ -> "unknown disproof";
  });

check_cert ::
  forall a b c d e f.
    (Compare.Compare_order b, Countable.Countable b, HOL.Default b, Eq b,
      Term_Rewriting.Showl b) => Termination_Problem_Spec.Tp_ops_ext a
                                   (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                   () ->
                                   Dependency_Pair_Problem_Spec.Dpp_ops_ext c
                                     (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                     () ->
                                     AC_Termination_Problem_Spec.Ac_tp_ops_ext d
                                       (Labelings.Lab b [Arith.Nat])
                                       [Arith.Char] () ->
                                       AC_Dependency_Pair_Problem_Spec.Ac_dpp_ops_ext
 e (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
 Bool ->
   Ceta_Problem_Spec.Input (Labelings.Lab b [Arith.Nat]) [Arith.Char] ->
     Ceta_Problem_Spec.Property (Labelings.Lab b [Arith.Nat]) f ->
       Ceta_Problem_Spec.Answer (Labelings.Lab b [Arith.Nat]) [Arith.Char] ->
         Proof b [Arith.Nat] [Arith.Char] -> Sum_Type.Sum (String -> String) ();
check_cert i j k l a input property answer proof =
  let {
    mismatch =
      Term_Rewriting.showsl_lit
        (((((((("\nthe combination of input <" ++
                 Ceta_Problem_Spec.input_to_string input) ++
                "> and property <") ++
               Ceta_Problem_Spec.property_to_string property) ++
              "> and answer <") ++
             Ceta_Problem_Spec.answer_to_string answer) ++
            "> and proof <") ++
           proof_to_string proof) ++
          "> is not supported by CeTA\n");
    triple = (input, (property, answer));
  } in (case proof of {
         TRS_Termination_Proof prf ->
           (case triple of {
             (Ceta_Problem_Spec.DP_input _ _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input q r s,
               (Ceta_Problem_Spec.Termination, Ceta_Problem_Spec.Decision True))
               -> Check_Termination.check_trs_termination_proof i j a
                    (Term_Rewriting.showsl_lit "1")
                    (Termination_Problem_Spec.mk i
                      (Ceta_Problem_Spec.strategy_to_nfs q)
                      (Ceta_Problem_Spec.strategy_to_Q q r) r s)
                    prf;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Decision False))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Upperbound_Poly _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Completed_System _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Order_Completed_System _ _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Confluence, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Safety, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _, _) -> Sum_Type.Inl mismatch;
           });
         Complexity_Proof prf ->
           (case triple of {
             (Ceta_Problem_Spec.DP_input _ _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Termination, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Confluence, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Safety, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Complexity _, Ceta_Problem_Spec.Decision _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input q r s,
               (Ceta_Problem_Spec.Complexity cm,
                 Ceta_Problem_Spec.Upperbound_Poly n))
               -> Check_Complexity.check_complexity_proof i a
                    (Term_Rewriting.showsl_lit "1")
                    (Termination_Problem_Spec.mk i
                       (Ceta_Problem_Spec.strategy_to_nfs q)
                       (Ceta_Problem_Spec.strategy_to_Q q (r ++ s)) r s,
                      (Ceta_Problem_Spec.complexity_measure_of r s cm,
                        Term_Rewriting.Comp_Poly n))
                    prf;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Complexity _,
                 Ceta_Problem_Spec.Completed_System _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Complexity _,
                 Ceta_Problem_Spec.Order_Completed_System _ _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _, _) -> Sum_Type.Inl mismatch;
           });
         DP_Termination_Proof prf ->
           (case triple of {
             (Ceta_Problem_Spec.DP_input m p q r,
               (Ceta_Problem_Spec.Termination, Ceta_Problem_Spec.Decision True))
               -> Check_Termination.check_dp_termination_proof i j a
                    (Term_Rewriting.showsl_lit "1")
                    (Dependency_Pair_Problem_Spec.mk j
                      (Ceta_Problem_Spec.strategy_to_nfs q) m p []
                      (Ceta_Problem_Spec.strategy_to_Q q r) [] r)
                    prf;
             (Ceta_Problem_Spec.DP_input _ _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Decision False))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.DP_input _ _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Upperbound_Poly _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.DP_input _ _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Completed_System _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.DP_input _ _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Order_Completed_System _ _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.DP_input _ _ _ _,
               (Ceta_Problem_Spec.Confluence, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.DP_input _ _ _ _,
               (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.DP_input _ _ _ _,
               (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.DP_input _ _ _ _, (Ceta_Problem_Spec.Safety, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.DP_input _ _ _ _,
               (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.DP_input _ _ _ _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.DP_input _ _ _ _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.DP_input _ _ _ _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.DP_input _ _ _ _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _, _) -> Sum_Type.Inl mismatch;
           });
         Relative_DP_Termination_Proof prf ->
           (case triple of {
             (Ceta_Problem_Spec.DP_input _ _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input nfs m p pw q r rw,
               (Ceta_Problem_Spec.Termination, Ceta_Problem_Spec.Decision True))
               -> Check_Termination.check_dp_termination_proof i j False
                    (Term_Rewriting.showsl_lit "1")
                    (Dependency_Pair_Problem_Spec.mk j nfs m p pw q r rw) prf;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Decision False))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Upperbound_Poly _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Completed_System _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Order_Completed_System _ _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _,
               (Ceta_Problem_Spec.Confluence, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _,
               (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _,
               (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _,
               (Ceta_Problem_Spec.Safety, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _,
               (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _, _) -> Sum_Type.Inl mismatch;
           });
         DP_Nontermination_Proof prf ->
           (case triple of {
             (Ceta_Problem_Spec.DP_input _ _ _ _,
               (Ceta_Problem_Spec.Termination, Ceta_Problem_Spec.Decision True))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.DP_input m p q r,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Decision False))
               -> Check_Nontermination.check_dp_nontermination_proof i j a
                    (Term_Rewriting.showsl_lit "1")
                    (Dependency_Pair_Problem_Spec.mk j
                      (Ceta_Problem_Spec.strategy_to_nfs q) m p []
                      (Ceta_Problem_Spec.strategy_to_Q q r) [] r)
                    prf;
             (Ceta_Problem_Spec.DP_input _ _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Upperbound_Poly _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.DP_input _ _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Completed_System _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.DP_input _ _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Order_Completed_System _ _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.DP_input _ _ _ _,
               (Ceta_Problem_Spec.Confluence, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.DP_input _ _ _ _,
               (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.DP_input _ _ _ _,
               (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.DP_input _ _ _ _, (Ceta_Problem_Spec.Safety, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.DP_input _ _ _ _,
               (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.DP_input _ _ _ _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.DP_input _ _ _ _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.DP_input _ _ _ _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.DP_input _ _ _ _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _, _) -> Sum_Type.Inl mismatch;
           });
         TRS_Nontermination_Proof prf ->
           (case triple of {
             (Ceta_Problem_Spec.DP_input _ _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Termination, Ceta_Problem_Spec.Decision True))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input q r s,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Decision False))
               -> Error_Monad.bind (Check_Monad.check (null s) mismatch)
                    (\ _ ->
                      Check_Nontermination.check_trs_nontermination_proof i j a
                        (Term_Rewriting.showsl_lit "1")
                        (Termination_Problem_Spec.mk i
                          (Ceta_Problem_Spec.strategy_to_nfs q)
                          (Ceta_Problem_Spec.strategy_to_Q q r) r [])
                        prf);
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Upperbound_Poly _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Completed_System _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Order_Completed_System _ _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Confluence, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Safety, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Termination, Ceta_Problem_Spec.Decision True))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost r,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Decision False))
               -> Error_Monad.bind
                    (Check_Nontermination.trs_nontermination_proof_to_fp prf)
                    (Check_Nontermination.check_fp_nontermination_proof i j
                      False (Term_Rewriting.showsl_lit "1")
                      (Ceta_Problem_Spec.fp_strategy_to_fp_impl
                         Ceta_Problem_Spec.Outermost r,
                        r));
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Upperbound_Poly _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Completed_System _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Order_Completed_System _ _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Confluence, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Safety, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Context_Sensitive _) _,
               (Ceta_Problem_Spec.Termination, Ceta_Problem_Spec.Decision True))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Context_Sensitive mu) r,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Decision False))
               -> (case prf of {
                    Check_Nontermination.TRS_Loop aa ->
                      CSR_Check_Loops.check_csr_loop mu r aa;
                    Check_Nontermination.TRS_Not_Well_Formed ->
                      Sum_Type.Inl mismatch;
                    Check_Nontermination.TRS_Rule_Removal _ _ ->
                      Sum_Type.Inl mismatch;
                    Check_Nontermination.TRS_String_Reversal _ ->
                      Sum_Type.Inl mismatch;
                    Check_Nontermination.TRS_Constant_String _ _ ->
                      Sum_Type.Inl mismatch;
                    Check_Nontermination.TRS_DP_Trans _ _ ->
                      Sum_Type.Inl mismatch;
                    Check_Nontermination.TRS_Termination_Switch _ _ ->
                      Sum_Type.Inl mismatch;
                    Check_Nontermination.TRS_Nonloop _ -> Sum_Type.Inl mismatch;
                    Check_Nontermination.TRS_Nonloop_SRS _ ->
                      Sum_Type.Inl mismatch;
                    Check_Nontermination.TRS_Q_Increase _ _ ->
                      Sum_Type.Inl mismatch;
                    Check_Nontermination.TRS_Uncurry _ _ ->
                      Sum_Type.Inl mismatch;
                    Check_Nontermination.TRS_Not_WN_Tree_Automaton _ ->
                      Sum_Type.Inl mismatch;
                    Check_Nontermination.TRS_Not_RG_Decision ->
                      Sum_Type.Inl mismatch;
                    Check_Nontermination.TRS_Assume_Not_SN _ _ ->
                      Sum_Type.Inl mismatch;
                  });
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Context_Sensitive _) _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Upperbound_Poly _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Context_Sensitive _) _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Completed_System _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Context_Sensitive _) _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Order_Completed_System _ _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Context_Sensitive _) _,
               (Ceta_Problem_Spec.Confluence, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Context_Sensitive _) _,
               (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Context_Sensitive _) _,
               (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Context_Sensitive _) _,
               (Ceta_Problem_Spec.Safety, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Context_Sensitive _) _,
               (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Context_Sensitive _) _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Context_Sensitive _) _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Context_Sensitive _) _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Context_Sensitive _) _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Forbidden_Patterns _) _,
               (Ceta_Problem_Spec.Termination, Ceta_Problem_Spec.Decision True))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Forbidden_Patterns p) r,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Decision False))
               -> Error_Monad.bind
                    (Check_Nontermination.trs_nontermination_proof_to_fp prf)
                    (Check_Nontermination.check_fp_nontermination_proof i j
                      False (Term_Rewriting.showsl_lit "1")
                      (Ceta_Problem_Spec.fp_strategy_to_fp_impl
                         (Ceta_Problem_Spec.Forbidden_Patterns p) r,
                        r));
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Forbidden_Patterns _) _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Upperbound_Poly _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Forbidden_Patterns _) _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Completed_System _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Forbidden_Patterns _) _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Order_Completed_System _ _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Forbidden_Patterns _) _,
               (Ceta_Problem_Spec.Confluence, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Forbidden_Patterns _) _,
               (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Forbidden_Patterns _) _,
               (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Forbidden_Patterns _) _,
               (Ceta_Problem_Spec.Safety, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Forbidden_Patterns _) _,
               (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Forbidden_Patterns _) _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Forbidden_Patterns _) _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Forbidden_Patterns _) _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Forbidden_Patterns _) _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _, _) -> Sum_Type.Inl mismatch;
           });
         FP_Termination_Proof prf ->
           (case triple of {
             (Ceta_Problem_Spec.DP_input _ _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input strat r,
               (Ceta_Problem_Spec.Termination, Ceta_Problem_Spec.Decision True))
               -> Check_Termination.check_fptrs_termination_proof i j a
                    (Term_Rewriting.showsl_lit "1")
                    (Ceta_Problem_Spec.fp_strategy_to_fp_impl strat r, r) prf;
             (Ceta_Problem_Spec.FP_TRS_input _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Decision False))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Upperbound_Poly _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Completed_System _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Order_Completed_System _ _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _,
               (Ceta_Problem_Spec.Confluence, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _,
               (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _,
               (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _, (Ceta_Problem_Spec.Safety, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _,
               (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _, _) -> Sum_Type.Inl mismatch;
           });
         Outermost_RZ_Termination_Proof prf ->
           (case triple of {
             (Ceta_Problem_Spec.DP_input _ _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost r,
               (Ceta_Problem_Spec.Termination, Ceta_Problem_Spec.Decision True))
               -> Outermost_RZ_Checker.check_outermost_rz_termination_proof i j
                    (Term_Rewriting.showsl_lit "1") r prf;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Decision False))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Upperbound_Poly _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Completed_System _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Order_Completed_System _ _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Confluence, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Safety, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Context_Sensitive _) _,
               _)
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Forbidden_Patterns _) _,
               _)
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _, _) -> Sum_Type.Inl mismatch;
           });
         CSR_Termination_Proof prf ->
           (case triple of {
             (Ceta_Problem_Spec.DP_input _ _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _, _)
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Context_Sensitive mu) r,
               (Ceta_Problem_Spec.Termination, Ceta_Problem_Spec.Decision True))
               -> CSR_GM_Transformation.check_gm_extended_csr_termination_proof
                    i j a (Term_Rewriting.showsl_lit "1") mu r prf;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Context_Sensitive _) _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Decision False))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Context_Sensitive _) _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Upperbound_Poly _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Context_Sensitive _) _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Completed_System _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Context_Sensitive _) _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Order_Completed_System _ _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Context_Sensitive _) _,
               (Ceta_Problem_Spec.Confluence, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Context_Sensitive _) _,
               (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Context_Sensitive _) _,
               (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Context_Sensitive _) _,
               (Ceta_Problem_Spec.Safety, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Context_Sensitive _) _,
               (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Context_Sensitive _) _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Context_Sensitive _) _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Context_Sensitive _) _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Context_Sensitive _) _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Forbidden_Patterns _) _,
               _)
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _, _) -> Sum_Type.Inl mismatch;
           });
         CSR_Improved_DP_Proof prf ->
           (case triple of {
             (Ceta_Problem_Spec.DP_input _ _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input m u mu p r,
               (Ceta_Problem_Spec.Termination, Ceta_Problem_Spec.Decision True))
               -> CSR_Standalone_DP_Checker.check_standalone_improved_csr_dp i j
                    (Term_Rewriting.showsl_lit "1") m u mu p r prf;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Decision False))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Upperbound_Poly _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Completed_System _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Order_Completed_System _ _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _,
               (Ceta_Problem_Spec.Confluence, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _,
               (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _,
               (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _,
               (Ceta_Problem_Spec.Safety, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _,
               (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _, _) -> Sum_Type.Inl mismatch;
           });
         GM04_Complete_TRS_Proof prf ->
           (case triple of {
             (Ceta_Problem_Spec.DP_input _ _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input q r s,
               (Ceta_Problem_Spec.Termination, Ceta_Problem_Spec.Decision True))
               -> GM04_Complete_Checker.check_gm04_complete_transformation_proof
                    i j (Term_Rewriting.showsl_lit "1")
                    (Ceta_Problem_Spec.strategy_to_nfs q)
                    (Ceta_Problem_Spec.strategy_to_Q q r) r s prf;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Decision False))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Upperbound_Poly _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Completed_System _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Order_Completed_System _ _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Confluence, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Safety, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _, _) -> Sum_Type.Inl mismatch;
           });
         GM04_Complete_TRS_Nontermination_Proof prf ->
           (case triple of {
             (Ceta_Problem_Spec.DP_input _ _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Termination, Ceta_Problem_Spec.Decision True))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input q r s,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Decision False))
               -> GM04_Complete_Checker.check_gm04_complete_nontermination_proof
                    (Term_Rewriting.showsl_lit "1")
                    (Ceta_Problem_Spec.strategy_to_nfs q)
                    (Ceta_Problem_Spec.strategy_to_Q q r) r s prf;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Upperbound_Poly _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Completed_System _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Order_Completed_System _ _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Confluence, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Safety, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _, _) -> Sum_Type.Inl mismatch;
           });
         FP_Nontermination_Proof prf ->
           (case triple of {
             (Ceta_Problem_Spec.DP_input _ _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Termination, Ceta_Problem_Spec.Decision True))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost r,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Decision False))
               -> Check_Nontermination.check_fp_nontermination_proof i j a
                    (Term_Rewriting.showsl_lit "1")
                    (Ceta_Problem_Spec.fp_strategy_to_fp_impl
                       Ceta_Problem_Spec.Outermost r,
                      r)
                    prf;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Upperbound_Poly _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Completed_System _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Order_Completed_System _ _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Confluence, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Safety, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Context_Sensitive _) _,
               _)
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Forbidden_Patterns _) _,
               (Ceta_Problem_Spec.Termination, Ceta_Problem_Spec.Decision True))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Forbidden_Patterns p) r,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Decision False))
               -> Check_Nontermination.check_fp_nontermination_proof i j a
                    (Term_Rewriting.showsl_lit "1")
                    (Ceta_Problem_Spec.fp_strategy_to_fp_impl
                       (Ceta_Problem_Spec.Forbidden_Patterns p) r,
                      r)
                    prf;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Forbidden_Patterns _) _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Upperbound_Poly _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Forbidden_Patterns _) _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Completed_System _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Forbidden_Patterns _) _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Order_Completed_System _ _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Forbidden_Patterns _) _,
               (Ceta_Problem_Spec.Confluence, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Forbidden_Patterns _) _,
               (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Forbidden_Patterns _) _,
               (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Forbidden_Patterns _) _,
               (Ceta_Problem_Spec.Safety, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Forbidden_Patterns _) _,
               (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Forbidden_Patterns _) _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Forbidden_Patterns _) _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Forbidden_Patterns _) _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input
                (Ceta_Problem_Spec.Forbidden_Patterns _) _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _, _) -> Sum_Type.Inl mismatch;
           });
         Relative_TRS_Nontermination_Proof prf ->
           (case triple of {
             (Ceta_Problem_Spec.DP_input _ _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Termination, Ceta_Problem_Spec.Decision True))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input q r s,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Decision False))
               -> Check_Nontermination.check_reltrs_nontermination_proof i j a
                    (Term_Rewriting.showsl_lit "1")
                    (Termination_Problem_Spec.mk i
                      (Ceta_Problem_Spec.strategy_to_nfs q)
                      (Ceta_Problem_Spec.strategy_to_Q q r) r s)
                    prf;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Upperbound_Poly _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Completed_System _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Order_Completed_System _ _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Confluence, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Safety, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _, _) -> Sum_Type.Inl mismatch;
           });
         TRS_Confluence_Proof prf ->
           (case triple of {
             (Ceta_Problem_Spec.DP_input _ _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _,
               (Ceta_Problem_Spec.Termination, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ r,
               (Ceta_Problem_Spec.Confluence, Ceta_Problem_Spec.Decision True))
               -> Check_CRP.check_cr_proof a (Term_Rewriting.showsl_lit "1") i j
                    r prf;
             (Ceta_Problem_Spec.Single_TRS_input _ _,
               (Ceta_Problem_Spec.Confluence, Ceta_Problem_Spec.Decision False))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _,
               (Ceta_Problem_Spec.Confluence,
                 Ceta_Problem_Spec.Upperbound_Poly _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _,
               (Ceta_Problem_Spec.Confluence,
                 Ceta_Problem_Spec.Completed_System _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _,
               (Ceta_Problem_Spec.Confluence,
                 Ceta_Problem_Spec.Order_Completed_System _ _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _,
               (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _,
               (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _,
               (Ceta_Problem_Spec.Safety, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _,
               (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _, _) -> Sum_Type.Inl mismatch;
           });
         TRS_Non_Confluence_Proof prf ->
           (case triple of {
             (Ceta_Problem_Spec.DP_input _ _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _,
               (Ceta_Problem_Spec.Termination, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _,
               (Ceta_Problem_Spec.Confluence, Ceta_Problem_Spec.Decision True))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ r,
               (Ceta_Problem_Spec.Confluence, Ceta_Problem_Spec.Decision False))
               -> Check_CRP.check_ncr_proof a (Term_Rewriting.showsl_lit "1") i
                    j r prf;
             (Ceta_Problem_Spec.Single_TRS_input _ _,
               (Ceta_Problem_Spec.Confluence,
                 Ceta_Problem_Spec.Upperbound_Poly _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _,
               (Ceta_Problem_Spec.Confluence,
                 Ceta_Problem_Spec.Completed_System _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _,
               (Ceta_Problem_Spec.Confluence,
                 Ceta_Problem_Spec.Order_Completed_System _ _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _,
               (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _,
               (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _,
               (Ceta_Problem_Spec.Safety, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _,
               (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _, _) -> Sum_Type.Inl mismatch;
           });
         TRS_Non_Commutation_Proof prf ->
           (case triple of {
             (Ceta_Problem_Spec.DP_input _ _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _,
               (Ceta_Problem_Spec.Termination, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _,
               (Ceta_Problem_Spec.Confluence, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _,
               (Ceta_Problem_Spec.Commutation, Ceta_Problem_Spec.Decision True))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input f r s,
               (Ceta_Problem_Spec.Commutation,
                 Ceta_Problem_Spec.Decision False))
               -> Check_CRP.check_ncomm_proof (Term_Rewriting.showsl_lit "1") f
                    r s prf;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _,
               (Ceta_Problem_Spec.Commutation,
                 Ceta_Problem_Spec.Upperbound_Poly _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _,
               (Ceta_Problem_Spec.Commutation,
                 Ceta_Problem_Spec.Completed_System _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _,
               (Ceta_Problem_Spec.Commutation,
                 Ceta_Problem_Spec.Order_Completed_System _ _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _,
               (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _,
               (Ceta_Problem_Spec.Safety, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _,
               (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _, _) -> Sum_Type.Inl mismatch;
           });
         TRS_Commutation_Proof prf ->
           (case triple of {
             (Ceta_Problem_Spec.DP_input _ _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _,
               (Ceta_Problem_Spec.Termination, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _,
               (Ceta_Problem_Spec.Confluence, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ r s,
               (Ceta_Problem_Spec.Commutation, Ceta_Problem_Spec.Decision True))
               -> Check_CRP.check_comm_proof i j a
                    (Term_Rewriting.showsl_lit "1") r s prf;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _,
               (Ceta_Problem_Spec.Commutation,
                 Ceta_Problem_Spec.Decision False))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _,
               (Ceta_Problem_Spec.Commutation,
                 Ceta_Problem_Spec.Upperbound_Poly _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _,
               (Ceta_Problem_Spec.Commutation,
                 Ceta_Problem_Spec.Completed_System _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _,
               (Ceta_Problem_Spec.Commutation,
                 Ceta_Problem_Spec.Order_Completed_System _ _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _,
               (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _,
               (Ceta_Problem_Spec.Safety, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _,
               (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _, _) -> Sum_Type.Inl mismatch;
           });
         Completion_Proof prf ->
           (case triple of {
             (Ceta_Problem_Spec.DP_input _ _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, (Ceta_Problem_Spec.Termination, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, (Ceta_Problem_Spec.Confluence, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _,
               (Ceta_Problem_Spec.Completion, Ceta_Problem_Spec.Decision _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _,
               (Ceta_Problem_Spec.Completion,
                 Ceta_Problem_Spec.Upperbound_Poly _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input e,
               (Ceta_Problem_Spec.Completion,
                 Ceta_Problem_Spec.Completed_System r))
               -> Check_Completion_Proof.check_completion_proof a
                    (Term_Rewriting.showsl_lit "1") i j e r prf;
             (Ceta_Problem_Spec.EQ_input _,
               (Ceta_Problem_Spec.Completion,
                 Ceta_Problem_Spec.Order_Completed_System _ _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, (Ceta_Problem_Spec.Safety, _)) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _, _) -> Sum_Type.Inl mismatch;
           });
         Ordered_Completion_Proof prf ->
           (case triple of {
             (Ceta_Problem_Spec.DP_input _ _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _,
               (Ceta_Problem_Spec.Termination, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _,
               (Ceta_Problem_Spec.Confluence, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _,
               (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _,
               (Ceta_Problem_Spec.Completion, Ceta_Problem_Spec.Decision _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _,
               (Ceta_Problem_Spec.Completion,
                 Ceta_Problem_Spec.Upperbound_Poly _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _,
               (Ceta_Problem_Spec.Completion,
                 Ceta_Problem_Spec.Completed_System _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input e_0 ord,
               (Ceta_Problem_Spec.Completion,
                 Ceta_Problem_Spec.Order_Completed_System e r))
               -> Ordered_Completion_Impl.check_ordered_completion_proof_ext
                    (Term_Rewriting.showsl_lit "1") e_0 e r ord prf;
             (Ceta_Problem_Spec.EQ_RO_input _ _, (Ceta_Problem_Spec.Safety, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _,
               (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _, _) -> Sum_Type.Inl mismatch;
           });
         Equational_Proof prf ->
           (case triple of {
             (Ceta_Problem_Spec.DP_input _ _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _,
               (Ceta_Problem_Spec.Termination, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _,
               (Ceta_Problem_Spec.Confluence, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _,
               (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _,
               (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _,
               (Ceta_Problem_Spec.Safety, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input e eq,
               (Ceta_Problem_Spec.Entailment, Ceta_Problem_Spec.Decision True))
               -> Check_Equational_Proof.check_equational_proof a
                    (Term_Rewriting.showsl_lit "1") i j e eq prf;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _,
               (Ceta_Problem_Spec.Entailment, Ceta_Problem_Spec.Decision False))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _,
               (Ceta_Problem_Spec.Entailment,
                 Ceta_Problem_Spec.Upperbound_Poly _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _,
               (Ceta_Problem_Spec.Entailment,
                 Ceta_Problem_Spec.Completed_System _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _,
               (Ceta_Problem_Spec.Entailment,
                 Ceta_Problem_Spec.Order_Completed_System _ _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _, _) -> Sum_Type.Inl mismatch;
           });
         Equational_Disproof prf ->
           (case triple of {
             (Ceta_Problem_Spec.DP_input _ _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _,
               (Ceta_Problem_Spec.Termination, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _,
               (Ceta_Problem_Spec.Confluence, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _,
               (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _,
               (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _,
               (Ceta_Problem_Spec.Safety, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _,
               (Ceta_Problem_Spec.Entailment, Ceta_Problem_Spec.Decision True))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input e eq,
               (Ceta_Problem_Spec.Entailment, Ceta_Problem_Spec.Decision False))
               -> Check_Equational_Proof.check_equational_disproof a
                    (Term_Rewriting.showsl_lit "1") i j e eq prf;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _,
               (Ceta_Problem_Spec.Entailment,
                 Ceta_Problem_Spec.Upperbound_Poly _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _,
               (Ceta_Problem_Spec.Entailment,
                 Ceta_Problem_Spec.Completed_System _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _,
               (Ceta_Problem_Spec.Entailment,
                 Ceta_Problem_Spec.Order_Completed_System _ _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _, _) -> Sum_Type.Inl mismatch;
           });
         Quasi_Reductive_Proof prf ->
           (case triple of {
             (Ceta_Problem_Spec.DP_input _ _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input r,
               (Ceta_Problem_Spec.Termination, Ceta_Problem_Spec.Decision True))
               -> Check_Quasi_Reductive.check_quasi_reductive_proof a
                    (Term_Rewriting.showsl_lit "1") i j r prf;
             (Ceta_Problem_Spec.CTRS_input _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Decision False))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Upperbound_Poly _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Completed_System _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Order_Completed_System _ _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, (Ceta_Problem_Spec.Confluence, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _,
               (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, (Ceta_Problem_Spec.Safety, _)) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _, _) -> Sum_Type.Inl mismatch;
           });
         Conditional_CR_Proof prf ->
           (case triple of {
             (Ceta_Problem_Spec.DP_input _ _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _,
               (Ceta_Problem_Spec.Termination, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input r,
               (Ceta_Problem_Spec.Confluence, Ceta_Problem_Spec.Decision True))
               -> Check_Conditional_CRP.check_conditional_cr_proof a
                    (Term_Rewriting.showsl_lit "1") i j r prf;
             (Ceta_Problem_Spec.CTRS_input _,
               (Ceta_Problem_Spec.Confluence, Ceta_Problem_Spec.Decision False))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _,
               (Ceta_Problem_Spec.Confluence,
                 Ceta_Problem_Spec.Upperbound_Poly _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _,
               (Ceta_Problem_Spec.Confluence,
                 Ceta_Problem_Spec.Completed_System _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _,
               (Ceta_Problem_Spec.Confluence,
                 Ceta_Problem_Spec.Order_Completed_System _ _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _,
               (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, (Ceta_Problem_Spec.Safety, _)) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _, _) -> Sum_Type.Inl mismatch;
           });
         Conditional_Non_CR_Proof prf ->
           (case triple of {
             (Ceta_Problem_Spec.DP_input _ _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _,
               (Ceta_Problem_Spec.Termination, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _,
               (Ceta_Problem_Spec.Confluence, Ceta_Problem_Spec.Decision True))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input r,
               (Ceta_Problem_Spec.Confluence, Ceta_Problem_Spec.Decision False))
               -> Check_Conditional_CRP.check_conditional_ncr_proof a
                    (Term_Rewriting.showsl_lit "1") i j r prf;
             (Ceta_Problem_Spec.CTRS_input _,
               (Ceta_Problem_Spec.Confluence,
                 Ceta_Problem_Spec.Upperbound_Poly _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _,
               (Ceta_Problem_Spec.Confluence,
                 Ceta_Problem_Spec.Completed_System _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _,
               (Ceta_Problem_Spec.Confluence,
                 Ceta_Problem_Spec.Order_Completed_System _ _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _,
               (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, (Ceta_Problem_Spec.Safety, _)) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _, _) -> Sum_Type.Inl mismatch;
           });
         Tree_Automata_Closed_Proof prf ->
           (case triple of {
             (Ceta_Problem_Spec.DP_input _ _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _,
               (Ceta_Problem_Spec.Termination, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, (Ceta_Problem_Spec.Confluence, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _,
               (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, (Ceta_Problem_Spec.Safety, _)) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input ta r,
               (Ceta_Problem_Spec.Closed_Under_Rewriting,
                 Ceta_Problem_Spec.Decision True))
               -> Tree_Automata_Impl.tree_aut_trs_closed ta prf r;
             (Ceta_Problem_Spec.TA_input _ _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting,
                 Ceta_Problem_Spec.Decision False))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting,
                 Ceta_Problem_Spec.Upperbound_Poly _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting,
                 Ceta_Problem_Spec.Completed_System _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting,
                 Ceta_Problem_Spec.Order_Completed_System _ _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _, _) -> Sum_Type.Inl mismatch;
           });
         AC_Termination_Proof prf ->
           (case triple of {
             (Ceta_Problem_Spec.DP_input _ _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input r aa c,
               (Ceta_Problem_Spec.Termination, Ceta_Problem_Spec.Decision True))
               -> Check_AC_Termination.check_ac_termination_proof l k
                    (Term_Rewriting.showsl_lit "1")
                    (AC_Termination_Problem_Spec.mk k r aa c) prf;
             (Ceta_Problem_Spec.AC_input _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Decision False))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Upperbound_Poly _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Completed_System _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Order_Completed_System _ _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _,
               (Ceta_Problem_Spec.Confluence, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _,
               (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _,
               (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _, (Ceta_Problem_Spec.Safety, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _,
               (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _, _) -> Sum_Type.Inl mismatch;
           });
         LTS_Termination_Proof prf ->
           (case triple of {
             (Ceta_Problem_Spec.DP_input _ _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input r,
               (Ceta_Problem_Spec.Termination, Ceta_Problem_Spec.Decision True))
               -> IA_Instance.check_termination r prf;
             (Ceta_Problem_Spec.LTS_input _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Decision False))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Upperbound_Poly _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Completed_System _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _,
               (Ceta_Problem_Spec.Termination,
                 Ceta_Problem_Spec.Order_Completed_System _ _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, (Ceta_Problem_Spec.Confluence, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, (Ceta_Problem_Spec.Safety, _)) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _, _) -> Sum_Type.Inl mismatch;
           });
         LTS_Safety_Proof prf ->
           (case triple of {
             (Ceta_Problem_Spec.DP_input _ _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _,
               (Ceta_Problem_Spec.Termination, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _,
               (Ceta_Problem_Spec.Confluence, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _,
               (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _,
               (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input r e,
               (Ceta_Problem_Spec.Safety, Ceta_Problem_Spec.Decision True))
               -> LTS_Safety_Prover.check_safety Term_Rewriting.type_of_fun
                    (Arith.insert Term_Rewriting.BoolT
                      (Arith.set_empty
                        (Phantom_Type.of_phantom Term_Rewriting.set_impl_ty)))
                    IA_Checker.check_clause IA_Checker.check_clause
                    Term_Rewriting.showsl_IA_exp Term_Rewriting.showsl_IA_exp
                    IA_Checker.lit_normalize IA_Checker.lit_normalize r e prf;
             (Ceta_Problem_Spec.LTS_safety_input _ _,
               (Ceta_Problem_Spec.Safety, Ceta_Problem_Spec.Decision False))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _,
               (Ceta_Problem_Spec.Safety, Ceta_Problem_Spec.Upperbound_Poly _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _,
               (Ceta_Problem_Spec.Safety, Ceta_Problem_Spec.Completed_System _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _,
               (Ceta_Problem_Spec.Safety,
                 Ceta_Problem_Spec.Order_Completed_System _ _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _,
               (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _, _) -> Sum_Type.Inl mismatch;
           });
         Infeasibility_Proof prf ->
           (case triple of {
             (Ceta_Problem_Spec.DP_input _ _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _,
               (Ceta_Problem_Spec.Termination, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _,
               (Ceta_Problem_Spec.Confluence, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _,
               (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _,
               (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _,
               (Ceta_Problem_Spec.Safety, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _,
               (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input r cs,
               (Ceta_Problem_Spec.Infeasibility,
                 Ceta_Problem_Spec.Decision True))
               -> Check_Infeasibility.check_infeasible a
                    (Term_Rewriting.showsl_lit "1") i j r cs prf;
             (Ceta_Problem_Spec.Infeasibility_input _ _,
               (Ceta_Problem_Spec.Infeasibility,
                 Ceta_Problem_Spec.Decision False))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _,
               (Ceta_Problem_Spec.Infeasibility,
                 Ceta_Problem_Spec.Upperbound_Poly _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _,
               (Ceta_Problem_Spec.Infeasibility,
                 Ceta_Problem_Spec.Completed_System _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _,
               (Ceta_Problem_Spec.Infeasibility,
                 Ceta_Problem_Spec.Order_Completed_System _ _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _, _) -> Sum_Type.Inl mismatch;
           });
         Feasibility_Proof prf ->
           (case triple of {
             (Ceta_Problem_Spec.DP_input _ _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _,
               (Ceta_Problem_Spec.Termination, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _,
               (Ceta_Problem_Spec.Confluence, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _,
               (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _,
               (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _,
               (Ceta_Problem_Spec.Safety, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _,
               (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _,
               (Ceta_Problem_Spec.Infeasibility,
                 Ceta_Problem_Spec.Decision True))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input r cs,
               (Ceta_Problem_Spec.Infeasibility,
                 Ceta_Problem_Spec.Decision False))
               -> Check_Infeasibility.check_feasibility_proof r cs prf;
             (Ceta_Problem_Spec.Infeasibility_input _ _,
               (Ceta_Problem_Spec.Infeasibility,
                 Ceta_Problem_Spec.Upperbound_Poly _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _,
               (Ceta_Problem_Spec.Infeasibility,
                 Ceta_Problem_Spec.Completed_System _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _,
               (Ceta_Problem_Spec.Infeasibility,
                 Ceta_Problem_Spec.Order_Completed_System _ _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _, _) -> Sum_Type.Inl mismatch;
           });
         Unknown_Proof prf ->
           (case triple of {
             (Ceta_Problem_Spec.DP_input _ _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _,
               (Ceta_Problem_Spec.Termination, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _,
               (Ceta_Problem_Spec.Confluence, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _,
               (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _,
               (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _, (Ceta_Problem_Spec.Safety, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _,
               (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input ur,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Check_Termination.check_unknown_proof i j a
                    (Term_Rewriting.showsl_lit "1") ur prf;
           });
         Unknown_Disproof prf ->
           (case triple of {
             (Ceta_Problem_Spec.DP_input _ _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Relative_DP_input _ _ _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CSR_Improved_DP_input _ _ _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Inn_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.FP_TRS_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.AC_input _ _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.LTS_safety_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.CTRS_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_input _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_RO_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.EQ_reasoning_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.TA_input _ _, _) -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Infeasibility_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Single_TRS_input _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Two_TRS_input _ _ _, _) ->
               Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _,
               (Ceta_Problem_Spec.Termination, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _,
               (Ceta_Problem_Spec.Confluence, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _,
               (Ceta_Problem_Spec.Commutation, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _,
               (Ceta_Problem_Spec.Completion, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _, (Ceta_Problem_Spec.Safety, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _,
               (Ceta_Problem_Spec.Entailment, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _,
               (Ceta_Problem_Spec.Complexity _, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _,
               (Ceta_Problem_Spec.Closed_Under_Rewriting, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input _,
               (Ceta_Problem_Spec.Infeasibility, _))
               -> Sum_Type.Inl mismatch;
             (Ceta_Problem_Spec.Unknown_input ur,
               (Ceta_Problem_Spec.Unknown_Property, _))
               -> Check_Nontermination.check_unknown_disproof i j a
                    (Term_Rewriting.showsl_lit "1") ur prf;
           });
       });

certify_cert_problem ::
  forall a b c d e f.
    (Compare.Compare_order b, Countable.Countable b, HOL.Default b, Eq b,
      Term_Rewriting.Showl b) => Termination_Problem_Spec.Tp_ops_ext a
                                   (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                   () ->
                                   Dependency_Pair_Problem_Spec.Dpp_ops_ext c
                                     (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                     () ->
                                     AC_Termination_Problem_Spec.Ac_tp_ops_ext d
                                       (Labelings.Lab b [Arith.Nat])
                                       [Arith.Char] () ->
                                       AC_Dependency_Pair_Problem_Spec.Ac_dpp_ops_ext
 e (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
 Bool ->
   Ceta_Problem_Spec.Input (Labelings.Lab b [Arith.Nat]) [Arith.Char] ->
     Ceta_Problem_Spec.Property (Labelings.Lab b [Arith.Nat]) f ->
       Ceta_Problem_Spec.Answer (Labelings.Lab b [Arith.Nat]) [Arith.Char] ->
         Proof b [Arith.Nat] [Arith.Char] -> Cert_result;
certify_cert_problem i j k l a input property answer proof =
  (case check_cert i j k l a input property answer proof of {
    Sum_Type.Inl err -> Error (err "");
    Sum_Type.Inr _ -> Certified;
  });

}
