{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module RFC_Absolute_Cert(certify_proof_rfc_absolute) where {

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
import qualified AC_Termination_Problem_Impl;
import qualified CPF_Parser;
import qualified Ceta;
import qualified AC_Dependency_Pair_Problem_Impl;
import qualified Dependency_Pair_Problem_Impl;
import qualified Termination_Problem_Impl;
import qualified Strict_Sum;
import qualified Mapping;
import qualified Compare_Order_Instances;
import qualified Check_Termination_Common;
import qualified RFC_Absolute_Check;
import qualified AC_Dependency_Pair_Problem_Spec;
import qualified GM04_Complete_Checker;
import qualified CSR_GM_Transformation;
import qualified Outermost_RZ_Checker;
import qualified GM04_Standalone_DP_Checker;
import qualified AC_Termination_Problem_Spec;
import qualified Dependency_Pair_Problem_Spec;
import qualified Reduction_Pair_Implementations;
import qualified Ordered_Completion_Impl;
import qualified CSR_Muterm_Usable_Rules;
import qualified CSR_Guarded_List_Checker;
import qualified Check_Quasi_Reductive;
import qualified Termination_Problem_Spec;
import qualified Check_Conditional_CRP;
import qualified Check_AC_Termination;
import qualified LTS_Termination_Prover;
import qualified Check_Equational_Proof;
import qualified Check_Completion_Proof;
import qualified Check_Nontermination;
import qualified Check_Infeasibility;
import qualified Check_Complexity;
import qualified Check_Termination;
import qualified Tree_Automata_Impl;
import qualified LTS_Safety_Prover;
import qualified IA_Checker;
import qualified Ceta_Problem_Spec;
import qualified Proof_Checker;
import qualified Check_CRP;
import qualified Sum_Type;
import qualified Compare;
import qualified Term_Rewriting;
import qualified Countable;
import qualified HOL;
import qualified Labelings;
import qualified Arith;

check_cert_rfc_absolute ::
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
 Ceta_Problem_Spec.Input (Labelings.Lab b [Arith.Nat]) [Arith.Char] ->
   Ceta_Problem_Spec.Property (Labelings.Lab b [Arith.Nat]) f ->
     Ceta_Problem_Spec.Answer (Labelings.Lab b [Arith.Nat]) [Arith.Char] ->
       Proof_Checker.Proof b [Arith.Nat] [Arith.Char] ->
         Sum_Type.Sum (String -> String) ();
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.Inn_TRS_input q r s)
  Ceta_Problem_Spec.Termination (Ceta_Problem_Spec.Decision True)
  (Proof_Checker.TRS_Termination_Proof p) =
  RFC_Absolute_Check.check_rfc_absolute i j (Term_Rewriting.showsl_lit "1")
    (Termination_Problem_Spec.mk i (Ceta_Problem_Spec.strategy_to_nfs q)
      (Ceta_Problem_Spec.strategy_to_Q q r) r s)
    p;
check_cert_rfc_absolute i j k l
  (Ceta_Problem_Spec.FP_TRS_input Ceta_Problem_Spec.Outermost r)
  Ceta_Problem_Spec.Termination (Ceta_Problem_Spec.Decision True)
  (Proof_Checker.TRS_Termination_Proof p) =
  RFC_Absolute_Check.check_rfc_absolute i j (Term_Rewriting.showsl_lit "1")
    (Termination_Problem_Spec.mk i False [] r []) p;
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.DP_input v va vb vc) prop ans
  p = Proof_Checker.check_cert i j k l False
        (Ceta_Problem_Spec.DP_input v va vb vc) prop ans p;
check_cert_rfc_absolute i j k l
  (Ceta_Problem_Spec.Relative_DP_input v va vb vc vd ve vf) prop ans p =
  Proof_Checker.check_cert i j k l False
    (Ceta_Problem_Spec.Relative_DP_input v va vb vc vd ve vf) prop ans p;
check_cert_rfc_absolute i j k l
  (Ceta_Problem_Spec.CSR_Improved_DP_input v va vb vc vd) prop ans p =
  Proof_Checker.check_cert i j k l False
    (Ceta_Problem_Spec.CSR_Improved_DP_input v va vb vc vd) prop ans p;
check_cert_rfc_absolute i j k l
  (Ceta_Problem_Spec.CSR_Muterm_Typed_DP_input v va vb vc vd) prop ans p =
  Proof_Checker.check_cert i j k l False
    (Ceta_Problem_Spec.CSR_Muterm_Typed_DP_input v va vb vc vd) prop ans p;
check_cert_rfc_absolute i j k l
  (Ceta_Problem_Spec.FP_TRS_input (Ceta_Problem_Spec.Context_Sensitive vb) va)
  prop ans p =
  Proof_Checker.check_cert i j k l False
    (Ceta_Problem_Spec.FP_TRS_input (Ceta_Problem_Spec.Context_Sensitive vb) va)
    prop ans p;
check_cert_rfc_absolute i j k l
  (Ceta_Problem_Spec.FP_TRS_input (Ceta_Problem_Spec.Forbidden_Patterns vb) va)
  prop ans p =
  Proof_Checker.check_cert i j k l False
    (Ceta_Problem_Spec.FP_TRS_input (Ceta_Problem_Spec.Forbidden_Patterns vb)
      va)
    prop ans p;
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va)
  Ceta_Problem_Spec.Confluence ans p =
  (Proof_Checker.check_cert ::
    Termination_Problem_Spec.Tp_ops_ext a (Labelings.Lab b [Arith.Nat])
      [Arith.Char] () ->
      Dependency_Pair_Problem_Spec.Dpp_ops_ext c (Labelings.Lab b [Arith.Nat])
        [Arith.Char] () ->
        AC_Termination_Problem_Spec.Ac_tp_ops_ext d
          (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
          AC_Dependency_Pair_Problem_Spec.Ac_dpp_ops_ext e
            (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
            Bool ->
              Ceta_Problem_Spec.Input (Labelings.Lab b [Arith.Nat])
                [Arith.Char] ->
                Ceta_Problem_Spec.Property (Labelings.Lab b [Arith.Nat]) f ->
                  Ceta_Problem_Spec.Answer (Labelings.Lab b [Arith.Nat])
                    [Arith.Char] ->
                    Proof_Checker.Proof b [Arith.Nat] [Arith.Char] ->
                      Sum_Type.Sum (String -> String) ())
    i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    Ceta_Problem_Spec.Confluence ans p;
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va)
  Ceta_Problem_Spec.Commutation ans p =
  (Proof_Checker.check_cert ::
    Termination_Problem_Spec.Tp_ops_ext a (Labelings.Lab b [Arith.Nat])
      [Arith.Char] () ->
      Dependency_Pair_Problem_Spec.Dpp_ops_ext c (Labelings.Lab b [Arith.Nat])
        [Arith.Char] () ->
        AC_Termination_Problem_Spec.Ac_tp_ops_ext d
          (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
          AC_Dependency_Pair_Problem_Spec.Ac_dpp_ops_ext e
            (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
            Bool ->
              Ceta_Problem_Spec.Input (Labelings.Lab b [Arith.Nat])
                [Arith.Char] ->
                Ceta_Problem_Spec.Property (Labelings.Lab b [Arith.Nat]) f ->
                  Ceta_Problem_Spec.Answer (Labelings.Lab b [Arith.Nat])
                    [Arith.Char] ->
                    Proof_Checker.Proof b [Arith.Nat] [Arith.Char] ->
                      Sum_Type.Sum (String -> String) ())
    i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    Ceta_Problem_Spec.Commutation ans p;
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va)
  Ceta_Problem_Spec.Completion ans p =
  (Proof_Checker.check_cert ::
    Termination_Problem_Spec.Tp_ops_ext a (Labelings.Lab b [Arith.Nat])
      [Arith.Char] () ->
      Dependency_Pair_Problem_Spec.Dpp_ops_ext c (Labelings.Lab b [Arith.Nat])
        [Arith.Char] () ->
        AC_Termination_Problem_Spec.Ac_tp_ops_ext d
          (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
          AC_Dependency_Pair_Problem_Spec.Ac_dpp_ops_ext e
            (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
            Bool ->
              Ceta_Problem_Spec.Input (Labelings.Lab b [Arith.Nat])
                [Arith.Char] ->
                Ceta_Problem_Spec.Property (Labelings.Lab b [Arith.Nat]) f ->
                  Ceta_Problem_Spec.Answer (Labelings.Lab b [Arith.Nat])
                    [Arith.Char] ->
                    Proof_Checker.Proof b [Arith.Nat] [Arith.Char] ->
                      Sum_Type.Sum (String -> String) ())
    i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    Ceta_Problem_Spec.Completion ans p;
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va)
  Ceta_Problem_Spec.Safety ans p =
  (Proof_Checker.check_cert ::
    Termination_Problem_Spec.Tp_ops_ext a (Labelings.Lab b [Arith.Nat])
      [Arith.Char] () ->
      Dependency_Pair_Problem_Spec.Dpp_ops_ext c (Labelings.Lab b [Arith.Nat])
        [Arith.Char] () ->
        AC_Termination_Problem_Spec.Ac_tp_ops_ext d
          (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
          AC_Dependency_Pair_Problem_Spec.Ac_dpp_ops_ext e
            (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
            Bool ->
              Ceta_Problem_Spec.Input (Labelings.Lab b [Arith.Nat])
                [Arith.Char] ->
                Ceta_Problem_Spec.Property (Labelings.Lab b [Arith.Nat]) f ->
                  Ceta_Problem_Spec.Answer (Labelings.Lab b [Arith.Nat])
                    [Arith.Char] ->
                    Proof_Checker.Proof b [Arith.Nat] [Arith.Char] ->
                      Sum_Type.Sum (String -> String) ())
    i j k l False (Ceta_Problem_Spec.FP_TRS_input v va) Ceta_Problem_Spec.Safety
    ans p;
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va)
  Ceta_Problem_Spec.Entailment ans p =
  (Proof_Checker.check_cert ::
    Termination_Problem_Spec.Tp_ops_ext a (Labelings.Lab b [Arith.Nat])
      [Arith.Char] () ->
      Dependency_Pair_Problem_Spec.Dpp_ops_ext c (Labelings.Lab b [Arith.Nat])
        [Arith.Char] () ->
        AC_Termination_Problem_Spec.Ac_tp_ops_ext d
          (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
          AC_Dependency_Pair_Problem_Spec.Ac_dpp_ops_ext e
            (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
            Bool ->
              Ceta_Problem_Spec.Input (Labelings.Lab b [Arith.Nat])
                [Arith.Char] ->
                Ceta_Problem_Spec.Property (Labelings.Lab b [Arith.Nat]) f ->
                  Ceta_Problem_Spec.Answer (Labelings.Lab b [Arith.Nat])
                    [Arith.Char] ->
                    Proof_Checker.Proof b [Arith.Nat] [Arith.Char] ->
                      Sum_Type.Sum (String -> String) ())
    i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    Ceta_Problem_Spec.Entailment ans p;
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va)
  (Ceta_Problem_Spec.Complexity vb) ans p =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    (Ceta_Problem_Spec.Complexity vb) ans p;
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va)
  Ceta_Problem_Spec.Closed_Under_Rewriting ans p =
  (Proof_Checker.check_cert ::
    Termination_Problem_Spec.Tp_ops_ext a (Labelings.Lab b [Arith.Nat])
      [Arith.Char] () ->
      Dependency_Pair_Problem_Spec.Dpp_ops_ext c (Labelings.Lab b [Arith.Nat])
        [Arith.Char] () ->
        AC_Termination_Problem_Spec.Ac_tp_ops_ext d
          (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
          AC_Dependency_Pair_Problem_Spec.Ac_dpp_ops_ext e
            (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
            Bool ->
              Ceta_Problem_Spec.Input (Labelings.Lab b [Arith.Nat])
                [Arith.Char] ->
                Ceta_Problem_Spec.Property (Labelings.Lab b [Arith.Nat]) f ->
                  Ceta_Problem_Spec.Answer (Labelings.Lab b [Arith.Nat])
                    [Arith.Char] ->
                    Proof_Checker.Proof b [Arith.Nat] [Arith.Char] ->
                      Sum_Type.Sum (String -> String) ())
    i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    Ceta_Problem_Spec.Closed_Under_Rewriting ans p;
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va)
  Ceta_Problem_Spec.Infeasibility ans p =
  (Proof_Checker.check_cert ::
    Termination_Problem_Spec.Tp_ops_ext a (Labelings.Lab b [Arith.Nat])
      [Arith.Char] () ->
      Dependency_Pair_Problem_Spec.Dpp_ops_ext c (Labelings.Lab b [Arith.Nat])
        [Arith.Char] () ->
        AC_Termination_Problem_Spec.Ac_tp_ops_ext d
          (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
          AC_Dependency_Pair_Problem_Spec.Ac_dpp_ops_ext e
            (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
            Bool ->
              Ceta_Problem_Spec.Input (Labelings.Lab b [Arith.Nat])
                [Arith.Char] ->
                Ceta_Problem_Spec.Property (Labelings.Lab b [Arith.Nat]) f ->
                  Ceta_Problem_Spec.Answer (Labelings.Lab b [Arith.Nat])
                    [Arith.Char] ->
                    Proof_Checker.Proof b [Arith.Nat] [Arith.Char] ->
                      Sum_Type.Sum (String -> String) ())
    i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    Ceta_Problem_Spec.Infeasibility ans p;
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va)
  Ceta_Problem_Spec.Unknown_Property ans p =
  (Proof_Checker.check_cert ::
    Termination_Problem_Spec.Tp_ops_ext a (Labelings.Lab b [Arith.Nat])
      [Arith.Char] () ->
      Dependency_Pair_Problem_Spec.Dpp_ops_ext c (Labelings.Lab b [Arith.Nat])
        [Arith.Char] () ->
        AC_Termination_Problem_Spec.Ac_tp_ops_ext d
          (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
          AC_Dependency_Pair_Problem_Spec.Ac_dpp_ops_ext e
            (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
            Bool ->
              Ceta_Problem_Spec.Input (Labelings.Lab b [Arith.Nat])
                [Arith.Char] ->
                Ceta_Problem_Spec.Property (Labelings.Lab b [Arith.Nat]) f ->
                  Ceta_Problem_Spec.Answer (Labelings.Lab b [Arith.Nat])
                    [Arith.Char] ->
                    Proof_Checker.Proof b [Arith.Nat] [Arith.Char] ->
                      Sum_Type.Sum (String -> String) ())
    i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    Ceta_Problem_Spec.Unknown_Property ans p;
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop
  (Ceta_Problem_Spec.Decision False) p =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop (Ceta_Problem_Spec.Decision False) p;
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop
  (Ceta_Problem_Spec.Upperbound_Poly vb) p =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop (Ceta_Problem_Spec.Upperbound_Poly vb) p;
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop
  (Ceta_Problem_Spec.Completed_System vb) p =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop (Ceta_Problem_Spec.Completed_System vb) p;
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop
  (Ceta_Problem_Spec.Order_Completed_System vb vc) p =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop (Ceta_Problem_Spec.Order_Completed_System vb vc) p;
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.Complexity_Proof vb) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.Complexity_Proof vb);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.DP_Termination_Proof vb) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.DP_Termination_Proof vb);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.Relative_DP_Termination_Proof vb) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.Relative_DP_Termination_Proof vb);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.DP_Nontermination_Proof vb) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.DP_Nontermination_Proof vb);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.TRS_Nontermination_Proof vb) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.TRS_Nontermination_Proof vb);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.FP_Termination_Proof vb) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.FP_Termination_Proof vb);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.Outermost_RZ_Termination_Proof vb) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.Outermost_RZ_Termination_Proof vb);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.CSR_Termination_Proof vb) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.CSR_Termination_Proof vb);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.CSR_Improved_DP_Proof vb) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.CSR_Improved_DP_Proof vb);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.CSR_Muterm_Typed_DP_Proof vb) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.CSR_Muterm_Typed_DP_Proof vb);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.GM04_Complete_TRS_Proof vb) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.GM04_Complete_TRS_Proof vb);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.GM04_Standalone_DP_Proof_Node vb) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.GM04_Standalone_DP_Proof_Node vb);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.GM04_Standalone_TRS_Proof_Node vb vc) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.GM04_Standalone_TRS_Proof_Node vb vc);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.GM04_Complete_TRS_Nontermination_Proof vb) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.GM04_Complete_TRS_Nontermination_Proof vb);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.FP_Nontermination_Proof vb) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.FP_Nontermination_Proof vb);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.Relative_TRS_Nontermination_Proof vb) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.Relative_TRS_Nontermination_Proof vb);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.TRS_Confluence_Proof vb) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.TRS_Confluence_Proof vb);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.TRS_Non_Confluence_Proof vb) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.TRS_Non_Confluence_Proof vb);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.TRS_Non_Commutation_Proof vb) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.TRS_Non_Commutation_Proof vb);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.TRS_Commutation_Proof vb) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.TRS_Commutation_Proof vb);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.Completion_Proof vb) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.Completion_Proof vb);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.Ordered_Completion_Proof vb) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.Ordered_Completion_Proof vb);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.Equational_Proof vb) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.Equational_Proof vb);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.Equational_Disproof vb) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.Equational_Disproof vb);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.Quasi_Reductive_Proof vb) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.Quasi_Reductive_Proof vb);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.Conditional_CR_Proof vb) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.Conditional_CR_Proof vb);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.Conditional_Non_CR_Proof vb) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.Conditional_Non_CR_Proof vb);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.Tree_Automata_Closed_Proof vb) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.Tree_Automata_Closed_Proof vb);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.AC_Termination_Proof vb) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.AC_Termination_Proof vb);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.LTS_Termination_Proof vb) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.LTS_Termination_Proof vb);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.LTS_Safety_Proof vb) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.LTS_Safety_Proof vb);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.Infeasibility_Proof vb) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.Infeasibility_Proof vb);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.Feasibility_Proof vb) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.Feasibility_Proof vb);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.Unknown_Proof vb) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.Unknown_Proof vb);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.FP_TRS_input v va) prop ans
  (Proof_Checker.Unknown_Disproof vb) =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.FP_TRS_input v va)
    prop ans (Proof_Checker.Unknown_Disproof vb);
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.AC_input v va vb) prop ans p
  = Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.AC_input v va vb)
      prop ans p;
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.LTS_input v) prop ans p =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.LTS_input v) prop
    ans p;
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.LTS_safety_input v va) prop
  ans p =
  Proof_Checker.check_cert i j k l False
    (Ceta_Problem_Spec.LTS_safety_input v va) prop ans p;
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.CTRS_input v) prop ans p =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.CTRS_input v) prop
    ans p;
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.EQ_input v) prop ans p =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.EQ_input v) prop ans
    p;
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.EQ_RO_input v va) prop ans p
  = Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.EQ_RO_input v va)
      prop ans p;
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.EQ_reasoning_input v va) prop
  ans p =
  Proof_Checker.check_cert i j k l False
    (Ceta_Problem_Spec.EQ_reasoning_input v va) prop ans p;
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.TA_input v va) prop ans p =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.TA_input v va) prop
    ans p;
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.Infeasibility_input v va)
  prop ans p =
  Proof_Checker.check_cert i j k l False
    (Ceta_Problem_Spec.Infeasibility_input v va) prop ans p;
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.Single_TRS_input v va) prop
  ans p =
  Proof_Checker.check_cert i j k l False
    (Ceta_Problem_Spec.Single_TRS_input v va) prop ans p;
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.Two_TRS_input v va vb) prop
  ans p =
  Proof_Checker.check_cert i j k l False
    (Ceta_Problem_Spec.Two_TRS_input v va vb) prop ans p;
check_cert_rfc_absolute i j k l (Ceta_Problem_Spec.Unknown_input v) prop ans p =
  Proof_Checker.check_cert i j k l False (Ceta_Problem_Spec.Unknown_input v)
    prop ans p;
check_cert_rfc_absolute i j k l inp Ceta_Problem_Spec.Confluence ans p =
  (Proof_Checker.check_cert ::
    Termination_Problem_Spec.Tp_ops_ext a (Labelings.Lab b [Arith.Nat])
      [Arith.Char] () ->
      Dependency_Pair_Problem_Spec.Dpp_ops_ext c (Labelings.Lab b [Arith.Nat])
        [Arith.Char] () ->
        AC_Termination_Problem_Spec.Ac_tp_ops_ext d
          (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
          AC_Dependency_Pair_Problem_Spec.Ac_dpp_ops_ext e
            (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
            Bool ->
              Ceta_Problem_Spec.Input (Labelings.Lab b [Arith.Nat])
                [Arith.Char] ->
                Ceta_Problem_Spec.Property (Labelings.Lab b [Arith.Nat]) f ->
                  Ceta_Problem_Spec.Answer (Labelings.Lab b [Arith.Nat])
                    [Arith.Char] ->
                    Proof_Checker.Proof b [Arith.Nat] [Arith.Char] ->
                      Sum_Type.Sum (String -> String) ())
    i j k l False inp Ceta_Problem_Spec.Confluence ans p;
check_cert_rfc_absolute i j k l inp Ceta_Problem_Spec.Commutation ans p =
  (Proof_Checker.check_cert ::
    Termination_Problem_Spec.Tp_ops_ext a (Labelings.Lab b [Arith.Nat])
      [Arith.Char] () ->
      Dependency_Pair_Problem_Spec.Dpp_ops_ext c (Labelings.Lab b [Arith.Nat])
        [Arith.Char] () ->
        AC_Termination_Problem_Spec.Ac_tp_ops_ext d
          (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
          AC_Dependency_Pair_Problem_Spec.Ac_dpp_ops_ext e
            (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
            Bool ->
              Ceta_Problem_Spec.Input (Labelings.Lab b [Arith.Nat])
                [Arith.Char] ->
                Ceta_Problem_Spec.Property (Labelings.Lab b [Arith.Nat]) f ->
                  Ceta_Problem_Spec.Answer (Labelings.Lab b [Arith.Nat])
                    [Arith.Char] ->
                    Proof_Checker.Proof b [Arith.Nat] [Arith.Char] ->
                      Sum_Type.Sum (String -> String) ())
    i j k l False inp Ceta_Problem_Spec.Commutation ans p;
check_cert_rfc_absolute i j k l inp Ceta_Problem_Spec.Completion ans p =
  (Proof_Checker.check_cert ::
    Termination_Problem_Spec.Tp_ops_ext a (Labelings.Lab b [Arith.Nat])
      [Arith.Char] () ->
      Dependency_Pair_Problem_Spec.Dpp_ops_ext c (Labelings.Lab b [Arith.Nat])
        [Arith.Char] () ->
        AC_Termination_Problem_Spec.Ac_tp_ops_ext d
          (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
          AC_Dependency_Pair_Problem_Spec.Ac_dpp_ops_ext e
            (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
            Bool ->
              Ceta_Problem_Spec.Input (Labelings.Lab b [Arith.Nat])
                [Arith.Char] ->
                Ceta_Problem_Spec.Property (Labelings.Lab b [Arith.Nat]) f ->
                  Ceta_Problem_Spec.Answer (Labelings.Lab b [Arith.Nat])
                    [Arith.Char] ->
                    Proof_Checker.Proof b [Arith.Nat] [Arith.Char] ->
                      Sum_Type.Sum (String -> String) ())
    i j k l False inp Ceta_Problem_Spec.Completion ans p;
check_cert_rfc_absolute i j k l inp Ceta_Problem_Spec.Safety ans p =
  (Proof_Checker.check_cert ::
    Termination_Problem_Spec.Tp_ops_ext a (Labelings.Lab b [Arith.Nat])
      [Arith.Char] () ->
      Dependency_Pair_Problem_Spec.Dpp_ops_ext c (Labelings.Lab b [Arith.Nat])
        [Arith.Char] () ->
        AC_Termination_Problem_Spec.Ac_tp_ops_ext d
          (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
          AC_Dependency_Pair_Problem_Spec.Ac_dpp_ops_ext e
            (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
            Bool ->
              Ceta_Problem_Spec.Input (Labelings.Lab b [Arith.Nat])
                [Arith.Char] ->
                Ceta_Problem_Spec.Property (Labelings.Lab b [Arith.Nat]) f ->
                  Ceta_Problem_Spec.Answer (Labelings.Lab b [Arith.Nat])
                    [Arith.Char] ->
                    Proof_Checker.Proof b [Arith.Nat] [Arith.Char] ->
                      Sum_Type.Sum (String -> String) ())
    i j k l False inp Ceta_Problem_Spec.Safety ans p;
check_cert_rfc_absolute i j k l inp Ceta_Problem_Spec.Entailment ans p =
  (Proof_Checker.check_cert ::
    Termination_Problem_Spec.Tp_ops_ext a (Labelings.Lab b [Arith.Nat])
      [Arith.Char] () ->
      Dependency_Pair_Problem_Spec.Dpp_ops_ext c (Labelings.Lab b [Arith.Nat])
        [Arith.Char] () ->
        AC_Termination_Problem_Spec.Ac_tp_ops_ext d
          (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
          AC_Dependency_Pair_Problem_Spec.Ac_dpp_ops_ext e
            (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
            Bool ->
              Ceta_Problem_Spec.Input (Labelings.Lab b [Arith.Nat])
                [Arith.Char] ->
                Ceta_Problem_Spec.Property (Labelings.Lab b [Arith.Nat]) f ->
                  Ceta_Problem_Spec.Answer (Labelings.Lab b [Arith.Nat])
                    [Arith.Char] ->
                    Proof_Checker.Proof b [Arith.Nat] [Arith.Char] ->
                      Sum_Type.Sum (String -> String) ())
    i j k l False inp Ceta_Problem_Spec.Entailment ans p;
check_cert_rfc_absolute i j k l inp (Ceta_Problem_Spec.Complexity v) ans p =
  Proof_Checker.check_cert i j k l False inp (Ceta_Problem_Spec.Complexity v)
    ans p;
check_cert_rfc_absolute i j k l inp Ceta_Problem_Spec.Closed_Under_Rewriting ans
  p = (Proof_Checker.check_cert ::
        Termination_Problem_Spec.Tp_ops_ext a (Labelings.Lab b [Arith.Nat])
          [Arith.Char] () ->
          Dependency_Pair_Problem_Spec.Dpp_ops_ext c
            (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
            AC_Termination_Problem_Spec.Ac_tp_ops_ext d
              (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
              AC_Dependency_Pair_Problem_Spec.Ac_dpp_ops_ext e
                (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
                Bool ->
                  Ceta_Problem_Spec.Input (Labelings.Lab b [Arith.Nat])
                    [Arith.Char] ->
                    Ceta_Problem_Spec.Property (Labelings.Lab b [Arith.Nat])
                      f ->
                      Ceta_Problem_Spec.Answer (Labelings.Lab b [Arith.Nat])
                        [Arith.Char] ->
                        Proof_Checker.Proof b [Arith.Nat] [Arith.Char] ->
                          Sum_Type.Sum (String -> String) ())
        i j k l False inp Ceta_Problem_Spec.Closed_Under_Rewriting ans p;
check_cert_rfc_absolute i j k l inp Ceta_Problem_Spec.Infeasibility ans p =
  (Proof_Checker.check_cert ::
    Termination_Problem_Spec.Tp_ops_ext a (Labelings.Lab b [Arith.Nat])
      [Arith.Char] () ->
      Dependency_Pair_Problem_Spec.Dpp_ops_ext c (Labelings.Lab b [Arith.Nat])
        [Arith.Char] () ->
        AC_Termination_Problem_Spec.Ac_tp_ops_ext d
          (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
          AC_Dependency_Pair_Problem_Spec.Ac_dpp_ops_ext e
            (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
            Bool ->
              Ceta_Problem_Spec.Input (Labelings.Lab b [Arith.Nat])
                [Arith.Char] ->
                Ceta_Problem_Spec.Property (Labelings.Lab b [Arith.Nat]) f ->
                  Ceta_Problem_Spec.Answer (Labelings.Lab b [Arith.Nat])
                    [Arith.Char] ->
                    Proof_Checker.Proof b [Arith.Nat] [Arith.Char] ->
                      Sum_Type.Sum (String -> String) ())
    i j k l False inp Ceta_Problem_Spec.Infeasibility ans p;
check_cert_rfc_absolute i j k l inp Ceta_Problem_Spec.Unknown_Property ans p =
  (Proof_Checker.check_cert ::
    Termination_Problem_Spec.Tp_ops_ext a (Labelings.Lab b [Arith.Nat])
      [Arith.Char] () ->
      Dependency_Pair_Problem_Spec.Dpp_ops_ext c (Labelings.Lab b [Arith.Nat])
        [Arith.Char] () ->
        AC_Termination_Problem_Spec.Ac_tp_ops_ext d
          (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
          AC_Dependency_Pair_Problem_Spec.Ac_dpp_ops_ext e
            (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
            Bool ->
              Ceta_Problem_Spec.Input (Labelings.Lab b [Arith.Nat])
                [Arith.Char] ->
                Ceta_Problem_Spec.Property (Labelings.Lab b [Arith.Nat]) f ->
                  Ceta_Problem_Spec.Answer (Labelings.Lab b [Arith.Nat])
                    [Arith.Char] ->
                    Proof_Checker.Proof b [Arith.Nat] [Arith.Char] ->
                      Sum_Type.Sum (String -> String) ())
    i j k l False inp Ceta_Problem_Spec.Unknown_Property ans p;
check_cert_rfc_absolute i j k l inp prop (Ceta_Problem_Spec.Decision False) p =
  Proof_Checker.check_cert i j k l False inp prop
    (Ceta_Problem_Spec.Decision False) p;
check_cert_rfc_absolute i j k l inp prop (Ceta_Problem_Spec.Upperbound_Poly v) p
  = Proof_Checker.check_cert i j k l False inp prop
      (Ceta_Problem_Spec.Upperbound_Poly v) p;
check_cert_rfc_absolute i j k l inp prop (Ceta_Problem_Spec.Completed_System v)
  p = Proof_Checker.check_cert i j k l False inp prop
        (Ceta_Problem_Spec.Completed_System v) p;
check_cert_rfc_absolute i j k l inp prop
  (Ceta_Problem_Spec.Order_Completed_System v va) p =
  Proof_Checker.check_cert i j k l False inp prop
    (Ceta_Problem_Spec.Order_Completed_System v va) p;
check_cert_rfc_absolute i j k l inp prop ans (Proof_Checker.Complexity_Proof v)
  = Proof_Checker.check_cert i j k l False inp prop ans
      (Proof_Checker.Complexity_Proof v);
check_cert_rfc_absolute i j k l inp prop ans
  (Proof_Checker.DP_Termination_Proof v) =
  Proof_Checker.check_cert i j k l False inp prop ans
    (Proof_Checker.DP_Termination_Proof v);
check_cert_rfc_absolute i j k l inp prop ans
  (Proof_Checker.Relative_DP_Termination_Proof v) =
  Proof_Checker.check_cert i j k l False inp prop ans
    (Proof_Checker.Relative_DP_Termination_Proof v);
check_cert_rfc_absolute i j k l inp prop ans
  (Proof_Checker.DP_Nontermination_Proof v) =
  Proof_Checker.check_cert i j k l False inp prop ans
    (Proof_Checker.DP_Nontermination_Proof v);
check_cert_rfc_absolute i j k l inp prop ans
  (Proof_Checker.TRS_Nontermination_Proof v) =
  Proof_Checker.check_cert i j k l False inp prop ans
    (Proof_Checker.TRS_Nontermination_Proof v);
check_cert_rfc_absolute i j k l inp prop ans
  (Proof_Checker.FP_Termination_Proof v) =
  Proof_Checker.check_cert i j k l False inp prop ans
    (Proof_Checker.FP_Termination_Proof v);
check_cert_rfc_absolute i j k l inp prop ans
  (Proof_Checker.Outermost_RZ_Termination_Proof v) =
  Proof_Checker.check_cert i j k l False inp prop ans
    (Proof_Checker.Outermost_RZ_Termination_Proof v);
check_cert_rfc_absolute i j k l inp prop ans
  (Proof_Checker.CSR_Termination_Proof v) =
  Proof_Checker.check_cert i j k l False inp prop ans
    (Proof_Checker.CSR_Termination_Proof v);
check_cert_rfc_absolute i j k l inp prop ans
  (Proof_Checker.CSR_Improved_DP_Proof v) =
  Proof_Checker.check_cert i j k l False inp prop ans
    (Proof_Checker.CSR_Improved_DP_Proof v);
check_cert_rfc_absolute i j k l inp prop ans
  (Proof_Checker.CSR_Muterm_Typed_DP_Proof v) =
  Proof_Checker.check_cert i j k l False inp prop ans
    (Proof_Checker.CSR_Muterm_Typed_DP_Proof v);
check_cert_rfc_absolute i j k l inp prop ans
  (Proof_Checker.GM04_Complete_TRS_Proof v) =
  Proof_Checker.check_cert i j k l False inp prop ans
    (Proof_Checker.GM04_Complete_TRS_Proof v);
check_cert_rfc_absolute i j k l inp prop ans
  (Proof_Checker.GM04_Standalone_DP_Proof_Node v) =
  Proof_Checker.check_cert i j k l False inp prop ans
    (Proof_Checker.GM04_Standalone_DP_Proof_Node v);
check_cert_rfc_absolute i j k l inp prop ans
  (Proof_Checker.GM04_Standalone_TRS_Proof_Node v va) =
  Proof_Checker.check_cert i j k l False inp prop ans
    (Proof_Checker.GM04_Standalone_TRS_Proof_Node v va);
check_cert_rfc_absolute i j k l inp prop ans
  (Proof_Checker.GM04_Complete_TRS_Nontermination_Proof v) =
  Proof_Checker.check_cert i j k l False inp prop ans
    (Proof_Checker.GM04_Complete_TRS_Nontermination_Proof v);
check_cert_rfc_absolute i j k l inp prop ans
  (Proof_Checker.FP_Nontermination_Proof v) =
  Proof_Checker.check_cert i j k l False inp prop ans
    (Proof_Checker.FP_Nontermination_Proof v);
check_cert_rfc_absolute i j k l inp prop ans
  (Proof_Checker.Relative_TRS_Nontermination_Proof v) =
  Proof_Checker.check_cert i j k l False inp prop ans
    (Proof_Checker.Relative_TRS_Nontermination_Proof v);
check_cert_rfc_absolute i j k l inp prop ans
  (Proof_Checker.TRS_Confluence_Proof v) =
  Proof_Checker.check_cert i j k l False inp prop ans
    (Proof_Checker.TRS_Confluence_Proof v);
check_cert_rfc_absolute i j k l inp prop ans
  (Proof_Checker.TRS_Non_Confluence_Proof v) =
  Proof_Checker.check_cert i j k l False inp prop ans
    (Proof_Checker.TRS_Non_Confluence_Proof v);
check_cert_rfc_absolute i j k l inp prop ans
  (Proof_Checker.TRS_Non_Commutation_Proof v) =
  Proof_Checker.check_cert i j k l False inp prop ans
    (Proof_Checker.TRS_Non_Commutation_Proof v);
check_cert_rfc_absolute i j k l inp prop ans
  (Proof_Checker.TRS_Commutation_Proof v) =
  Proof_Checker.check_cert i j k l False inp prop ans
    (Proof_Checker.TRS_Commutation_Proof v);
check_cert_rfc_absolute i j k l inp prop ans (Proof_Checker.Completion_Proof v)
  = Proof_Checker.check_cert i j k l False inp prop ans
      (Proof_Checker.Completion_Proof v);
check_cert_rfc_absolute i j k l inp prop ans
  (Proof_Checker.Ordered_Completion_Proof v) =
  Proof_Checker.check_cert i j k l False inp prop ans
    (Proof_Checker.Ordered_Completion_Proof v);
check_cert_rfc_absolute i j k l inp prop ans (Proof_Checker.Equational_Proof v)
  = Proof_Checker.check_cert i j k l False inp prop ans
      (Proof_Checker.Equational_Proof v);
check_cert_rfc_absolute i j k l inp prop ans
  (Proof_Checker.Equational_Disproof v) =
  Proof_Checker.check_cert i j k l False inp prop ans
    (Proof_Checker.Equational_Disproof v);
check_cert_rfc_absolute i j k l inp prop ans
  (Proof_Checker.Quasi_Reductive_Proof v) =
  Proof_Checker.check_cert i j k l False inp prop ans
    (Proof_Checker.Quasi_Reductive_Proof v);
check_cert_rfc_absolute i j k l inp prop ans
  (Proof_Checker.Conditional_CR_Proof v) =
  Proof_Checker.check_cert i j k l False inp prop ans
    (Proof_Checker.Conditional_CR_Proof v);
check_cert_rfc_absolute i j k l inp prop ans
  (Proof_Checker.Conditional_Non_CR_Proof v) =
  Proof_Checker.check_cert i j k l False inp prop ans
    (Proof_Checker.Conditional_Non_CR_Proof v);
check_cert_rfc_absolute i j k l inp prop ans
  (Proof_Checker.Tree_Automata_Closed_Proof v) =
  Proof_Checker.check_cert i j k l False inp prop ans
    (Proof_Checker.Tree_Automata_Closed_Proof v);
check_cert_rfc_absolute i j k l inp prop ans
  (Proof_Checker.AC_Termination_Proof v) =
  Proof_Checker.check_cert i j k l False inp prop ans
    (Proof_Checker.AC_Termination_Proof v);
check_cert_rfc_absolute i j k l inp prop ans
  (Proof_Checker.LTS_Termination_Proof v) =
  Proof_Checker.check_cert i j k l False inp prop ans
    (Proof_Checker.LTS_Termination_Proof v);
check_cert_rfc_absolute i j k l inp prop ans (Proof_Checker.LTS_Safety_Proof v)
  = Proof_Checker.check_cert i j k l False inp prop ans
      (Proof_Checker.LTS_Safety_Proof v);
check_cert_rfc_absolute i j k l inp prop ans
  (Proof_Checker.Infeasibility_Proof v) =
  Proof_Checker.check_cert i j k l False inp prop ans
    (Proof_Checker.Infeasibility_Proof v);
check_cert_rfc_absolute i j k l inp prop ans (Proof_Checker.Feasibility_Proof v)
  = Proof_Checker.check_cert i j k l False inp prop ans
      (Proof_Checker.Feasibility_Proof v);
check_cert_rfc_absolute i j k l inp prop ans (Proof_Checker.Unknown_Proof v) =
  Proof_Checker.check_cert i j k l False inp prop ans
    (Proof_Checker.Unknown_Proof v);
check_cert_rfc_absolute i j k l inp prop ans (Proof_Checker.Unknown_Disproof v)
  = Proof_Checker.check_cert i j k l False inp prop ans
      (Proof_Checker.Unknown_Disproof v);

certify_cert_problem_rfc_absolute ::
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
         Proof_Checker.Proof b [Arith.Nat] [Arith.Char] ->
           Proof_Checker.Cert_result;
certify_cert_problem_rfc_absolute i j k l a inp prop ans p =
  let {
    old = Proof_Checker.certify_cert_problem i j k l a inp prop ans p;
  } in (if Proof_Checker.equal_cert_result old Proof_Checker.Certified || a
         then old
         else (case check_cert_rfc_absolute i j k l inp prop ans p of {
                Sum_Type.Inl _ -> old;
                Sum_Type.Inr _ -> Proof_Checker.Certified;
              }));

certify_proof_rfc_absolute ::
  Bool ->
    Maybe [Arith.Char] ->
      Maybe [Arith.Char] ->
        Maybe [Arith.Char] -> [Arith.Char] -> Proof_Checker.Cert_result;
certify_proof_rfc_absolute a inp_o prop_o answ_o prfs =
  Ceta.bind2 (CPF_Parser.parse_combined_cert_problem inp_o prop_o answ_o prfs)
    Proof_Checker.Unsupported
    (\ (inp, (prop, (b, c))) ->
      certify_cert_problem_rfc_absolute Termination_Problem_Impl.tp_rbt_impl
        Dependency_Pair_Problem_Impl.dpp_rbt_impl
        AC_Termination_Problem_Impl.ac_tp_list_impl
        AC_Dependency_Pair_Problem_Impl.ac_dpp_rbt_impl a inp prop b c);

}
