{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Check_CRP(Cr_proof(..), Ncr_proof(..), Comm_proof(..), Ncomm_proof(..),
             check_cr_proof, check_ncr_proof, default_grd_fun, check_comm_proof,
             check_ncomm_proof)
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
import qualified Non_Commutation_Impl;
import qualified Trs_Impl_More;
import qualified Quasi_Order;
import qualified Missing_List;
import qualified Check_Monad;
import qualified Critical_Pair_Closure_Impl;
import qualified Development_Closed_Impl;
import qualified Strongly_Closed_Impl;
import qualified Rule_Labeling_Impl;
import qualified Redundant_Rules_Impl;
import qualified Parallel_Closed_Impl;
import qualified Orthogonality_Impl;
import qualified Okui_Criterion_Impl;
import qualified LS_Persistence_Impl;
import qualified RenamingN_String;
import qualified Renaming2_String;
import qualified QDP_Framework_Impl;
import qualified FOR_Preliminaries;
import qualified Error_Monad;
import qualified HOL;
import qualified Dependency_Pair_Problem_Spec;
import qualified Termination_Problem_Spec;
import qualified RenamingN;
import qualified Renaming2;
import qualified Sum_Type;
import qualified Countable;
import qualified Compare;
import qualified Mapping;
import qualified Compare_Order_Instances;
import qualified Lists_are_Infinite;
import qualified Reduction_Pair_Implementations;
import qualified Non_Confluence_Impl;
import qualified Parallel_Critical_Pairs_Impl;
import qualified Check_Termination;
import qualified Critical_Pairs_Impl;
import qualified Check_Joins;
import qualified Labelings;
import qualified Term_Rewriting;
import qualified Arith;

data Cr_proof a b c =
  SN_WCR (Critical_Pairs_Impl.Join_info (Labelings.Lab a b) c)
    (Check_Termination.Trs_termination_proof a b c)
  | Weakly_Orthogonal | Strongly_Closed Arith.Nat
  | Rule_Labeling
      [((Term_Rewriting.Term (Labelings.Lab a b) c,
          Term_Rewriting.Term (Labelings.Lab a b) c),
         Arith.Nat)]
      [Check_Joins.Crit_pair_info (Labelings.Lab a b) c]
      (Maybe (Check_Termination.Trs_termination_proof a b c))
  | Rule_Labeling_Conv
      [((Term_Rewriting.Term (Labelings.Lab a b) c,
          Term_Rewriting.Term (Labelings.Lab a b) c),
         Arith.Nat)]
      [Check_Joins.Crit_pair_info (Labelings.Lab a b) [Arith.Char]]
      (Maybe (Arith.Nat, Check_Termination.Trs_termination_proof a b c))
  | Redundant_Rules
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      Arith.Nat [[Term_Rewriting.Term (Labelings.Lab a b) c]] (Cr_proof a b c)
  | Compositional_PCP
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Check_Joins.Cp_join_hints (Labelings.Lab a b) c) (Cr_proof a b c)
  | Compositional_PCP_Rule_Lab
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Parallel_Critical_Pairs_Impl.Pcp_rule_lab_com (Labelings.Lab a b) c)
      (Cr_proof a b c)
  | Parallel_Closed (Maybe Arith.Nat)
  | PCP_Closed (Check_Joins.Cp_join_hints (Labelings.Lab a b) c)
      (Check_Joins.Cp_join_hints (Labelings.Lab a b) c)
  | PCP_Rule_Lab
      (Parallel_Critical_Pairs_Impl.Pcp_rule_lab (Labelings.Lab a b) c)
  | Development_Closed (Maybe Arith.Nat)
  | Sim_CPS_Closed (Check_Joins.Cp_join_hints (Labelings.Lab a b) c)
  | Critical_Pair_Closing_System
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Check_Termination.Trs_termination_proof a b c) Arith.Nat
  | Compositional_PCPS
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Check_Joins.Cp_join_hints (Labelings.Lab a b) c)
      (Check_Joins.Cp_join_hints (Labelings.Lab a b) c)
      (Check_Termination.Trs_termination_proof a b c) (Cr_proof a b c)
  | Persistent_Decomposition
      [(Labelings.Lab a b, ([[Arith.Char]], [Arith.Char]))]
      [([(Term_Rewriting.Term (Labelings.Lab a b) c,
           Term_Rewriting.Term (Labelings.Lab a b) c)],
         Cr_proof a b c)];

data Ncr_proof a b c d = SN_NWCR (Check_Termination.Trs_termination_proof a b c)
  | Non_Join (Term_Rewriting.Term (Labelings.Lab a b) c)
      [([Arith.Nat],
         ((Term_Rewriting.Term (Labelings.Lab a b) c,
            Term_Rewriting.Term (Labelings.Lab a b) c),
           Term_Rewriting.Term (Labelings.Lab a b) c))]
      [([Arith.Nat],
         ((Term_Rewriting.Term (Labelings.Lab a b) c,
            Term_Rewriting.Term (Labelings.Lab a b) c),
           Term_Rewriting.Term (Labelings.Lab a b) c))]
      (Non_Confluence_Impl.Non_join_info (Labelings.Lab a b) c d
        (Reduction_Pair_Implementations.Redtriple_impl (Labelings.Lab a b)))
  | NCR_Disj_Subtrs
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Ncr_proof a b c d)
  | NCR_Redundant_Rules
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      Arith.Nat (Ncr_proof a b c d)
  | NCR_Persistent_Decomposition
      [(Labelings.Lab a b, ([[Arith.Char]], [Arith.Char]))]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Ncr_proof a b c d)
  | NCR_Rule_Removal
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      [((Term_Rewriting.Term (Labelings.Lab a b) c,
          Term_Rewriting.Term (Labelings.Lab a b) c),
         [([Arith.Nat],
            ((Term_Rewriting.Term (Labelings.Lab a b) c,
               Term_Rewriting.Term (Labelings.Lab a b) c),
              Term_Rewriting.Term (Labelings.Lab a b) c))])]
      (Ncr_proof a b c d);

data Comm_proof a b c = Parallel_Closed_Comm (Maybe Arith.Nat)
  | Development_Closed_Comm (Maybe Arith.Nat)
  | PCP_Closed_Comm (Check_Joins.Cp_join_hints (Labelings.Lab a b) c)
      (Check_Joins.Cp_join_hints (Labelings.Lab a b) c)
  | PCP_Rule_Lab_Comm
      (Parallel_Critical_Pairs_Impl.Pcp_rule_lab_com (Labelings.Lab a b) c)
  | PCP_Compositional_Rule_Lab_Comm
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Parallel_Critical_Pairs_Impl.Pcp_rule_lab_com (Labelings.Lab a b) c)
      (Comm_proof a b c)
  | Sim_CPS_Closed_Comm (Check_Joins.Cp_join_hints (Labelings.Lab a b) c)
  | Compositional_PCPS_Comm
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Check_Joins.Cp_join_hints (Labelings.Lab a b) c)
      (Check_Joins.Cp_join_hints (Labelings.Lab a b) c)
      (Check_Joins.Cp_join_hints (Labelings.Lab a b) c)
      (Check_Joins.Cp_join_hints (Labelings.Lab a b) c)
      (Check_Termination.Trs_termination_proof a b c) (Comm_proof a b c)
  | Swap_Comm (Comm_proof a b c) | CR_Proof (Cr_proof a b c);

data Ncomm_proof a b c d =
  Non_Join_Comm (Term_Rewriting.Term (Labelings.Lab a b) c)
    [([Arith.Nat],
       ((Term_Rewriting.Term (Labelings.Lab a b) c,
          Term_Rewriting.Term (Labelings.Lab a b) c),
         Term_Rewriting.Term (Labelings.Lab a b) c))]
    [([Arith.Nat],
       ((Term_Rewriting.Term (Labelings.Lab a b) c,
          Term_Rewriting.Term (Labelings.Lab a b) c),
         Term_Rewriting.Term (Labelings.Lab a b) c))]
    (Non_Confluence_Impl.Non_join_info (Labelings.Lab a b) c d
      (Reduction_Pair_Implementations.Redtriple_impl (Labelings.Lab a b)))
  | Swap_Not_Comm (Ncomm_proof a b c d);

swap_cp_info ::
  forall a b. Check_Joins.Crit_pair_info a b -> Check_Joins.Crit_pair_info a b;
swap_cp_info info =
  Check_Joins.Crit_Pair_Info (Check_Joins.cp_right info)
    (Check_Joins.cp_peak info) (Check_Joins.cp_left info)
    (reverse (Check_Joins.cp_join info)) (Check_Joins.cp_poss info)
    (Arith.map_option Arith.swap (Check_Joins.cp_labels info));

symmetric_cp_infos ::
  forall a b.
    [Check_Joins.Crit_pair_info a b] -> [Check_Joins.Crit_pair_info a b];
symmetric_cp_infos infos =
  infos ++
    Arith.map_filter
      (\ x ->
        (if Arith.membera [Nothing, Just []] (Check_Joins.cp_poss x)
          then Just (swap_cp_info x) else Nothing))
      infos;

check_cr_proof ::
  forall a b c.
    (Compare.Compare_order b, Countable.Countable b, Eq b,
      Term_Rewriting.Showl b) => Bool ->
                                   (String -> String) ->
                                     Termination_Problem_Spec.Tp_ops_ext a
                                       (Labelings.Lab b [Arith.Nat])
                                       [Arith.Char] () ->
                                       Dependency_Pair_Problem_Spec.Dpp_ops_ext
 c (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
 [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
    Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
   Cr_proof b [Arith.Nat] [Arith.Char] -> Sum_Type.Sum (String -> String) ();
check_cr_proof a ia i j r (SN_WCR joins_i prf) =
  FOR_Preliminaries.debug ia "SN_WCR"
    (let {
       tp = Termination_Problem_Spec.mk i False [] r [];
     } in Error_Monad.bind
            (Error_Monad.catch_error
              (Check_Termination.check_trs_termination_proof i j a
                (Term_Rewriting.add_index ia Arith.one_nat) tp prf)
              (\ x ->
                Sum_Type.Inl
                  ((ia . Term_Rewriting.showsl_lit
                           ": error below strong normalization + wcr\n") .
                    x)))
            (\ _ ->
              Error_Monad.catch_error
                (Critical_Pairs_Impl.check_critical_pairs r
                  (Critical_Pairs_Impl.critical_pairs_impl
                    Renaming2_String.string_rename r r)
                  joins_i)
                (\ x ->
                  Sum_Type.Inl
                    ((((ia . Term_Rewriting.showsl_lit
                               ": error when proving local confluence of ") .
                        QDP_Framework_Impl.showsl_tp i tp) .
                       Term_Rewriting.showsl_literal "\n") .
                      x))));
check_cr_proof a ia i j r Weakly_Orthogonal =
  FOR_Preliminaries.debug ia "Weakly Orthogonal"
    (Error_Monad.catch_error
      (Orthogonality_Impl.check_weakly_orthogonal Renaming2_String.string_rename
        r)
      (\ x ->
        Sum_Type.Inl
          (((ia . Term_Rewriting.showsl_lit
                    ": error in checking weakly orthogonality of the ") .
             Term_Rewriting.showsl_trs r) .
            x)));
check_cr_proof a ia i j r (Strongly_Closed n) =
  FOR_Preliminaries.debug ia "Strongly Closed"
    (Error_Monad.catch_error
      (Strongly_Closed_Impl.check_strongly_closed Renaming2_String.string_rename
        r n)
      (\ x ->
        Sum_Type.Inl
          (((ia . Term_Rewriting.showsl_lit
                    ": error in checking strong closedness for the ") .
             Term_Rewriting.showsl_trs r) .
            x)));
check_cr_proof a ia i j r (Compositional_PCP c hints prf) =
  FOR_Preliminaries.debug ia "Compositional PCP"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Parallel_Critical_Pairs_Impl.check_compositional_parallel_pairs
          RenamingN_String.string_renameN r c hints)
        (\ x ->
          Sum_Type.Inl
            ((((ia . Term_Rewriting.showsl_lit
                       ": error in checking compositional parallel critical pairs to switch to TRS C = \n") .
                Term_Rewriting.showsl_trs c) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ _ ->
        Error_Monad.catch_error
          (check_cr_proof a (Term_Rewriting.add_index ia Arith.one_nat) i j c
            prf)
          (\ x ->
            Sum_Type.Inl
              ((((ia . Term_Rewriting.showsl_lit
                         ": error in proving confluence of sub TRS C\n") .
                  Term_Rewriting.showsl_trs c) .
                 Term_Rewriting.showsl_literal "\n") .
                x))));
check_cr_proof a ia i j r (Compositional_PCPS c p hintsP hints sn_prf cr_prf) =
  FOR_Preliminaries.debug ia "Compositional PCPS"
    (let {
       tp = Termination_Problem_Spec.mk i False [] p r;
     } in Error_Monad.bind
            (Error_Monad.catch_error
              (Parallel_Critical_Pairs_Impl.check_compositional_PCPS
                RenamingN_String.string_renameN r c p hintsP hints)
              (\ x ->
                Sum_Type.Inl
                  ((((ia . Term_Rewriting.showsl_lit
                             ": error in checking compositional parallel critical system to switch to TRS C = \n") .
                      Term_Rewriting.showsl_trs c) .
                     Term_Rewriting.showsl_literal "\n") .
                    x)))
            (\ _ ->
              Error_Monad.bind
                (Error_Monad.catch_error
                  (Check_Termination.check_trs_termination_proof i j a
                    (Term_Rewriting.add_index ia Arith.one_nat) tp sn_prf)
                  (\ x ->
                    Sum_Type.Inl
                      ((ia . Term_Rewriting.showsl_lit
                               ": error below relative termination proof of compositional CPCS\n") .
                        x)))
                (\ _ ->
                  Error_Monad.catch_error
                    (check_cr_proof a
                      (Term_Rewriting.add_index ia
                        (Arith.nat_of_integer (2 :: Integer)))
                      i j c cr_prf)
                    (\ x ->
                      Sum_Type.Inl
                        ((((ia . Term_Rewriting.showsl_lit
                                   ": error in proving confluence of sub TRS C\n") .
                            Term_Rewriting.showsl_trs c) .
                           Term_Rewriting.showsl_literal "\n") .
                          x)))));
check_cr_proof a ia i j r (Compositional_PCP_Rule_Lab c hints prf) =
  FOR_Preliminaries.debug ia "Compositional PCP Rule Labeling"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Parallel_Critical_Pairs_Impl.check_compositional_pcp_rule_lab
          RenamingN_String.string_renameN r c hints)
        (\ x ->
          Sum_Type.Inl
            ((ia . Term_Rewriting.showsl_lit
                     ": error in checking compositional parallel critical pairs \n") .
              x)))
      (\ _ ->
        Error_Monad.catch_error
          (check_cr_proof a (Term_Rewriting.add_index ia Arith.one_nat) i j c
            prf)
          (\ x ->
            Sum_Type.Inl
              ((((ia . Term_Rewriting.showsl_lit
                         ": error in proving confluence of sub TRS C\n") .
                  Term_Rewriting.showsl_trs c) .
                 Term_Rewriting.showsl_literal "\n") .
                x))));
check_cr_proof a ia i j r (PCP_Closed hints_cp hints_pcp) =
  FOR_Preliminaries.debug ia "PCP Closed"
    (Error_Monad.catch_error
      (Parallel_Critical_Pairs_Impl.check_parallel_critical_pairs_closed_CR
        RenamingN_String.string_renameN r hints_cp hints_pcp)
      (\ x ->
        Sum_Type.Inl
          ((ia . Term_Rewriting.showsl_lit
                   ": error in checking parallel critical pair closure criterion\n") .
            x)));
check_cr_proof a ia i j r (PCP_Rule_Lab hints) =
  FOR_Preliminaries.debug ia "PCP Rule Labeling"
    (Error_Monad.catch_error
      (Parallel_Critical_Pairs_Impl.check_pcp_rule_lab
        RenamingN_String.string_renameN r hints)
      (\ x ->
        Sum_Type.Inl
          ((ia . Term_Rewriting.showsl_lit
                   ": error when proving confluence by rule labeling with parallel critical pairs\n") .
            x)));
check_cr_proof a ia i j r (Rule_Labeling rl joins prf) =
  FOR_Preliminaries.debug ia "Rule Labeling"
    (Error_Monad.bind
      (case prf of {
        Nothing -> Term_Rewriting.check_linear_trs r;
        Just prfa ->
          Error_Monad.bind (Term_Rewriting.check_left_linear_trs r)
            (\ _ ->
              (case Arith.partition
                      (\ lr -> Term_Rewriting.linear_term (snd lr)) r
                of {
                (rnd, rd) ->
                  let {
                    tp = Termination_Problem_Spec.mk i False [] rd rnd;
                  } in Error_Monad.catch_error
                         (Check_Termination.check_trs_termination_proof i j a
                           (Term_Rewriting.add_index ia Arith.one_nat) tp prfa)
                         (\ x ->
                           Sum_Type.Inl
                             ((ia . Term_Rewriting.showsl_lit
                                      ": error below relative termination for rule labeling\n") .
                               x));
              }));
      })
      (\ _ ->
        Error_Monad.catch_error
          (Rule_Labeling_Impl.check_rule_labeling_eld
            Renaming2_String.string_rename r rl (symmetric_cp_infos joins))
          (\ x ->
            Sum_Type.Inl
              (((ia . Term_Rewriting.showsl_lit
                        ": error in checking decreasingness of CPs using rule labeling for the ") .
                 Term_Rewriting.showsl_trs r) .
                x))));
check_cr_proof a ia i j r (Rule_Labeling_Conv rl convs nprf) =
  FOR_Preliminaries.debug ia "Rule Labeling"
    (case nprf of {
      Nothing ->
        Error_Monad.bind (Term_Rewriting.check_linear_trs r)
          (\ _ ->
            Error_Monad.catch_error
              (Rule_Labeling_Impl.check_rule_labeling_eldc
                Renaming2_String.string_rename r rl (symmetric_cp_infos convs)
                Nothing)
              (\ x ->
                Sum_Type.Inl
                  (((ia . Term_Rewriting.showsl_lit
                            ": error in checking decreasingness of CPs using rule labeling for the ") .
                     Term_Rewriting.showsl_trs r) .
                    x)));
      Just (n, prf) ->
        Error_Monad.bind (Term_Rewriting.check_left_linear_trs r)
          (\ _ ->
            (case Arith.partition (\ lr -> Term_Rewriting.linear_term (snd lr))
                    r
              of {
              (rnd, rd) ->
                let {
                  tp = Termination_Problem_Spec.mk i False [] rd rnd;
                } in Error_Monad.bind
                       (Error_Monad.catch_error
                         (Check_Termination.check_trs_termination_proof i j a
                           (Term_Rewriting.add_index ia Arith.one_nat) tp prf)
                         (\ x ->
                           Sum_Type.Inl
                             ((ia . Term_Rewriting.showsl_lit
                                      ": error below relative termination for rule labeling\n") .
                               x)))
                       (\ _ ->
                         Error_Monad.catch_error
                           (Rule_Labeling_Impl.check_rule_labeling_eldc
                             Renaming2_String.string_rename r rl
                             (symmetric_cp_infos convs) (Just n))
                           (\ x ->
                             Sum_Type.Inl
                               (((ia . Term_Rewriting.showsl_lit
 ": error in checking decreasingness of CPs using rule labeling for the ") .
                                  Term_Rewriting.showsl_trs r) .
                                 x)));
            }));
    });
check_cr_proof a ia i j r (Redundant_Rules rs n convs prf) =
  FOR_Preliminaries.debug ia "Redundant Rules"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (check_cr_proof a (Term_Rewriting.add_index ia Arith.one_nat) i j rs
          prf)
        (\ x ->
          Sum_Type.Inl
            (((ia . Term_Rewriting.showsl_lit
                      ": error below confluence of modified TRS\n") .
               Term_Rewriting.showsl_trs rs) .
              x)))
      (\ _ ->
        Error_Monad.catch_error
          (Redundant_Rules_Impl.check_redundant_rules r rs n convs)
          (\ x ->
            Sum_Type.Inl
              (((((ia . Term_Rewriting.showsl_lit
                          ": error in checking redundant rules transformation of the ") .
                   Term_Rewriting.showsl_trs r) .
                  Term_Rewriting.showsl_lit "transformed to the ") .
                 Term_Rewriting.showsl_trs rs) .
                x))));
check_cr_proof a ia i j r (Parallel_Closed n) =
  FOR_Preliminaries.debug ia "Parallel Closed"
    (Error_Monad.catch_error
      (Parallel_Closed_Impl.check_parallel_closed Renaming2_String.string_rename
        r n)
      (\ x ->
        Sum_Type.Inl
          (((ia . Term_Rewriting.showsl_lit
                    ": error in checking parallel closedness for the ") .
             Term_Rewriting.showsl_trs r) .
            x)));
check_cr_proof a ia i j r (Development_Closed n) =
  FOR_Preliminaries.debug ia "Development Closed"
    (Error_Monad.catch_error
      (Development_Closed_Impl.check_development_closed
        Renaming2_String.string_rename r n)
      (\ x ->
        Sum_Type.Inl
          (((ia . Term_Rewriting.showsl_lit
                    ": error in checking development closedness for the ") .
             Term_Rewriting.showsl_trs r) .
            x)));
check_cr_proof a ia i j r (Sim_CPS_Closed hints) =
  FOR_Preliminaries.debug ia "Simultaneous CPS closed"
    (Error_Monad.catch_error
      (Okui_Criterion_Impl.check_sim_cps_closed RenamingN_String.string_renameN
        r hints)
      (\ x ->
        Sum_Type.Inl
          (((ia . Term_Rewriting.showsl_lit
                    ": error in checking simultaneous CP closedness for the ") .
             Term_Rewriting.showsl_trs r) .
            x)));
check_cr_proof a ia i j r (Critical_Pair_Closing_System c prf n) =
  FOR_Preliminaries.debug ia "Critical-Pair-Closing System"
    (let {
       tp = Termination_Problem_Spec.mk i False [] c [];
     } in Error_Monad.bind
            (Error_Monad.catch_error
              (Check_Termination.check_trs_termination_proof i j a
                (Term_Rewriting.add_index ia Arith.one_nat) tp prf)
              (\ x ->
                Sum_Type.Inl
                  ((ia . Term_Rewriting.showsl_lit
                           ": error below strong normalization of CPCS\n") .
                    x)))
            (\ _ ->
              Error_Monad.catch_error
                (Critical_Pair_Closure_Impl.check_critical_pair_closing
                  Renaming2_String.string_rename r c n)
                (\ x ->
                  Sum_Type.Inl
                    ((((ia . Term_Rewriting.showsl_lit
                               ": error when closing critical pairs of ") .
                        QDP_Framework_Impl.showsl_tp i tp) .
                       Term_Rewriting.showsl_literal "\n") .
                      x))));
check_cr_proof a ia i j r (Persistent_Decomposition sig ps) =
  FOR_Preliminaries.debug ia "Persistent Decomposition"
    (let {
       checks =
         map (Arith.map_prod id (\ prf iaa p -> check_cr_proof a iaa i j p prf))
           ps;
     } in Error_Monad.bind
            (Error_Monad.catch_error
              (Error_Monad.forallM
                (\ (n, (prf, f)) ->
                  Error_Monad.catch_error
                    (f (Term_Rewriting.add_index ia n) prf)
                    (\ x ->
                      Sum_Type.Inl
                        ((ia . Term_Rewriting.showsl_lit
                                 ": error while checking confluence of subproblems\n") .
                          x)))
                (Arith.enumerate Arith.one_nat checks))
              (\ x -> Sum_Type.Inl (snd x)))
            (\ _ ->
              Error_Monad.catch_error
                (LS_Persistence_Impl.check_persistence_cr sig r (map fst ps))
                (\ x ->
                  Sum_Type.Inl
                    (((ia . Term_Rewriting.showsl_lit
                              ": error in checking persistent decomposition of ") .
                       Term_Rewriting.showsl_trs r) .
                      x))));

check_ncr_proof ::
  forall a b c.
    (Compare.Compare_order b, Countable.Countable b, HOL.Default b, Eq b,
      Term_Rewriting.Showl b) => Bool ->
                                   (String -> String) ->
                                     Termination_Problem_Spec.Tp_ops_ext a
                                       (Labelings.Lab b [Arith.Nat])
                                       [Arith.Char] () ->
                                       Dependency_Pair_Problem_Spec.Dpp_ops_ext
 c (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
 [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
    Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
   Ncr_proof b [Arith.Nat] [Arith.Char] [Arith.Char] ->
     Sum_Type.Sum (String -> String) ();
check_ncr_proof a ia i j r (SN_NWCR prf) =
  FOR_Preliminaries.debug ia "SN_NWCR"
    (let {
       tp = Termination_Problem_Spec.mk i False [] r [];
     } in Error_Monad.bind
            (Error_Monad.catch_error
              (Check_Termination.check_trs_termination_proof i j a
                (Term_Rewriting.add_index ia Arith.one_nat) tp prf)
              (\ x ->
                Sum_Type.Inl
                  ((ia . Term_Rewriting.showsl_lit
                           ": error below strong normalization + wcr\n") .
                    x)))
            (\ _ ->
              Error_Monad.catch_error
                (Check_Monad.check
                  (not (Error_Monad.isOK
                         (Critical_Pairs_Impl.check_critical_pairs_NF r
                           (Critical_Pairs_Impl.critical_pairs_impl
                             Renaming2_String.string_rename r r))))
                  (Term_Rewriting.showsl_lit "all critical pairs are joinable"))
                (\ x ->
                  Sum_Type.Inl
                    ((((ia . Term_Rewriting.showsl_lit
                               ": error when disproving local confluence of ") .
                        QDP_Framework_Impl.showsl_tp i tp) .
                       Term_Rewriting.showsl_literal "\n") .
                      x))));
check_ncr_proof a ia i j r (Non_Join s seq1 seq2 prf) =
  FOR_Preliminaries.debug ia "Non_Join"
    (Error_Monad.catch_error
      (Non_Confluence_Impl.check_non_cr r s seq1 seq2 prf)
      (\ x ->
        Sum_Type.Inl
          ((((ia . Term_Rewriting.showsl_lit ": error when disproving CR of ") .
              Term_Rewriting.showsl_trs r) .
             Term_Rewriting.showsl_literal "\n") .
            x)));
check_ncr_proof a ia i j ra (NCR_Disj_Subtrs r prf) =
  FOR_Preliminaries.debug ia "Modularity"
    (Error_Monad.bind
      (Error_Monad.catch_error (Non_Confluence_Impl.check_modularity_ncr ra r)
        (\ x ->
          Sum_Type.Inl
            ((((ia . Term_Rewriting.showsl_lit
                       ": error when applying modularity to switch to ") .
                Term_Rewriting.showsl_trs r) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ _ ->
        Error_Monad.catch_error
          (check_ncr_proof a (Term_Rewriting.add_index ia Arith.one_nat) i j r
            prf)
          (\ x ->
            Sum_Type.Inl
              ((ia . Term_Rewriting.showsl_lit
                       ": error below the modular decomposition\n") .
                x))));
check_ncr_proof a ia i j r (NCR_Redundant_Rules rs n prf) =
  FOR_Preliminaries.debug ia "Redundant Rules"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (check_ncr_proof a (Term_Rewriting.add_index ia Arith.one_nat) i j rs
          prf)
        (\ x ->
          Sum_Type.Inl
            (((ia . Term_Rewriting.showsl_lit
                      ": error when proving nonconfluence of modified TRS\n") .
               Term_Rewriting.showsl_trs rs) .
              x)))
      (\ _ ->
        Error_Monad.catch_error
          (Redundant_Rules_Impl.check_redundant_rules_ncr r rs n)
          (\ x ->
            Sum_Type.Inl
              (((ia . Term_Rewriting.showsl_lit
                        ": error in checking redundant rules transformation of the TRS\n") .
                 Term_Rewriting.showsl_trs r) .
                x))));
check_ncr_proof a ia i j r (NCR_Rule_Removal r_del infos prf) =
  FOR_Preliminaries.debug ia "Rule Removal"
    (let {
       s = Missing_List.list_diff r r_del;
     } in Error_Monad.bind
            (Error_Monad.catch_error
              (check_ncr_proof a (Term_Rewriting.add_index ia Arith.one_nat) i j
                s prf)
              (\ x ->
                Sum_Type.Inl
                  ((((ia . Term_Rewriting.showsl_lit
                             ": error when proving nonconfluence of modified TRS\n") .
                      Term_Rewriting.showsl_trs s) .
                     Term_Rewriting.showsl_literal "\n") .
                    x)))
            (\ _ ->
              Error_Monad.catch_error
                (Non_Confluence_Impl.check_rule_removal infos r r_del s)
                (\ x ->
                  Sum_Type.Inl
                    ((((((ia . Term_Rewriting.showsl_lit
                                 ": error in checking rule removal on the TRS\n") .
                          Term_Rewriting.showsl_trs r) .
                         Term_Rewriting.showsl_lit "\nto switch to TRS\n") .
                        Term_Rewriting.showsl_trs s) .
                       Term_Rewriting.showsl_literal "\n") .
                      x))));
check_ncr_proof a ia i j r (NCR_Persistent_Decomposition sig s prf) =
  FOR_Preliminaries.debug ia "Persistent Decomposition"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (check_ncr_proof a (Term_Rewriting.add_index ia Arith.one_nat) i j s
          prf)
        (\ x ->
          Sum_Type.Inl
            (((ia . Term_Rewriting.showsl_lit
                      ": error while proving nonconfluence of resulting TRS\n") .
               Term_Rewriting.showsl_trs s) .
              x)))
      (\ _ ->
        Error_Monad.catch_error
          (LS_Persistence_Impl.check_persistence_not_cr sig r s)
          (\ x ->
            Sum_Type.Inl
              (((ia . Term_Rewriting.showsl_lit
                        ": error in checking persistent decomposition of ") .
                 Term_Rewriting.showsl_trs r) .
                x))));

default_grd_fun ::
  forall a.
    Term_Rewriting.Term (Labelings.Lab [Arith.Char] a) [Arith.Char] ->
      Term_Rewriting.Term (Labelings.Lab [Arith.Char] a) [Arith.Char] ->
        [Arith.Char] ->
          Term_Rewriting.Term (Labelings.Lab [Arith.Char] a) [Arith.Char];
default_grd_fun s t =
  let {
    f = Term_Rewriting.funs_rule_list (s, t);
    m = Arith.fold
          (\ fa m ->
            (case fa of {
              Labelings.Lab _ _ -> m;
              Labelings.FunLab _ _ -> m;
              Labelings.UnLab _ -> m;
              Labelings.Sharp (Labelings.Lab _ _) -> m;
              Labelings.Sharp (Labelings.FunLab _ _) -> m;
              Labelings.Sharp (Labelings.UnLab g) ->
                Quasi_Order.max (Arith.size_list g) m;
              Labelings.Sharp (Labelings.Sharp _) -> m;
            }))
          f Arith.zero_nat;
    suffix = Arith.replicate (Arith.suc m) Arith.char_0x61;
  } in (\ x ->
         Term_Rewriting.Fun (Labelings.Sharp (Labelings.UnLab (x ++ suffix)))
           []);

check_comm_proof ::
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
 [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
    Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
   [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
      Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
     Comm_proof b [Arith.Nat] [Arith.Char] ->
       Sum_Type.Sum (String -> String) ();
check_comm_proof ia j a i r s (Parallel_Closed_Comm n) =
  FOR_Preliminaries.debug i "Parallel_Closed_Comm"
    (Error_Monad.catch_error
      (Parallel_Closed_Impl.check_parallel_closed_comm
        Renaming2_String.string_rename r s n)
      (\ x ->
        Sum_Type.Inl
          ((i . Term_Rewriting.showsl_lit
                  ": error when proving commutation by almost parallel closed criterion\n") .
            x)));
check_comm_proof ia j a i r s (Development_Closed_Comm n) =
  FOR_Preliminaries.debug i "Development_Closed_Comm"
    (Error_Monad.catch_error
      (Development_Closed_Impl.check_development_closed_comm
        Renaming2_String.string_rename r s n)
      (\ x ->
        Sum_Type.Inl
          ((i . Term_Rewriting.showsl_lit
                  ": error when proving commutation by almost development closed criterion\n") .
            x)));
check_comm_proof ia j a i r s (Sim_CPS_Closed_Comm hints_cp) =
  FOR_Preliminaries.debug i "Sim_CPS_Closed_Comm"
    (Error_Monad.catch_error
      (Okui_Criterion_Impl.check_sim_cps_closed_comm
        RenamingN_String.string_renameN r s hints_cp)
      (\ x ->
        Sum_Type.Inl
          ((i . Term_Rewriting.showsl_lit
                  ": error when proving commutation by simultaneous critical pairs\n") .
            x)));
check_comm_proof ia j a i r s (PCP_Closed_Comm hints_cp hints_pcp) =
  FOR_Preliminaries.debug i "PCP_Closed_Comm"
    (Error_Monad.catch_error
      (Parallel_Critical_Pairs_Impl.check_parallel_critical_pairs_closed_comm
        RenamingN_String.string_renameN r s hints_cp hints_pcp)
      (\ x ->
        Sum_Type.Inl
          ((i . Term_Rewriting.showsl_lit
                  ": error when proving commutation by parallel critical pair closure criterion\n") .
            x)));
check_comm_proof ia j a i r s (PCP_Rule_Lab_Comm hints) =
  FOR_Preliminaries.debug i "PCP_Rule_Lab_Comm"
    (Error_Monad.catch_error
      (Parallel_Critical_Pairs_Impl.check_pcp_rule_lab_com
        RenamingN_String.string_renameN r s hints)
      (\ x ->
        Sum_Type.Inl
          ((i . Term_Rewriting.showsl_lit
                  ": error when proving commutation by rule labeling with parallel critical pairs\n") .
            x)));
check_comm_proof ia j a i r s (PCP_Compositional_Rule_Lab_Comm c d hints prf) =
  FOR_Preliminaries.debug i "Compositional PCP Rule Labeling"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Parallel_Critical_Pairs_Impl.check_compositional_pcp_rule_lab_comm
          RenamingN_String.string_renameN r s c d hints)
        (\ x ->
          Sum_Type.Inl
            ((i . Term_Rewriting.showsl_lit
                    ": error in checking compositional parallel critical pairs \n") .
              x)))
      (\ _ ->
        Error_Monad.catch_error
          (check_comm_proof ia j a (Term_Rewriting.add_index i Arith.one_nat) c
            d prf)
          (\ x ->
            Sum_Type.Inl
              (((((((i . Term_Rewriting.showsl_lit
                           ": error in proving commutation of sub TRS C\n") .
                     Term_Rewriting.showsl_trs c) .
                    Term_Rewriting.showsl_literal "\n") .
                   Term_Rewriting.showsl_lit " and sub TRS D of S\n") .
                  Term_Rewriting.showsl_trs d) .
                 Term_Rewriting.showsl_literal "\n") .
                x))));
check_comm_proof ia j a i r s
  (Compositional_PCPS_Comm c d p hintsP_RS hintsP_SR hintsRS hintsSR sn_prf
    com_prf)
  = FOR_Preliminaries.debug i "Compositional PCPS"
      (let {
         tp = Termination_Problem_Spec.mk ia False [] p
                (Arith.remdups (r ++ s));
       } in Error_Monad.bind
              (Error_Monad.catch_error
                (Parallel_Critical_Pairs_Impl.check_compositional_PCPS_com
                  RenamingN_String.string_renameN r s c d p hintsP_RS hintsP_SR
                  hintsRS hintsSR)
                (\ x ->
                  Sum_Type.Inl
                    (((((((i . Term_Rewriting.showsl_lit
                                 ": error in checking compositional parallel critical system to switch to TRSs C = \n") .
                           Term_Rewriting.showsl_trs c) .
                          Term_Rewriting.showsl_literal "\n") .
                         Term_Rewriting.showsl_lit " and D = \n") .
                        Term_Rewriting.showsl_trs d) .
                       Term_Rewriting.showsl_literal "\n") .
                      x)))
              (\ _ ->
                Error_Monad.bind
                  (Error_Monad.catch_error
                    (Check_Termination.check_trs_termination_proof ia j a
                      (Term_Rewriting.add_index i Arith.one_nat) tp sn_prf)
                    (\ x ->
                      Sum_Type.Inl
                        ((i . Term_Rewriting.showsl_lit
                                ": error below relative termination proof of compositional CPCS\n") .
                          x)))
                  (\ _ ->
                    Error_Monad.catch_error
                      (check_comm_proof ia j a
                        (Term_Rewriting.add_index i
                          (Arith.nat_of_integer (2 :: Integer)))
                        c d com_prf)
                      (\ x ->
                        Sum_Type.Inl
                          (((((i . Term_Rewriting.showsl_lit
                                     ": error in proving commutation of sub TRSs C and D\n") .
                               Term_Rewriting.showsl_trs c) .
                              Term_Rewriting.showsl_literal "\n") .
                             Term_Rewriting.showsl_trs d) .
                            x)))));
check_comm_proof ia j a i r s (Swap_Comm prf) =
  FOR_Preliminaries.debug i "Swap_Comm"
    (check_comm_proof ia j a (Term_Rewriting.add_index i Arith.one_nat) s r
      prf);
check_comm_proof ia j a i r s (CR_Proof prf) =
  FOR_Preliminaries.debug i "CR_proof"
    (Error_Monad.bind
      (Error_Monad.catch_error (Trs_Impl_More.check_variants_trs r s)
        (\ x ->
          Sum_Type.Inl
            (x . Term_Rewriting.showsl_lit "\nthe TRSs do not coincide")))
      (\ _ ->
        Error_Monad.bind
          (Error_Monad.catch_error (Trs_Impl_More.check_variants_trs s r)
            (\ x ->
              Sum_Type.Inl
                (x . Term_Rewriting.showsl_lit "\nthe TRSs do not coincide")))
          (\ _ ->
            check_cr_proof a (Term_Rewriting.add_index i Arith.one_nat) ia j r
              prf)));

check_ncomm_proof ::
  forall a.
    (Compare.Compare_order a, Countable.Countable a, HOL.Default a, Eq a,
      Term_Rewriting.Showl a) => (String -> String) ->
                                   [(Labelings.Lab a [Arith.Nat], Arith.Nat)] ->
                                     [(Term_Rewriting.Term
 (Labelings.Lab a [Arith.Nat]) [Arith.Char],
Term_Rewriting.Term (Labelings.Lab a [Arith.Nat]) [Arith.Char])] ->
                                       [(Term_Rewriting.Term
   (Labelings.Lab a [Arith.Nat]) [Arith.Char],
  Term_Rewriting.Term (Labelings.Lab a [Arith.Nat]) [Arith.Char])] ->
 Ncomm_proof a [Arith.Nat] [Arith.Char] [Arith.Char] ->
   Sum_Type.Sum (String -> String) ();
check_ncomm_proof i f r sa (Non_Join_Comm s seq1 seq2 prf) =
  FOR_Preliminaries.debug i "Non_Join"
    (Error_Monad.catch_error
      (Non_Commutation_Impl.check_non_commute (Arith.set f) r sa s seq1 seq2
        prf)
      (\ x ->
        Sum_Type.Inl
          ((((((((i . Term_Rewriting.showsl_lit
                        ": error when disproving commutation of R: ") .
                  Term_Rewriting.showsl_trs r) .
                 Term_Rewriting.showsl_literal "\n") .
                Term_Rewriting.showsl_lit "and S: ") .
               Term_Rewriting.showsl_literal "\n") .
              Term_Rewriting.showsl_trs sa) .
             Term_Rewriting.showsl_literal "\n") .
            x)));
check_ncomm_proof i f r s (Swap_Not_Comm prf) =
  FOR_Preliminaries.debug i "Swap_Not_Comm"
    (Error_Monad.catch_error
      (check_ncomm_proof (Term_Rewriting.add_index i Arith.one_nat) f s r prf)
      (\ x ->
        Sum_Type.Inl
          (((i . Term_Rewriting.showsl_lit ": error below swap TRSs") .
             Term_Rewriting.showsl_literal "\n") .
            x)));

}
