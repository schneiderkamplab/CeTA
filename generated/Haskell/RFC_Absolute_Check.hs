{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module RFC_Absolute_Check(check_rfc_absolute) where {

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
import qualified RFC_Absolute_Residual;
import qualified Error_Monad;
import qualified Dependency_Pair_Problem_Spec;
import qualified Monadic_Rewriting_Impl;
import qualified Reduction_Pair_Implementations;
import qualified Check_Termination_Common;
import qualified Termination_Problem_Spec;
import qualified Semantic_Labeling_Carrier;
import qualified Check_Termination;
import qualified Critical_Pairs_Impl;
import qualified Matchbounds_Impl;
import qualified Sum_Type;
import qualified Countable;
import qualified Compare;
import qualified Labelings;
import qualified Mapping;
import qualified Compare_Order_Instances;
import qualified Term_Rewriting;
import qualified Arith;

check_rfc_absolute ::
  forall a b c.
    (Compare.Compare_order b, Countable.Countable b, Eq b,
      Term_Rewriting.Showl b) => Termination_Problem_Spec.Tp_ops_ext a
                                   (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                   () ->
                                   Dependency_Pair_Problem_Spec.Dpp_ops_ext c
                                     (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                     () ->
                                     (String -> String) ->
                                       a ->
 Check_Termination.Trs_termination_proof b [Arith.Nat] [Arith.Char] ->
   Sum_Type.Sum (String -> String) ();
check_rfc_absolute ia j i tp
  (Check_Termination.Rfc_Matchbox_Relative_Bounds info initial d child) =
  Error_Monad.bind
    (RFC_Absolute_Residual.rfc_matchbox_absolute_bounds_tt ia info initial d tp)
    (\ tpa ->
      check_rfc_absolute ia j (Term_Rewriting.add_index i Arith.one_nat) tpa
        child);
check_rfc_absolute ia j i tp (Check_Termination.DP_Trans v va vb vc) =
  Check_Termination.check_trs_termination_proof ia j False i tp
    (Check_Termination.DP_Trans v va vb vc);
check_rfc_absolute ia j i tp (Check_Termination.Rule_Removal v va vb) =
  Check_Termination.check_trs_termination_proof ia j False i tp
    (Check_Termination.Rule_Removal v va vb);
check_rfc_absolute ia j i tp (Check_Termination.String_Reversal v) =
  Check_Termination.check_trs_termination_proof ia j False i tp
    (Check_Termination.String_Reversal v);
check_rfc_absolute ia j i tp (Check_Termination.Constant_String v va) =
  Check_Termination.check_trs_termination_proof ia j False i tp
    (Check_Termination.Constant_String v va);
check_rfc_absolute ia j i tp (Check_Termination.Bounds v) =
  Check_Termination.check_trs_termination_proof ia j False i tp
    (Check_Termination.Bounds v);
check_rfc_absolute ia j i tp (Check_Termination.Relative_Bounds v va vb) =
  Check_Termination.check_trs_termination_proof ia j False i tp
    (Check_Termination.Relative_Bounds v va vb);
check_rfc_absolute ia j i tp (Check_Termination.Rfc_Bounds v va) =
  Check_Termination.check_trs_termination_proof ia j False i tp
    (Check_Termination.Rfc_Bounds v va);
check_rfc_absolute ia j i tp
  (Check_Termination.Rfc_Automaton_Closed_Bounds v va) =
  Check_Termination.check_trs_termination_proof ia j False i tp
    (Check_Termination.Rfc_Automaton_Closed_Bounds v va);
check_rfc_absolute ia j i tp (Check_Termination.Rfc_Relative_Bounds v va vb vc)
  = Check_Termination.check_trs_termination_proof ia j False i tp
      (Check_Termination.Rfc_Relative_Bounds v va vb vc);
check_rfc_absolute ia j i tp
  (Check_Termination.Rfc_Automaton_Closed_Relative_Bounds v va vb vc) =
  Check_Termination.check_trs_termination_proof ia j False i tp
    (Check_Termination.Rfc_Automaton_Closed_Relative_Bounds v va vb vc);
check_rfc_absolute ia j i tp (Check_Termination.Uncurry v va vb) =
  Check_Termination.check_trs_termination_proof ia j False i tp
    (Check_Termination.Uncurry v va vb);
check_rfc_absolute ia j i tp (Check_Termination.Semlab v va vb vc) =
  Check_Termination.check_trs_termination_proof ia j False i tp
    (Check_Termination.Semlab v va vb vc);
check_rfc_absolute ia j i tp Check_Termination.R_is_Empty =
  Check_Termination.check_trs_termination_proof ia j False i tp
    Check_Termination.R_is_Empty;
check_rfc_absolute ia j i tp (Check_Termination.Fcc v va vb) =
  Check_Termination.check_trs_termination_proof ia j False i tp
    (Check_Termination.Fcc v va vb);
check_rfc_absolute ia j i tp (Check_Termination.Split v va vb) =
  Check_Termination.check_trs_termination_proof ia j False i tp
    (Check_Termination.Split v va vb);
check_rfc_absolute ia j i tp (Check_Termination.Switch_Innermost v va) =
  Check_Termination.check_trs_termination_proof ia j False i tp
    (Check_Termination.Switch_Innermost v va);
check_rfc_absolute ia j i tp (Check_Termination.Drop_Equality v) =
  Check_Termination.check_trs_termination_proof ia j False i tp
    (Check_Termination.Drop_Equality v);
check_rfc_absolute ia j i tp (Check_Termination.Remove_Nonapplicable_Rules v va)
  = Check_Termination.check_trs_termination_proof ia j False i tp
      (Check_Termination.Remove_Nonapplicable_Rules v va);
check_rfc_absolute ia j i tp (Check_Termination.Permuting_AFS v va) =
  Check_Termination.check_trs_termination_proof ia j False i tp
    (Check_Termination.Permuting_AFS v va);
check_rfc_absolute ia j i tp Check_Termination.Right_Ground_Termination =
  Check_Termination.check_trs_termination_proof ia j False i tp
    Check_Termination.Right_Ground_Termination;
check_rfc_absolute ia j i tp (Check_Termination.Assume_SN v va) =
  Check_Termination.check_trs_termination_proof ia j False i tp
    (Check_Termination.Assume_SN v va);
check_rfc_absolute ia j i tp
  (Check_Termination.Rfc_Native_Matchbox_Relative_Bounds v va vb vc) =
  Check_Termination.check_trs_termination_proof ia j False i tp
    (Check_Termination.Rfc_Native_Matchbox_Relative_Bounds v va vb vc);
check_rfc_absolute ia j i tp (Check_Termination.AAECC_Innermost v va vb vc vd) =
  Check_Termination.check_trs_termination_proof ia j False i tp
    (Check_Termination.AAECC_Innermost v va vb vc vd);

}
