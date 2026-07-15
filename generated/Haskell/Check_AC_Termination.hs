{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Check_AC_Termination(Ac_dp_termination_proof(..), Ac_termination_proof(..),
                        check_ac_termination_proof)
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
import qualified AC_Subterm_Criterion_Impl;
import qualified Dependency_Graph_Impl;
import qualified AC_Reduction_Pair_Processor_Impl;
import qualified FOR_Preliminaries;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Compare;
import qualified Mapping;
import qualified AC_Dependency_Pair_Problem_Spec;
import qualified HOL;
import qualified AC_Termination_Problem_Spec;
import qualified Arith;
import qualified AC_Dependency_Pairs_Impl;
import qualified Reduction_Pair_Implementations;
import qualified Labelings;
import qualified Term_Rewriting;

data Ac_dp_termination_proof a b = AC_P_is_Empty
  | AC_Subterm_Proc [((a, Arith.Nat), [Arith.Nat])]
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]
      (Ac_dp_termination_proof a b)
  | AC_Redpair_UR_Proc (Reduction_Pair_Implementations.Redtriple_impl a)
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]
      (Ac_dp_termination_proof a b)
  | AC_Mono_Redpair_UR_Proc (Reduction_Pair_Implementations.Redtriple_impl a)
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]
      (Ac_dp_termination_proof a b)
  | AC_Dep_Graph_Proc
      [(Maybe (Ac_dp_termination_proof a b),
         [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)])];

data Ac_termination_proof a b c =
  AC_DP_Trans
    (AC_Dependency_Pairs_Impl.Ac_dependency_pairs_proof (Labelings.Lab a b) c)
    (Ac_dp_termination_proof (Labelings.Lab a b) c)
    (Ac_dp_termination_proof (Labelings.Lab a b) c)
  | AC_DP_Trans_Single
      (AC_Dependency_Pairs_Impl.Ac_dependency_pairs_proof (Labelings.Lab a b) c)
      (Ac_dp_termination_proof (Labelings.Lab a b) c)
  | AC_Rule_Removal
      (Reduction_Pair_Implementations.Redtriple_impl (Labelings.Lab a b))
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Ac_termination_proof a b c)
  | AC_R_is_Empty;

showsl_ac_tp ::
  forall a b c.
    (Term_Rewriting.Showl b,
      Term_Rewriting.Showl c) => AC_Termination_Problem_Spec.Ac_tp_ops_ext a b c
                                   () ->
                                   a -> String -> String;
showsl_ac_tp i t =
  let {
    r = AC_Termination_Problem_Spec.r i t;
    a = AC_Termination_Problem_Spec.a i t;
    c = AC_Termination_Problem_Spec.c i t;
  } in (Term_Rewriting.showsl_trsa Term_Rewriting.showsl Term_Rewriting.showsl
          "rules:" " -> " r .
         (if null a then id
           else (Term_Rewriting.showsl_lit "A-symbols: " .
                  Term_Rewriting.showsl_lista a) .
                  Term_Rewriting.showsl_literal "\n")) .
         (if null c then id
           else (Term_Rewriting.showsl_lit "C-symbols: " .
                  Term_Rewriting.showsl_lista c) .
                  Term_Rewriting.showsl_literal "\n");

showsl_ac_dpp ::
  forall a b c.
    (Term_Rewriting.Showl b,
      Term_Rewriting.Showl c) => AC_Dependency_Pair_Problem_Spec.Ac_dpp_ops_ext
                                   a b c () ->
                                   a -> String -> String;
showsl_ac_dpp i d =
  let {
    p = AC_Dependency_Pair_Problem_Spec.p i d;
    pw = AC_Dependency_Pair_Problem_Spec.pw i d;
    r = AC_Dependency_Pair_Problem_Spec.r i d;
    rw = AC_Dependency_Pair_Problem_Spec.rw i d;
    e = AC_Dependency_Pair_Problem_Spec.e i d;
  } in ((((if null p then id
            else Term_Rewriting.showsl_trsa Term_Rewriting.showsl
                   Term_Rewriting.showsl "pairs:" " -> " p) .
           (if null pw then id
             else Term_Rewriting.showsl_trsa Term_Rewriting.showsl
                    Term_Rewriting.showsl "weak pairs:" " ->= " pw)) .
          (if null r then id
            else Term_Rewriting.showsl_trsa Term_Rewriting.showsl
                   Term_Rewriting.showsl "strict rules:" " ->! " r)) .
         (if null rw then id
           else Term_Rewriting.showsl_trsa Term_Rewriting.showsl
                  Term_Rewriting.showsl "rules:" " -> " rw)) .
         (if null e then id
           else Term_Rewriting.showsl_trsa Term_Rewriting.showsl
                  Term_Rewriting.showsl "equations:" " -> " e);

check_ac_dp_termination_proof ::
  forall a b.
    (Arith.Cenum b, Arith.Ceq b, Arith.Ccompare b, Compare.Compare_order b,
      Eq b, Mapping.Mapping_impl b, Arith.Set_impl b,
      Term_Rewriting.Showl b) => AC_Dependency_Pair_Problem_Spec.Ac_dpp_ops_ext
                                   a b [Arith.Char] () ->
                                   (String -> String) ->
                                     a -> Ac_dp_termination_proof b
    [Arith.Char] ->
    Sum_Type.Sum (String -> String) ();
check_ac_dp_termination_proof ia i dpp AC_P_is_Empty =
  FOR_Preliminaries.debug i "P is empty"
    (Error_Monad.catch_error
      (AC_Dependency_Pair_Problem_Spec.ac_dpp_trivial_check ia dpp)
      (\ x ->
        Sum_Type.Inl
          (((i . Term_Rewriting.showsl_lit
                   "problem in applying trivial check on\n") .
             showsl_ac_dpp ia dpp) .
            x)));
check_ac_dp_termination_proof ia i dpp (AC_Redpair_UR_Proc redp del_p ur prf) =
  FOR_Preliminaries.debug i "AC_Redpair_UR_Proc"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (AC_Reduction_Pair_Processor_Impl.ac_ur_redpair_proc ia
          (Reduction_Pair_Implementations.get_rel_impl redp) del_p ur dpp)
        (\ x ->
          Sum_Type.Inl
            ((((((i . Term_Rewriting.showsl_lit
                        ": error when applying AC-reduction pair processor to DP problem\n") .
                  showsl_ac_dpp ia dpp) .
                 Term_Rewriting.showsl_lit "\nand trying to remove pairs\n") .
                Term_Rewriting.showsl_rules del_p) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ dppa ->
        Error_Monad.catch_error
          (check_ac_dp_termination_proof ia
            (Term_Rewriting.add_index i Arith.one_nat) dppa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below AC-reduction pair processor\n") .
                x))));
check_ac_dp_termination_proof ia i dpp (AC_Subterm_Proc pi del_p prf) =
  FOR_Preliminaries.debug i "AC_Subterm_Proc"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (AC_Subterm_Criterion_Impl.ac_subterm_proc ia pi del_p dpp)
        (\ x ->
          Sum_Type.Inl
            ((((((i . Term_Rewriting.showsl_lit
                        ": error when applying AC-subterm criterion processor to DP problem\n") .
                  showsl_ac_dpp ia dpp) .
                 Term_Rewriting.showsl_lit "\nand trying to remove pairs\n") .
                Term_Rewriting.showsl_rules del_p) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ dppa ->
        Error_Monad.catch_error
          (check_ac_dp_termination_proof ia
            (Term_Rewriting.add_index i Arith.one_nat) dppa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below AC-reduction pair processor\n") .
                x))));
check_ac_dp_termination_proof ia i dpp
  (AC_Mono_Redpair_UR_Proc redp del_p del_r ur prf) =
  FOR_Preliminaries.debug i "AC_Mono_Redpair_UR_Proc"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (AC_Reduction_Pair_Processor_Impl.ac_mono_ur_redpair_proc ia
          (Reduction_Pair_Implementations.get_rel_impl redp) del_p del_r ur dpp)
        (\ x ->
          Sum_Type.Inl
            ((((((((i . Term_Rewriting.showsl_lit
                          ": error when applying monotone AC-reduction pair processor to DP problem\n") .
                    showsl_ac_dpp ia dpp) .
                   Term_Rewriting.showsl_lit "\nand trying to remove pairs\n") .
                  Term_Rewriting.showsl_rules del_p) .
                 Term_Rewriting.showsl_lit "\nand rules\n") .
                Term_Rewriting.showsl_rules del_r) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ dppa ->
        Error_Monad.catch_error
          (check_ac_dp_termination_proof ia
            (Term_Rewriting.add_index i Arith.one_nat) dppa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below monotone AC-reduction pair processor\n") .
                x))));
check_ac_dp_termination_proof ia i dpp (AC_Dep_Graph_Proc edpts) =
  FOR_Preliminaries.debug i "Dep_Graph_Proc"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Dependency_Graph_Impl.ac_dep_graph_proc ia dpp edpts)
        (\ x ->
          Sum_Type.Inl
            ((((i . Term_Rewriting.showsl_lit
                      ": error while trying to perform Sctxt_closure-decomposition  on\n") .
                showsl_ac_dpp ia dpp) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ pdpps ->
        Error_Monad.catch_error
          (Error_Monad.catch_error
            (Error_Monad.forallM_index
              (\ (prof, dppa) j ->
                check_ac_dp_termination_proof ia
                  (Term_Rewriting.add_index i (Arith.suc j)) dppa prof)
              pdpps)
            (\ x -> Sum_Type.Inl (snd x)))
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below the dependency graph processor\n") .
                x))));

check_ac_termination_proof ::
  forall a b c d.
    (Compare.Compare_order b, Eq b, Term_Rewriting.Showl b,
      Compare.Compare_order c, Eq c,
      Term_Rewriting.Showl c) => AC_Dependency_Pair_Problem_Spec.Ac_dpp_ops_ext
                                   a (Labelings.Lab b c) [Arith.Char] () ->
                                   AC_Termination_Problem_Spec.Ac_tp_ops_ext d
                                     (Labelings.Lab b c) [Arith.Char] () ->
                                     (String -> String) ->
                                       d ->
 Ac_termination_proof b c [Arith.Char] -> Sum_Type.Sum (String -> String) ();
check_ac_termination_proof ia j i tp (AC_DP_Trans info prf1 prf2) =
  FOR_Preliminaries.debug i "AC Dependency Pairs"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (AC_Dependency_Pairs_Impl.ac_dependency_pairs_proc j ia Labelings.Sharp
          [Arith.char_0x78] [Arith.char_0x79] [Arith.char_0x7A] info tp)
        (\ x ->
          Sum_Type.Inl
            (((i . Term_Rewriting.showsl_lit
                     ": error when applying AC-dependency pair processor to\n") .
               showsl_ac_tp j tp) .
              x)))
      (\ (dp1, dp2) ->
        Error_Monad.bind
          (Error_Monad.catch_error
            (check_ac_dp_termination_proof ia
              (Term_Rewriting.add_index i Arith.one_nat) dp1 prf1)
            (\ x ->
              Sum_Type.Inl
                ((i . Term_Rewriting.showsl_lit
                        ": error below AC-dependency pair processor\n") .
                  x)))
          (\ _ ->
            Error_Monad.catch_error
              (check_ac_dp_termination_proof ia
                (Term_Rewriting.add_index i
                  (Arith.nat_of_integer (2 :: Integer)))
                dp2 prf2)
              (\ x ->
                Sum_Type.Inl
                  ((i . Term_Rewriting.showsl_lit
                          ": error below AC-dependency pair processor\n") .
                    x)))));
check_ac_termination_proof ia j i tp (AC_DP_Trans_Single info prf1) =
  FOR_Preliminaries.debug i "AC Dependency Pairs"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (AC_Dependency_Pairs_Impl.ac_dependency_pairs_proc_simple j ia
          Labelings.Sharp [Arith.char_0x78] [Arith.char_0x79] [Arith.char_0x7A]
          info tp)
        (\ x ->
          Sum_Type.Inl
            (((i . Term_Rewriting.showsl_lit
                     ": error when applying AC-dependency pair processor to\n") .
               showsl_ac_tp j tp) .
              x)))
      (\ dp1 ->
        Error_Monad.catch_error
          (check_ac_dp_termination_proof ia
            (Term_Rewriting.add_index i Arith.one_nat) dp1 prf1)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below AC-dependency pair processor\n") .
                x))));
check_ac_termination_proof ia j i tp (AC_Rule_Removal redp del_r prf) =
  FOR_Preliminaries.debug i "AC_Mono_Redpair_UR_Proc"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (AC_Reduction_Pair_Processor_Impl.ac_rule_removal j
          (Reduction_Pair_Implementations.get_rel_impl redp) del_r tp)
        (\ x ->
          Sum_Type.Inl
            ((((((i . Term_Rewriting.showsl_lit
                        ": error when applying AC rule removal to AC termination problem\n") .
                  showsl_ac_tp j tp) .
                 Term_Rewriting.showsl_lit "\ntrying to remove rules\n") .
                Term_Rewriting.showsl_rules del_r) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ tpa ->
        Error_Monad.catch_error
          (check_ac_termination_proof ia j
            (Term_Rewriting.add_index i Arith.one_nat) tpa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below AC rule removal\n") .
                x))));
check_ac_termination_proof ia j i tp AC_R_is_Empty =
  FOR_Preliminaries.debug i "AC_R_is_Empty"
    (Error_Monad.catch_error
      (Check_Monad.check (null (AC_Termination_Problem_Spec.r j tp))
        (Term_Rewriting.showsl_lit "The TRS is not empty"))
      (\ x ->
        Sum_Type.Inl
          ((((i . Term_Rewriting.showsl_lit
                    ": error when applying the R-is-Empty check on the AC termination problem\n") .
              showsl_ac_tp j tp) .
             Term_Rewriting.showsl_literal "\n") .
            x)));

}
