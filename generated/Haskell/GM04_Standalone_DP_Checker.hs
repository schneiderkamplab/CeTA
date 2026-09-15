{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  GM04_Standalone_DP_Checker(Gm04_standalone_dp_proof(..),
                              check_gm04_standalone_dp_proof,
                              check_gm04_standalone_trs_proof)
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
import qualified GM04_Complete_Transformation;
import qualified GM04_Complete_Checker;
import qualified Context_Sensitive_Impl;
import qualified FOR_Preliminaries;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified HOL;
import qualified Termination_Problem_Spec;
import qualified Sum_Type;
import qualified Countable;
import qualified Compare;
import qualified Mapping;
import qualified Compare_Order_Instances;
import qualified Check_Termination_Common;
import qualified Dependency_Pair_Problem_Spec;
import qualified CSR_GM_Transformation;
import qualified Check_Termination;
import qualified Labelings;
import qualified Term_Rewriting;
import qualified Arith;

data Gm04_standalone_dp_proof a b c =
  GM04_Standalone_DP_Proof [(Labelings.Lab a b, Arith.Nat)]
    [((Labelings.Lab a b, Arith.Nat), [Arith.Nat])]
    [(Term_Rewriting.Term (Labelings.Lab a b) c,
       Term_Rewriting.Term (Labelings.Lab a b) c)]
    (Labelings.Lab a b) (Labelings.Lab a b) (Labelings.Lab a b)
    (Labelings.Lab a b) (Labelings.Lab a b) (Labelings.Lab a b)
    (Check_Termination.Dp_termination_proof a b c)
    (CSR_GM_Transformation.Gm_extended_csr_termination_proof a b c);

gm04_mk_dpp ::
  forall a b c d.
    Dependency_Pair_Problem_Spec.Dpp_ops_ext a b c d ->
      (Bool,
        (Bool,
          ([(Term_Rewriting.Term b c, Term_Rewriting.Term b c)],
            ([(Term_Rewriting.Term b c, Term_Rewriting.Term b c)],
              ([Term_Rewriting.Term b c],
                ([(Term_Rewriting.Term b c, Term_Rewriting.Term b c)],
                  [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)])))))) ->
        a;
gm04_mk_dpp j (nfs, (m, (p, (pw, (q, (r, rw)))))) =
  Dependency_Pair_Problem_Spec.mk j nfs m p pw q r rw;

gm04_single_dp_assumption ::
  forall a b c.
    [Check_Termination_Common.Assm a b c] ->
      Maybe (Bool,
              (Bool,
                ([(Term_Rewriting.Term (Labelings.Lab a b) c,
                    Term_Rewriting.Term (Labelings.Lab a b) c)],
                  ([(Term_Rewriting.Term (Labelings.Lab a b) c,
                      Term_Rewriting.Term (Labelings.Lab a b) c)],
                    ([Term_Rewriting.Term (Labelings.Lab a b) c],
                      ([(Term_Rewriting.Term (Labelings.Lab a b) c,
                          Term_Rewriting.Term (Labelings.Lab a b) c)],
                        [(Term_Rewriting.Term (Labelings.Lab a b) c,
                           Term_Rewriting.Term (Labelings.Lab a b) c)]))))));
gm04_single_dp_assumption [Check_Termination_Common.Finite_assm [] d] = Just d;
gm04_single_dp_assumption [] = Nothing;
gm04_single_dp_assumption (Check_Termination_Common.SN_assm vb vc : va) =
  Nothing;
gm04_single_dp_assumption (Check_Termination_Common.SN_FP_assm vb vc : va) =
  Nothing;
gm04_single_dp_assumption
  (Check_Termination_Common.Finite_assm (vd : ve) vc : va) = Nothing;
gm04_single_dp_assumption (Check_Termination_Common.Unknown_assm vb vc : va) =
  Nothing;
gm04_single_dp_assumption (Check_Termination_Common.Not_SN_assm vb vc : va) =
  Nothing;
gm04_single_dp_assumption (Check_Termination_Common.Not_RelSN_assm vb vc : va) =
  Nothing;
gm04_single_dp_assumption (Check_Termination_Common.Not_SN_FP_assm vb vc : va) =
  Nothing;
gm04_single_dp_assumption (Check_Termination_Common.Infinite_assm vb vc : va) =
  Nothing;
gm04_single_dp_assumption (Check_Termination_Common.Complexity_assm vb vc : va)
  = Nothing;
gm04_single_dp_assumption (v : vb : vc) = Nothing;

check_gm04_standalone_dp_proof ::
  forall a b c.
    (Compare.Compare_order b, Countable.Countable b, Eq b,
      Term_Rewriting.Showl b) => Termination_Problem_Spec.Tp_ops_ext a
                                   (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                   () ->
                                   Dependency_Pair_Problem_Spec.Dpp_ops_ext c
                                     (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                     () ->
                                     (String -> String) ->
                                       c ->
 Gm04_standalone_dp_proof b [Arith.Nat] [Arith.Char] ->
   Sum_Type.Sum (String -> String) ();
check_gm04_standalone_dp_proof ia j i dpp
  (GM04_Standalone_DP_Proof f mu r active mark proper ok top_sym top_sharp child
    source_child)
  = FOR_Preliminaries.debug i
      "standalone Giesl-Middeldorp residual with CSR child"
      (Error_Monad.bind (Term_Rewriting.check_wf_trs r)
        (\ _ ->
          Error_Monad.bind
            (Check_Monad.check
              (Arith.superset f (Term_Rewriting.funas_trs_list r))
              (Term_Rewriting.showsl_lit "source signature is incomplete"))
            (\ _ ->
              Error_Monad.bind
                (Check_Monad.check
                  (Arith.set_eq (Arith.set f)
                     (Arith.set (Term_Rewriting.funas_trs_list r)) ||
                    GM04_Complete_Checker.gm04_source_proof_is_global
                      source_child)
                  (Term_Rewriting.showsl_lit
                    "extended signature requires a global source proof"))
                (\ _ ->
                  Error_Monad.bind
                    (Check_Monad.check
                      (GM04_Complete_Checker.gm04_roles_fresh_list active mark
                        proper ok top_sym f)
                      (Term_Rewriting.showsl_lit
                        "GM04 administrative roles are not fresh"))
                    (\ _ ->
                      let {
                        s = GM04_Complete_Transformation.gm04_non_top_rules
                              (Context_Sensitive_Impl.mu_of mu) active mark
                              proper ok f r;
                        p = GM04_Complete_Transformation.gm04_top_pairs active
                              mark proper ok top_sharp;
                      } in Error_Monad.bind
                             (Check_Monad.check
                               (GM04_Complete_Checker.gm04_schema_signature_list
                                 active mark proper ok f s)
                               (Term_Rewriting.showsl_lit
                                 "GM04 non-top signature is invalid"))
                             (\ _ ->
                               Error_Monad.bind
                                 (Check_Monad.check
                                   (GM04_Complete_Checker.gm04_pair_args_signature_list
                                     top_sharp p s)
                                   (Term_Rewriting.showsl_lit
                                     "GM04 pair arguments escape the signature"))
                                 (\ _ ->
                                   Error_Monad.bind
                                     (Check_Monad.check
                                       (all
 (\ (fa, _) -> not (Labelings.equal_lab fa top_sharp))
 (Term_Rewriting.funas_trs_list s))
                                       (Term_Rewriting.showsl_lit
 "GM04 sharp role is not fresh"))
                                     (\ _ ->
                                       Error_Monad.bind
 (CSR_GM_Transformation.check_gm_extended_csr_termination_proof ia j False
   (Term_Rewriting.add_index i Arith.one_nat) mu r source_child)
 (\ _ ->
   Error_Monad.bind
     (Check_Termination.check_dp_termination_proof ia j True
       (Term_Rewriting.add_index i (Arith.nat_of_integer (2 :: Integer))) dpp
       child)
     (\ _ ->
       Check_Monad.check
         (GM04_Complete_Checker.gm04_residual_assm p s (map fst s)
           (Check_Termination.dp_assms True child))
         (Term_Rewriting.showsl_lit
           "DP proof does not have exactly the certified GM04 premise")))))))))));

check_gm04_standalone_trs_proof ::
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
 Gm04_standalone_dp_proof b [Arith.Nat] [Arith.Char] ->
   Check_Termination.Trs_termination_proof b [Arith.Nat] [Arith.Char] ->
     Sum_Type.Sum (String -> String) ();
check_gm04_standalone_trs_proof ia j i tp context child =
  (case gm04_single_dp_assumption (Check_Termination.sn_assms True child) of {
    Nothing ->
      Sum_Type.Inl
        (Term_Rewriting.showsl_lit
          "expected one unconditional GM04 DP premise");
    Just d ->
      Error_Monad.bind
        (check_gm04_standalone_dp_proof ia j
          (Term_Rewriting.add_index i Arith.one_nat) (gm04_mk_dpp j d) context)
        (\ _ ->
          Check_Termination.check_trs_termination_proof ia j True
            (Term_Rewriting.add_index i (Arith.nat_of_integer (2 :: Integer)))
            tp child);
  });

}
