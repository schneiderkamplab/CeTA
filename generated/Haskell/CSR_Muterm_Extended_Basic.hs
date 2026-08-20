{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module CSR_Muterm_Extended_Basic(muterm_extended_basic_redpair_proc) where {

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
import qualified CSR_Checker_Base;
import qualified CSR_Muterm_Usable_Rules;
import qualified CSR_Minimal_CSDP_Proofs;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified HOL;
import qualified Dependency_Pair_Problem_Spec;
import qualified Sum_Type;
import qualified Arith;
import qualified Term_Rewriting;
import qualified Labelings;

muterm_extended_basic_side_conditions_check ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Arith.Card_UNIV b, Arith.Ceq b,
      Arith.Cproper_interval b, Eq b, Arith.Set_impl b,
      Term_Rewriting.Showl b) => [((a, Arith.Nat), [Arith.Nat])] ->
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)] ->
                                     [(Term_Rewriting.Term a b,
Term_Rewriting.Term a b)] ->
                                       Sum_Type.Sum (String -> String) ();
muterm_extended_basic_side_conditions_check mu p u =
  Error_Monad.bind
    (Check_Monad.check (all ((\ t -> not (Term_Rewriting.is_Var t)) . snd) p)
      (Term_Rewriting.showsl_lit
        "extended-basic processor requires non-collapsing pairs"))
    (\ _ ->
      Error_Monad.bind (Term_Rewriting.check_left_linear_trs (p ++ u))
        (\ _ ->
          Error_Monad.bind
            (Check_Monad.check
              (CSR_Checker_Base.rhs_mu_vars_condition_list mu (p ++ u))
              (Term_Rewriting.showsl_lit
                "extended-basic conservativity condition failed"))
            (\ _ ->
              Check_Monad.check
                (all (\ (l, _) ->
                       Arith.is_empty
                         (Arith.inf_set
                           (Arith.set (CSR_Checker_Base.mu_vars_term_list mu l))
                           (Arith.set
                             (CSR_Muterm_Usable_Rules.non_mu_vars_term_list mu
                               l))))
                  (p ++ u))
                (Term_Rewriting.showsl_lit
                  "extended-basic left-hand-side activity partition failed"))));

muterm_extended_basic_ur_closed_check ::
  forall a b c.
    (Eq a, Eq b,
      Eq c) => [(Term_Rewriting.Term a b, Term_Rewriting.Term a c)] ->
                 [(Term_Rewriting.Term a b, Term_Rewriting.Term a c)] ->
                   [((a, Arith.Nat), [Arith.Nat])] ->
                     [(Term_Rewriting.Term a b, Term_Rewriting.Term a c)] ->
                       [(Term_Rewriting.Term a b, Term_Rewriting.Term a c)] ->
                         Bool;
muterm_extended_basic_ur_closed_check r u mu p b =
  all (Arith.membera r) u &&
    all (\ lr ->
          CSR_Minimal_CSDP_Proofs.csr_rta08_active_root_rules_check r u mu
            (snd lr))
      (CSR_Muterm_Usable_Rules.muterm_extended_basic_seed_list p b u);

muterm_extended_basic_redpair_proc ::
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
muterm_extended_basic_redpair_proc j mu rp premove u dpp =
  (case Error_Monad.bind (Term_Rewriting.rel_impl_redpair rp)
          (\ _ ->
            (case Dependency_Pair_Problem_Spec.split_pairs j dpp premove of {
              (ps, pns) ->
                Error_Monad.bind
                  (Check_Monad.check
                    (CSR_Minimal_CSDP_Proofs.csr_sharp_pairs_check
                      (Dependency_Pair_Problem_Spec.pairs j dpp))
                    (Term_Rewriting.showsl_lit
                      "extended-basic processor requires marked pairs"))
                  (\ _ ->
                    Error_Monad.bind
                      (Check_Monad.check
                        (CSR_Muterm_Usable_Rules.muterm_marked_mu_pairs_check mu
                          (Dependency_Pair_Problem_Spec.pairs j dpp))
                        (Term_Rewriting.showsl_lit
                          "marked replacement-map entries differ from their source symbols"))
                      (\ _ ->
                        Error_Monad.bind
                          (Check_Monad.check
                            (muterm_extended_basic_ur_closed_check
                              (Dependency_Pair_Problem_Spec.rules j dpp) u mu
                              (Dependency_Pair_Problem_Spec.pairs j dpp) [])
                            (Term_Rewriting.showsl_lit
                              "supplied rules are not a closed extended-basic set"))
                          (\ _ ->
                            Error_Monad.bind
                              (muterm_extended_basic_side_conditions_check mu
                                (Dependency_Pair_Problem_Spec.pairs j dpp) u)
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

}
