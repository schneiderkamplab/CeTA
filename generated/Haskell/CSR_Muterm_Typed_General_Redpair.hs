{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module CSR_Muterm_Typed_General_Redpair(muterm_general_rta08_ur_redpair_proc)
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
import qualified CSR_Muterm_Usable_Rules;
import qualified CSR_Minimal_CSDP_Proofs;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified HOL;
import qualified Dependency_Pair_Problem_Spec;
import qualified Sum_Type;
import qualified Labelings;
import qualified Arith;
import qualified Term_Rewriting;

muterm_general_rta08_ur_redpair_proc ::
  forall a b c.
    (Eq b, Term_Rewriting.Showl b, Eq c,
      Term_Rewriting.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a
                                   (Labelings.Lab b c) [Arith.Char] () ->
                                   [((Labelings.Lab b c, Arith.Nat),
                                      [Arith.Nat])] ->
                                     Term_Rewriting.Rel_impl_ext
                                       (Labelings.Lab b c) [Arith.Char] () ->
                                       [(Term_Rewriting.Term (Labelings.Lab b c)
   [Arith.Char],
  Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char])] ->
 [(Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char],
    Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char])] ->
   [(Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char],
      Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char])] ->
     a -> Sum_Type.Sum (String -> String) a;
muterm_general_rta08_ur_redpair_proc j mu rp premove u b dpp =
  (case (case Term_Rewriting.not_wst rp of {
          Nothing ->
            Sum_Type.Inl
              (Term_Rewriting.showsl_lit
                "general RTA\'08 MU-TERM reduction pair does not expose weak-subterm exceptions");
          Just f ->
            Error_Monad.bind (Term_Rewriting.rel_impl_redpair rp)
              (\ _ ->
                (case Dependency_Pair_Problem_Spec.split_pairs j dpp premove of
                  {
                  (ps, pns) ->
                    Error_Monad.bind
                      (Check_Monad.check
                        (CSR_Minimal_CSDP_Proofs.csr_rta08_usable_rules_check
                          (Dependency_Pair_Problem_Spec.rules j dpp) u mu
                          (Dependency_Pair_Problem_Spec.pairs j dpp))
                        (Term_Rewriting.showsl_lit
                          "general RTA\'08 MU-TERM usable-rule closure failed"))
                      (\ _ ->
                        Error_Monad.bind
                          (Check_Monad.check
                            (all (\ dp ->
                                   Term_Rewriting.is_Var (snd dp) ||
                                     CSR_Minimal_CSDP_Proofs.csr_u3_all_root_rules_check
                                       (Dependency_Pair_Problem_Spec.rules j
 dpp)
                                       u (snd dp))
                              (Dependency_Pair_Problem_Spec.pairs j dpp))
                            (Term_Rewriting.showsl_lit
                              "general RTA\'08 MU-TERM pair RHS closure failed"))
                          (\ _ ->
                            Error_Monad.bind
                              (Check_Monad.check
                                (all (\ lr ->
                                       CSR_Minimal_CSDP_Proofs.csr_u3_inactive_root_rules_check
 (Dependency_Pair_Problem_Spec.rules j dpp) u mu (fst lr))
                                  b)
                                (Term_Rewriting.showsl_lit
                                  "general RTA\'08 MU-TERM unhiding LHS closure failed"))
                              (\ _ ->
                                Error_Monad.bind
                                  (Check_Monad.check
                                    (all (\ lr ->
   CSR_Minimal_CSDP_Proofs.csr_u3_all_root_rules_check
     (Dependency_Pair_Problem_Spec.rules j dpp) u (snd lr))
                                      b)
                                    (Term_Rewriting.showsl_lit
                                      "general RTA\'08 MU-TERM unhiding RHS closure failed"))
                                  (\ _ ->
                                    Error_Monad.bind
                                      (Check_Monad.check
(CSR_Muterm_Usable_Rules.muterm_general_typed_shape_check
  (Dependency_Pair_Problem_Spec.pairs j dpp) b)
(Term_Rewriting.showsl_lit
  "general RTA\'08 MU-TERM typed pair or unhiding shape failed"))
                                      (\ _ ->
Error_Monad.bind
  (Check_Monad.check (CSR_Muterm_Usable_Rules.muterm_marked_mu_equal_check mu)
    (Term_Rewriting.showsl_lit
      "marked replacement-map entries differ from their source symbols"))
  (\ _ ->
    Error_Monad.bind (Term_Rewriting.ce_compat rp)
      (\ _ ->
        Error_Monad.bind
          (Error_Monad.catch_error
            (Term_Rewriting.rel_impl_ns rp
              (u ++ b ++ CSR_Minimal_CSDP_Proofs.csr_rta08_projection_rules_list
                           mu f ++
                           pns))
            (\ x ->
              Sum_Type.Inl
                (Term_Rewriting.showsl_lit
                   "problem weakly orienting general RTA\'08 MU-TERM rules, unhiding rules, projections, or pairs\n" .
                  x)))
          (\ _ ->
            Error_Monad.catch_error (Term_Rewriting.rel_impl_s rp ps)
              (\ x ->
                Sum_Type.Inl
                  (Term_Rewriting.showsl_lit
                     "problem strictly orienting general RTA\'08 MU-TERM pairs\n" .
                    x))))))))));
                }));
        })
    of {
    Sum_Type.Inl a -> Sum_Type.Inl a;
    Sum_Type.Inr _ ->
      Sum_Type.Inr
        (Dependency_Pair_Problem_Spec.delete_P_Pw j dpp premove premove);
  });

}
