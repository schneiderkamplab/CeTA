{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  GM04_Complete_Checker(Gm04_complete_nontermination_proof(..),
                         Gm04_complete_transformation_proof(..),
                         check_gm04_complete_nontermination_proof,
                         check_gm04_complete_transformation_proof)
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
import qualified Dependency_Pair_Problem_Spec;
import qualified Termination_Problem_Spec;
import qualified Phantom_Type;
import qualified Compare_Order_Instances;
import qualified GM04_Complete_Transformation;
import qualified Trs_Impl_More;
import qualified CSR_Check_Loops;
import qualified Context_Sensitive_Impl;
import qualified FOR_Preliminaries;
import qualified Check_Monad;
import qualified HOL;
import qualified Countable;
import qualified CSR_Conservative_Checker;
import qualified CSR_Guarded_List_Checker;
import qualified CSR_Muterm_Usable_Rules;
import qualified CSR_Checker_Base;
import qualified Q_Restricted_Rewriting_Impl;
import qualified Error_Monad;
import qualified Check_Termination_Common;
import qualified Sum_Type;
import qualified Mapping;
import qualified Compare;
import qualified CSR_GM_Transformation;
import qualified Check_Termination;
import qualified Critical_Pairs_Impl;
import qualified Loops_Impl;
import qualified Labelings;
import qualified Term_Rewriting;
import qualified Arith;

data Gm04_complete_nontermination_proof a b c =
  GM04_Complete_Nontermination_Proof
    [((Labelings.Lab a b, Arith.Nat), [Arith.Nat])]
    [(Term_Rewriting.Term (Labelings.Lab a b) c,
       Term_Rewriting.Term (Labelings.Lab a b) c)]
    (Labelings.Lab a b) (Labelings.Lab a b) (Labelings.Lab a b)
    (Labelings.Lab a b) (Labelings.Lab a b)
    (Loops_Impl.Trs_loop_prf (Labelings.Lab a b) c);

data Gm04_complete_transformation_proof a b c =
  GM04_Complete_Transformation_Proof
    [((Labelings.Lab a b, Arith.Nat), [Arith.Nat])]
    [(Term_Rewriting.Term (Labelings.Lab a b) c,
       Term_Rewriting.Term (Labelings.Lab a b) c)]
    (Labelings.Lab a b) (Labelings.Lab a b) (Labelings.Lab a b)
    (Labelings.Lab a b) (Labelings.Lab a b) (Labelings.Lab a b)
    (Check_Termination.Trs_termination_proof a b c)
    (CSR_GM_Transformation.Gm_extended_csr_termination_proof a b c)
  | GM04_Complete_Full_Transformation_Proof
      [((Labelings.Lab a b, Arith.Nat), [Arith.Nat])]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Labelings.Lab a b) (Labelings.Lab a b) (Labelings.Lab a b)
      (Labelings.Lab a b) (Labelings.Lab a b) (Labelings.Lab a b)
      (Critical_Pairs_Impl.Join_info (Labelings.Lab a b) c)
      (Check_Termination.Trs_termination_proof a b c)
      (CSR_GM_Transformation.Gm_extended_csr_termination_proof a b c);

gm04_rules_variant_subset ::
  forall a b.
    (Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => [(Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b)] ->
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)] ->
                                     Bool;
gm04_rules_variant_subset pa p =
  all (\ pb -> any (Term_Rewriting.eq_rule_mod_vars pb) pa) p;

gm04_rules_variant_eq ::
  forall a b.
    (Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => [(Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b)] ->
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)] ->
                                     Bool;
gm04_rules_variant_eq pa p =
  all (\ paa -> any (Term_Rewriting.eq_rule_mod_vars paa) p) pa &&
    all (\ pb -> any (Term_Rewriting.eq_rule_mod_vars pb) pa) p;

gm04_residual_assm ::
  forall a b c.
    (Compare.Compare_order a, Eq a, Compare.Compare_order b, Eq b,
      Arith.Ccompare c, Eq c,
      Mapping.Mapping_impl c) => [(Term_Rewriting.Term (Labelings.Lab a b) c,
                                    Term_Rewriting.Term (Labelings.Lab a b)
                                      c)] ->
                                   [(Term_Rewriting.Term (Labelings.Lab a b) c,
                                      Term_Rewriting.Term (Labelings.Lab a b)
c)] ->
                                     [Term_Rewriting.Term (Labelings.Lab a b)
c] ->
                                       [Check_Termination_Common.Assm a b c] ->
 Bool;
gm04_residual_assm pa s qa
  [Check_Termination_Common.Finite_assm [] (True, (m, (p, (pw, (q, (r, rw))))))]
  = gm04_rules_variant_eq pa p &&
      null pw &&
        Error_Monad.isOK (Q_Restricted_Rewriting_Impl.check_NF_terms_eq qa q) &&
          null r && gm04_rules_variant_subset s rw;
gm04_residual_assm p s q [] = False;
gm04_residual_assm p s q (Check_Termination_Common.SN_assm vb vc : va) = False;
gm04_residual_assm p s q (Check_Termination_Common.SN_FP_assm vb vc : va) =
  False;
gm04_residual_assm p s q
  (Check_Termination_Common.Finite_assm (vd : ve) vc : va) = False;
gm04_residual_assm p s q
  (Check_Termination_Common.Finite_assm vb (False, ve) : va) = False;
gm04_residual_assm p s q (Check_Termination_Common.Unknown_assm vb vc : va) =
  False;
gm04_residual_assm p s q (Check_Termination_Common.Not_SN_assm vb vc : va) =
  False;
gm04_residual_assm p s q (Check_Termination_Common.Not_RelSN_assm vb vc : va) =
  False;
gm04_residual_assm p s q (Check_Termination_Common.Not_SN_FP_assm vb vc : va) =
  False;
gm04_residual_assm p s q (Check_Termination_Common.Infinite_assm vb vc : va) =
  False;
gm04_residual_assm p s q (Check_Termination_Common.Complexity_assm vb vc : va) =
  False;
gm04_residual_assm p s q (v : vb : vc) = False;

gm04_extra_nullaries ::
  forall a b c d e.
    (Eq a, Arith.Zero b, Eq b,
      Arith.Zero e) => a -> a -> [(a, b)] ->
                                   [(Term_Rewriting.Term a c,
                                      Term_Rewriting.Term a d)] ->
                                     [(a, e)];
gm04_extra_nullaries proper ok f [] = [];
gm04_extra_nullaries proper ok f
  ((Term_Rewriting.Fun p [Term_Rewriting.Fun c []],
     Term_Rewriting.Fun q [Term_Rewriting.Fun d []]) :
    r)
  = (if p == proper &&
          q == ok && c == d && not (Arith.membera f (c, Arith.zero))
      then (c, Arith.zero) : gm04_extra_nullaries proper ok f r
      else gm04_extra_nullaries proper ok f r);
gm04_extra_nullaries proper ok f ((Term_Rewriting.Var vb, va) : r) =
  gm04_extra_nullaries proper ok f r;
gm04_extra_nullaries proper ok f ((Term_Rewriting.Fun vb [], va) : r) =
  gm04_extra_nullaries proper ok f r;
gm04_extra_nullaries proper ok f
  ((Term_Rewriting.Fun vb (Term_Rewriting.Var vf : ve), va) : r) =
  gm04_extra_nullaries proper ok f r;
gm04_extra_nullaries proper ok f
  ((Term_Rewriting.Fun vb (Term_Rewriting.Fun vf (vh : vi) : ve), va) : r) =
  gm04_extra_nullaries proper ok f r;
gm04_extra_nullaries proper ok f
  ((Term_Rewriting.Fun vb (vd : vf : vg), va) : r) =
  gm04_extra_nullaries proper ok f r;
gm04_extra_nullaries proper ok f ((v, Term_Rewriting.Var vb) : r) =
  gm04_extra_nullaries proper ok f r;
gm04_extra_nullaries proper ok f ((v, Term_Rewriting.Fun vb []) : r) =
  gm04_extra_nullaries proper ok f r;
gm04_extra_nullaries proper ok f
  ((v, Term_Rewriting.Fun vb (Term_Rewriting.Var vf : ve)) : r) =
  gm04_extra_nullaries proper ok f r;
gm04_extra_nullaries proper ok f
  ((v, Term_Rewriting.Fun vb (Term_Rewriting.Fun vf (vh : vi) : ve)) : r) =
  gm04_extra_nullaries proper ok f r;
gm04_extra_nullaries proper ok f ((v, Term_Rewriting.Fun vb (vd : vf : vg)) : r)
  = gm04_extra_nullaries proper ok f r;

gm04_roles_fresh_list ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Eq a,
      Arith.Set_impl a) => a -> a -> a -> a -> a -> [(a, b)] -> Bool;
gm04_roles_fresh_list active mark proper ok top_sym f =
  Arith.distinct [active, mark, proper, ok, top_sym] &&
    all (\ (fa, _) ->
          not (Arith.member fa
                (Arith.insert active
                  (Arith.insert mark
                    (Arith.insert proper
                      (Arith.insert ok
                        (Arith.insert top_sym Arith.bot_set)))))))
      f;

gm04_schema_signature_list ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Eq a,
      Arith.Set_impl a) => a -> a -> a -> a ->
    [(a, Arith.Nat)] ->
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] -> Bool;
gm04_schema_signature_list active mark proper ok f s =
  all (\ (fa, n) ->
        Arith.membera f (fa, n) ||
          Arith.member (fa, n)
            (Arith.insert (active, Arith.one_nat)
              (Arith.insert (mark, Arith.one_nat)
                (Arith.insert (proper, Arith.one_nat)
                  (Arith.insert (ok, Arith.one_nat) Arith.bot_set)))))
    (Term_Rewriting.funas_trs_list s);

gm04_source_proof_is_global ::
  forall a b c.
    CSR_GM_Transformation.Gm_extended_csr_termination_proof a b c -> Bool;
gm04_source_proof_is_global (CSR_GM_Transformation.Existing_CSR_Proof old) =
  CSR_Conservative_Checker.extended_csr_proof_is_global old;
gm04_source_proof_is_global (CSR_GM_Transformation.Guarded_CSR_Proof v) = False;
gm04_source_proof_is_global
  (CSR_GM_Transformation.Innermost_CSR_Dependency_Pairs v va vb) = False;
gm04_source_proof_is_global
  (CSR_GM_Transformation.Muterm_Innermost_CSR_Dependency_Pairs v va vb) = False;
gm04_source_proof_is_global
  (CSR_GM_Transformation.Muterm_Usable_CSR_Dependency_Pairs v va vb vc) = False;
gm04_source_proof_is_global
  (CSR_GM_Transformation.Muterm_Typed_CSR_Dependency_Pairs v va vb) = False;
gm04_source_proof_is_global
  (CSR_GM_Transformation.Muterm_Expanded_Innermost_CSR_Dependency_Pairs v va vb)
  = False;
gm04_source_proof_is_global
  (CSR_GM_Transformation.Muterm_Expanded_Innermost_Filtered_Usable_CSR_Dependency_Pairs
    v va vb)
  = False;
gm04_source_proof_is_global
  (CSR_GM_Transformation.Muterm_Expanded_Innermost_Usable_CSR_Dependency_Pairs v
    va vb vc)
  = False;
gm04_source_proof_is_global
  (CSR_GM_Transformation.GM_CSR_Transformation v va vb vc) = False;

gm04_pair_args_signature_list ::
  forall a b c d.
    (Eq b) => a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
                     [(Term_Rewriting.Term b d, Term_Rewriting.Term b d)] ->
                       Bool;
gm04_pair_args_signature_list top_sharp p s =
  all (Arith.membera (Term_Rewriting.funas_trs_list s))
    (Term_Rewriting.funas_args_trs_list p);

check_gm04_complete_nontermination_proof ::
  forall a.
    (Compare.Compare_order a, Countable.Countable a, Eq a,
      Term_Rewriting.Showl a) => (String -> String) ->
                                   Bool ->
                                     [Term_Rewriting.Term
(Labelings.Lab a [Arith.Nat]) [Arith.Char]] ->
                                       [(Term_Rewriting.Term
   (Labelings.Lab a [Arith.Nat]) [Arith.Char],
  Term_Rewriting.Term (Labelings.Lab a [Arith.Nat]) [Arith.Char])] ->
 [(Term_Rewriting.Term (Labelings.Lab a [Arith.Nat]) [Arith.Char],
    Term_Rewriting.Term (Labelings.Lab a [Arith.Nat]) [Arith.Char])] ->
   Gm04_complete_nontermination_proof a [Arith.Nat] [Arith.Char] ->
     Sum_Type.Sum (String -> String) ();
check_gm04_complete_nontermination_proof i nfs q t tw
  (GM04_Complete_Nontermination_Proof mu r active mark proper ok top_sym
    source_loop)
  = FOR_Preliminaries.debug i
      "complete Giesl-Middeldorp nontermination transformation"
      (Error_Monad.bind
        (Check_Monad.check (not nfs)
          (Term_Rewriting.showsl_lit
            "transformed problem is not full rewriting"))
        (\ _ ->
          Error_Monad.bind
            (Check_Monad.check (null q)
              (Term_Rewriting.showsl_lit
                "transformed problem has a nonempty Q component"))
            (\ _ ->
              Error_Monad.bind
                (Check_Monad.check (null tw)
                  (Term_Rewriting.showsl_lit
                    "transformed problem has weak rules"))
                (\ _ ->
                  Error_Monad.bind (Term_Rewriting.check_wf_trs r)
                    (\ _ ->
                      let {
                        f = Arith.remdups (Term_Rewriting.funas_trs_list r);
                      } in Error_Monad.bind
                             (Check_Monad.check
                               (any (\ (_, n) ->
                                      Arith.equal_nat n Arith.zero_nat)
                                 f)
                               (Term_Rewriting.showsl_lit
                                 "source signature has no constant for grounding"))
                             (\ _ ->
                               Error_Monad.bind
                                 (Check_Monad.check
                                   (gm04_roles_fresh_list active mark proper ok
                                     top_sym f)
                                   (Term_Rewriting.showsl_lit
                                     "GM04 administrative symbols are not fresh"))
                                 (\ _ ->
                                   let {
                                     c = GM04_Complete_Transformation.gm04_complete_rules
   (Context_Sensitive_Impl.mu_of mu) active mark proper ok top_sym f r;
                                   } in Error_Monad.bind
  (Trs_Impl_More.check_variants_trs t c)
  (\ _ ->
    Error_Monad.bind (Trs_Impl_More.check_variants_trs c t)
      (\ _ -> CSR_Check_Loops.check_csr_loop mu r source_loop)))))))));

check_gm04_complete_transformation_proof ::
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
 [Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char]] ->
   [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
      Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
     [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
        Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
       Gm04_complete_transformation_proof b [Arith.Nat] [Arith.Char] ->
         Sum_Type.Sum (String -> String) ();
check_gm04_complete_transformation_proof ia j i nfs q t tw
  (GM04_Complete_Transformation_Proof mu r active mark proper ok top_sym
    top_sharp child source_child)
  = FOR_Preliminaries.debug i "complete Giesl-Middeldorp inverse transformation"
      (Error_Monad.bind
        (Check_Monad.check nfs
          (Term_Rewriting.showsl_lit "transformed problem is not innermost"))
        (\ _ ->
          Error_Monad.bind
            (Check_Monad.check (null tw)
              (Term_Rewriting.showsl_lit "transformed problem has weak rules"))
            (\ _ ->
              Error_Monad.bind (Term_Rewriting.check_wf_trs r)
                (\ _ ->
                  let {
                    f0 = Arith.remdups (Term_Rewriting.funas_trs_list r);
                    f = Arith.remdups
                          (f0 ++ gm04_extra_nullaries proper ok f0 t);
                  } in Error_Monad.bind
                         (Check_Monad.check
                           (f == f0 || gm04_source_proof_is_global source_child)
                           (Term_Rewriting.showsl_lit
                             "GM04 signature extension requires a global source proof"))
                         (\ _ ->
                           Error_Monad.bind
                             (Check_Monad.check
                               (gm04_roles_fresh_list active mark proper ok
                                 top_sym f)
                               (Term_Rewriting.showsl_lit
                                 "GM04 administrative symbols are not fresh"))
                             (\ _ ->
                               let {
                                 s = GM04_Complete_Transformation.gm04_non_top_rules
                                       (Context_Sensitive_Impl.mu_of mu) active
                                       mark proper ok f r;
                                 p = GM04_Complete_Transformation.gm04_top_pairs
                                       active mark proper ok top_sharp;
                                 c = GM04_Complete_Transformation.gm04_complete_rules
                                       (Context_Sensitive_Impl.mu_of mu) active
                                       mark proper ok top_sym f r;
                               } in Error_Monad.bind
                                      (Trs_Impl_More.check_variants_trs t c)
                                      (\ _ ->
Error_Monad.bind (Trs_Impl_More.check_variants_trs c t)
  (\ _ ->
    Error_Monad.bind
      (Check_Monad.check (gm04_schema_signature_list active mark proper ok f s)
        (Term_Rewriting.showsl_lit "GM04 non-top signature is invalid"))
      (\ _ ->
        Error_Monad.bind
          (Check_Monad.check (gm04_pair_args_signature_list top_sharp p s)
            (Term_Rewriting.showsl_lit
              "GM04 residual pair arguments are outside the non-top signature"))
          (\ _ ->
            Error_Monad.bind
              (Check_Monad.check
                (all (\ (fa, _) -> not (Labelings.equal_lab fa top_sharp))
                  (Term_Rewriting.funas_trs_list s))
                (Term_Rewriting.showsl_lit
                  "GM04 residual sharp symbol is not fresh"))
              (\ _ ->
                Error_Monad.bind
                  (CSR_GM_Transformation.check_gm_extended_csr_termination_proof
                    ia j False (Term_Rewriting.add_index i Arith.one_nat) mu r
                    source_child)
                  (\ _ ->
                    Error_Monad.bind
                      (Check_Termination.check_trs_termination_proof ia j True
                        (Term_Rewriting.add_index i
                          (Arith.nat_of_integer (2 :: Integer)))
                        (Termination_Problem_Spec.mk ia nfs q t tw) child)
                      (\ _ ->
                        Check_Monad.check
                          (gm04_residual_assm p s (map fst s)
                            (Check_Termination.sn_assms True child))
                          (Term_Rewriting.showsl_lit
                            "ordinary proof does not have exactly the certified GM04 residual"))))))))))))));
check_gm04_complete_transformation_proof ia j i nfs q t tw
  (GM04_Complete_Full_Transformation_Proof mu r active mark proper ok top_sym
    top_sharp joins administrative_child source_child)
  = FOR_Preliminaries.debug i
      "complete full Giesl-Middeldorp inverse transformation"
      (Error_Monad.bind
        (Check_Monad.check (not nfs)
          (Term_Rewriting.showsl_lit
            "transformed problem is not full rewriting"))
        (\ _ ->
          Error_Monad.bind
            (Check_Monad.check (null q)
              (Term_Rewriting.showsl_lit
                "transformed problem has a nonempty Q component"))
            (\ _ ->
              Error_Monad.bind
                (Check_Monad.check (null tw)
                  (Term_Rewriting.showsl_lit
                    "transformed problem has weak rules"))
                (\ _ ->
                  Error_Monad.bind (Term_Rewriting.check_wf_trs r)
                    (\ _ ->
                      let {
                        f0 = Arith.remdups (Term_Rewriting.funas_trs_list r);
                        f = Arith.remdups
                              (f0 ++ gm04_extra_nullaries proper ok f0 t);
                      } in Error_Monad.bind
                             (Check_Monad.check
                               (f == f0 ||
                                 gm04_source_proof_is_global source_child)
                               (Term_Rewriting.showsl_lit
                                 "GM04 signature extension requires a global source proof"))
                             (\ _ ->
                               Error_Monad.bind
                                 (Check_Monad.check
                                   (gm04_roles_fresh_list active mark proper ok
                                     top_sym f)
                                   (Term_Rewriting.showsl_lit
                                     "GM04 administrative symbols are not fresh"))
                                 (\ _ ->
                                   let {
                                     s = GM04_Complete_Transformation.gm04_non_top_rules
   (Context_Sensitive_Impl.mu_of mu) active mark proper ok f r;
                                     p = GM04_Complete_Transformation.gm04_top_pairs
   active mark proper ok top_sharp;
                                     c = GM04_Complete_Transformation.gm04_complete_rules
   (Context_Sensitive_Impl.mu_of mu) active mark proper ok top_sym f r;
                                   } in Error_Monad.bind
  (Trs_Impl_More.check_variants_trs t c)
  (\ _ ->
    Error_Monad.bind (Trs_Impl_More.check_variants_trs c t)
      (\ _ ->
        Error_Monad.bind
          (Check_Monad.check
            (gm04_schema_signature_list active mark proper ok f s)
            (Term_Rewriting.showsl_lit "GM04 non-top signature is invalid"))
          (\ _ ->
            Error_Monad.bind
              (Check_Monad.check (gm04_pair_args_signature_list top_sharp p s)
                (Term_Rewriting.showsl_lit
                  "GM04 residual pair arguments are outside the non-top signature"))
              (\ _ ->
                Error_Monad.bind
                  (Check_Monad.check
                    (not (Arith.member top_sharp
                           (Arith.insert active
                             (Arith.insert mark
                               (Arith.insert proper
                                 (Arith.insert ok
                                   (Arith.insert top_sym
                                     (Arith.set_empty
                                       (Phantom_Type.of_phantom
 Term_Rewriting.set_impl_lab)))))))))
                    (Term_Rewriting.showsl_lit
                      "GM04 residual sharp symbol is not fresh"))
                  (\ _ ->
                    Error_Monad.bind
                      (Check_Monad.check
                        (all (\ (fa, _) ->
                               not (Labelings.equal_lab fa top_sharp))
                          (Term_Rewriting.funas_trs_list s))
                        (Term_Rewriting.showsl_lit
                          "GM04 residual sharp symbol occurs in administrative rules"))
                      (\ _ ->
                        Error_Monad.bind
                          (CSR_GM_Transformation.check_gm_extended_csr_termination_proof
                            ia j False
                            (Term_Rewriting.add_index i Arith.one_nat) mu r
                            source_child)
                          (\ _ ->
                            Error_Monad.bind
                              (Check_Termination.check_trs_termination_proof ia
                                j False
                                (Term_Rewriting.add_index i
                                  (Arith.nat_of_integer (2 :: Integer)))
                                (Termination_Problem_Spec.mk ia False [] s [])
                                administrative_child)
                              (\ _ ->
                                Check_Monad.check
                                  (null (Check_Termination.sn_assms False
  administrative_child))
                                  (Term_Rewriting.showsl_lit
                                    "administrative proof has unresolved assumptions"))))))))))))))));

}
