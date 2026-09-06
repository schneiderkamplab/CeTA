{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  CSR_GM_Transformation(Gm_extended_csr_termination_proof(..),
                         check_gm_extended_csr_termination_proof)
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
import qualified CSR_Innermost_Unhiding_RTA08;
import qualified CSR_Muterm_Innermost_Usable_Exec;
import qualified CSR_Innermost_Unhiding_Checker;
import qualified CSR_Muterm_Innermost_Usable;
import qualified CSR_Muterm_Typed_Checker;
import qualified CSR_Innermost_Switch;
import qualified RenamingN_String;
import qualified Context_Sensitive_Impl;
import qualified FOR_Preliminaries;
import qualified Map;
import qualified Termination_Problem_Spec;
import qualified RenamingN;
import qualified Countable;
import qualified Mapping;
import qualified Lists_are_Infinite;
import qualified CSR_Innermost_Unhiding_Proofs;
import qualified CSR_Minimal_CSDP_Proofs;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Dependency_Pair_Problem_Spec;
import qualified Sum_Type;
import qualified Compare;
import qualified HOL;
import qualified Name;
import qualified CSR_Conservative_Checker;
import qualified CSR_Guarded_List_Checker;
import qualified CSR_Muterm_Usable_Rules;
import qualified CSR_Checker_Base;
import qualified Check_Termination;
import qualified Labelings;
import qualified Term_Rewriting;
import qualified Arith;

data Gm_extended_csr_termination_proof a b c =
  Existing_CSR_Proof
    (CSR_Conservative_Checker.Extended_csr_termination_proof a b c)
  | Guarded_CSR_Proof
      (CSR_Guarded_List_Checker.Guarded_csr_termination_proof a b c)
  | Innermost_CSR_Dependency_Pairs
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (CSR_Checker_Base.Csr_dp_termination_proof a b c)
  | Muterm_Innermost_CSR_Dependency_Pairs
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (CSR_Checker_Base.Csr_dp_termination_proof a b c)
  | Muterm_Usable_CSR_Dependency_Pairs
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (CSR_Checker_Base.Csr_dp_termination_proof a b c)
  | Muterm_Typed_CSR_Dependency_Pairs
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (CSR_Muterm_Usable_Rules.Muterm_typed_dp_proof a b c)
  | Muterm_Expanded_Innermost_CSR_Dependency_Pairs
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (CSR_Checker_Base.Csr_dp_termination_proof a b c)
  | Muterm_Expanded_Innermost_Filtered_Usable_CSR_Dependency_Pairs
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (CSR_Checker_Base.Csr_dp_termination_proof a b c)
  | Muterm_Expanded_Innermost_Usable_CSR_Dependency_Pairs
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Check_Termination.Dp_termination_proof a b c)
  | GM_CSR_Transformation (Labelings.Lab a b) (Labelings.Lab a b)
      [((Labelings.Lab a b, Arith.Nat), Labelings.Lab a b)]
      (Check_Termination.Trs_termination_proof a b c);

gm_nf ::
  forall a b.
    (Arith.Ceq a,
      Arith.Ccompare a) => ((a, Arith.Nat) -> Arith.Set Arith.Nat) ->
                             Arith.Set (a, Arith.Nat) ->
                               ((a, Arith.Nat) -> a) ->
                                 a -> Term_Rewriting.Term a b ->
Term_Rewriting.Term a b;
gm_nf mu d act mark (Term_Rewriting.Var x) =
  Term_Rewriting.Fun mark [Term_Rewriting.Var x];
gm_nf mu d act mark (Term_Rewriting.Fun f ts) =
  Term_Rewriting.Fun
    (if Arith.member (f, Arith.size_list ts) d then act (f, Arith.size_list ts)
      else f)
    (gm_nf_args mu d act mark f (Arith.size_list ts) Arith.zero_nat ts);

gm_nf_args ::
  forall a b.
    (Arith.Ceq a,
      Arith.Ccompare a) => ((a, Arith.Nat) -> Arith.Set Arith.Nat) ->
                             Arith.Set (a, Arith.Nat) ->
                               ((a, Arith.Nat) -> a) ->
                                 a -> a ->
Arith.Nat ->
  Arith.Nat -> [Term_Rewriting.Term a b] -> [Term_Rewriting.Term a b];
gm_nf_args mu d act mark f n i [] = [];
gm_nf_args mu d act mark f n i (t : ts) =
  (if Arith.member i (mu (f, n)) then gm_nf mu d act mark t else t) :
    gm_nf_args mu d act mark f n (Arith.suc i) ts;

gm_lhs ::
  forall a b.
    (Arith.Ceq a,
      Arith.Ccompare a) => Arith.Set (a, Arith.Nat) ->
                             ((a, Arith.Nat) -> a) ->
                               Term_Rewriting.Term a b ->
                                 Term_Rewriting.Term a b;
gm_lhs d act (Term_Rewriting.Var x) = Term_Rewriting.Var x;
gm_lhs d act (Term_Rewriting.Fun f ts) =
  Term_Rewriting.Fun
    (if Arith.member (f, Arith.size_list ts) d then act (f, Arith.size_list ts)
      else f)
    ts;

gm_rule ::
  forall a b c.
    (Arith.Ceq a,
      Arith.Ccompare a) => ((a, Arith.Nat) -> Arith.Set Arith.Nat) ->
                             Arith.Set (a, Arith.Nat) ->
                               ((a, Arith.Nat) -> a) ->
                                 a -> (Term_Rewriting.Term a b,
Term_Rewriting.Term a c) ->
(Term_Rewriting.Term a b, Term_Rewriting.Term a c);
gm_rule mu d act mark lr =
  (gm_lhs d act (fst lr), gm_nf mu d act mark (snd lr));

gm_vars :: forall a. Arith.Nat -> [Term_Rewriting.Term a [Arith.Char]];
gm_vars n = map Term_Rewriting.Var (Name.x_1_to_x_n n);

gm_mark_rule ::
  forall a.
    (Arith.Ceq a,
      Arith.Ccompare a) => ((a, Arith.Nat) -> Arith.Set Arith.Nat) ->
                             Arith.Set (a, Arith.Nat) ->
                               ((a, Arith.Nat) -> a) ->
                                 a -> (a, Arith.Nat) ->
(Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char]);
gm_mark_rule mu d act mark fn =
  let {
    f = fst fn;
    n = snd fn;
    xs = gm_vars n;
  } in (Term_Rewriting.Fun mark [Term_Rewriting.Fun f xs],
         gm_nf mu d act mark (Term_Rewriting.Fun f xs));

gm_deactivate_rule ::
  forall a.
    ((a, Arith.Nat) -> a) ->
      (a, Arith.Nat) ->
        (Term_Rewriting.Term a [Arith.Char],
          Term_Rewriting.Term a [Arith.Char]);
gm_deactivate_rule act fn =
  let {
    f = fst fn;
    n = snd fn;
    xs = gm_vars n;
  } in (Term_Rewriting.Fun (act fn) xs, Term_Rewriting.Fun f xs);

muterm_internal_mu ::
  forall a b.
    (Eq a,
      Eq b) => [((Labelings.Lab a b, Arith.Nat), [Arith.Nat])] ->
                 [(Labelings.Lab a b, Arith.Nat)] ->
                   [((Labelings.Lab a b, Arith.Nat), [Arith.Nat])];
muterm_internal_mu mu d =
  mu ++ map (\ (f, n) ->
              ((Labelings.Sharp f, n),
                CSR_Muterm_Usable_Rules.muterm_mu_positions_list mu (f, n)))
          d ++
          map (\ (a, b) ->
                (case a of {
                  (f, n) ->
                    (\ _ ->
                      ((Labelings.Sharp f, n),
                        CSR_Muterm_Usable_Rules.muterm_mu_positions_list mu
                          (f, n)));
                })
                  b)
            mu;

gm_transformed_rules_list ::
  forall a.
    (Arith.Ceq a,
      Arith.Ccompare a) => ((a, Arith.Nat) -> Arith.Set Arith.Nat) ->
                             Arith.Set (a, Arith.Nat) ->
                               ((a, Arith.Nat) -> a) ->
                                 a -> [(a, Arith.Nat)] ->
[(Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char])] ->
  [(a, Arith.Nat)] ->
    [(Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char])];
gm_transformed_rules_list mu d act mark f r ds =
  map (gm_rule mu d act mark) r ++
    map (gm_mark_rule mu d act mark) f ++ map (gm_deactivate_rule act) ds;

muterm_usable_csr_dependency_pairs_tt ::
  forall a b.
    (Compare.Compare_order b, Eq b,
      Term_Rewriting.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a
                                   (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                   () ->
                                   [((Labelings.Lab b [Arith.Nat], Arith.Nat),
                                      [Arith.Nat])] ->
                                     [(Term_Rewriting.Term
 (Labelings.Lab b [Arith.Nat]) [Arith.Char],
Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
                                       [(Term_Rewriting.Term
   (Labelings.Lab b [Arith.Nat]) [Arith.Char],
  Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
 [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
    Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
   [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
      Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
     Sum_Type.Sum (String -> String) a;
muterm_usable_csr_dependency_pairs_tt j mu r p s w =
  let {
    d = Term_Rewriting.defined_list r;
  } in (case Error_Monad.bind (Term_Rewriting.check_wf_trs r)
               (\ _ ->
                 Error_Monad.bind
                   (Check_Monad.check
                     (all (\ a -> (case a of {
                                    (Labelings.Lab _ _, _) -> True;
                                    (Labelings.FunLab _ _, _) -> True;
                                    (Labelings.UnLab _, _) -> True;
                                    (Labelings.Sharp _, _) -> False;
                                  }))
                       d)
                     (Term_Rewriting.showsl_lit
                       "MU-TERM source rules already contain marked defined symbols"))
                   (\ _ ->
                     Error_Monad.bind
                       (Error_Monad.catch_error
                         (Error_Monad.forallM
                           (\ (f, n) ->
                             Check_Monad.check
                               (not (Arith.membera d (Labelings.Sharp f, n)))
                               (Term_Rewriting.showsl_lit
                                 "sharping yields a defined symbol"))
                           d)
                         (\ x -> Sum_Type.Inl (snd x)))
                       (\ _ ->
                         Error_Monad.bind
                           (Error_Monad.catch_error
                             (Error_Monad.catch_error
                               (Error_Monad.forallM
                                 (\ x ->
                                   (if Arith.membera p x then Sum_Type.Inr ()
                                     else Sum_Type.Inl x))
                                 (CSR_Checker_Base.mu_CSDP_list Labelings.Sharp
                                   r mu d))
                               (\ x -> Sum_Type.Inl (snd x)))
                             (\ _ ->
                               Sum_Type.Inl
                                 (Term_Rewriting.showsl_lit
                                   "missing replacement-map dependency pair")))
                           (\ _ ->
                             Error_Monad.bind
                               (Error_Monad.catch_error
                                 (Error_Monad.catch_error
                                   (Error_Monad.forallM
                                     (\ x ->
                                       (if Arith.membera p x
 then Sum_Type.Inr () else Sum_Type.Inl x))
                                     (CSR_Minimal_CSDP_Proofs.csr_rta08_collapsing_CSDP_list
                                       Labelings.Sharp mu r))
                                   (\ x -> Sum_Type.Inl (snd x)))
                                 (\ _ ->
                                   Sum_Type.Inl
                                     (Term_Rewriting.showsl_lit
                                       "missing collapsing dependency pair")))
                               (\ _ ->
                                 Error_Monad.bind
                                   (Error_Monad.catch_error
                                     (Error_Monad.catch_error
                                       (Error_Monad.forallM
 (\ x -> (if Arith.membera s x then Sum_Type.Inr () else Sum_Type.Inl x))
 (CSR_Innermost_Unhiding_Proofs.muterm_exact_unhiding_rules_list Labelings.Sharp
   mu d r))
                                       (\ x -> Sum_Type.Inl (snd x)))
                                     (\ _ ->
                                       Sum_Type.Inl
 (Term_Rewriting.showsl_lit "missing exact MU-TERM unhiding rule")))
                                   (\ _ ->
                                     Error_Monad.bind
                                       (Check_Monad.check
 (CSR_Innermost_Unhiding_Proofs.muterm_unhiding_safe_list mu r)
 (Term_Rewriting.showsl_lit "MU-TERM unhiding safety condition failed"))
                                       (\ _ ->
 Check_Monad.check
   (CSR_Muterm_Usable_Rules.muterm_qcs_ur_closed_check r s w mu p)
   (Term_Rewriting.showsl_lit "MU-TERM usable-rule closure check failed"))))))))
         of {
         Sum_Type.Inl a -> Sum_Type.Inl a;
         Sum_Type.Inr _ ->
           Sum_Type.Inr
             (Dependency_Pair_Problem_Spec.mk j False False p [] [] [] w);
       });

muterm_innermost_csr_dependency_pairs_tt ::
  forall a b.
    (Compare.Compare_order b, Eq b,
      Term_Rewriting.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a
                                   (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                   () ->
                                   [((Labelings.Lab b [Arith.Nat], Arith.Nat),
                                      [Arith.Nat])] ->
                                     [(Term_Rewriting.Term
 (Labelings.Lab b [Arith.Nat]) [Arith.Char],
Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
                                       [(Term_Rewriting.Term
   (Labelings.Lab b [Arith.Nat]) [Arith.Char],
  Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
 [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
    Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
   Sum_Type.Sum (String -> String) a;
muterm_innermost_csr_dependency_pairs_tt j mu r p s =
  let {
    d = Term_Rewriting.defined_list r;
  } in (case Error_Monad.bind (Term_Rewriting.check_wf_trs r)
               (\ _ ->
                 Error_Monad.bind
                   (Error_Monad.catch_error
                     (Error_Monad.forallM
                       (\ (f, n) ->
                         Check_Monad.check
                           (not (Arith.membera d (Labelings.Sharp f, n)))
                           (Term_Rewriting.showsl_lit
                             "sharping yields a defined symbol"))
                       d)
                     (\ x -> Sum_Type.Inl (snd x)))
                   (\ _ ->
                     Error_Monad.bind
                       (Error_Monad.catch_error
                         (Error_Monad.catch_error
                           (Error_Monad.forallM
                             (\ x ->
                               (if Arith.membera p x then Sum_Type.Inr ()
                                 else Sum_Type.Inl x))
                             (CSR_Checker_Base.mu_CSDP_list Labelings.Sharp r mu
                               d))
                           (\ x -> Sum_Type.Inl (snd x)))
                         (\ _ ->
                           Sum_Type.Inl
                             (Term_Rewriting.showsl_lit
                               "missing replacement-map dependency pair")))
                       (\ _ ->
                         Error_Monad.bind
                           (Error_Monad.catch_error
                             (Error_Monad.catch_error
                               (Error_Monad.forallM
                                 (\ x ->
                                   (if Arith.membera p x then Sum_Type.Inr ()
                                     else Sum_Type.Inl x))
                                 (CSR_Minimal_CSDP_Proofs.csr_rta08_collapsing_CSDP_list
                                   Labelings.Sharp mu r))
                               (\ x -> Sum_Type.Inl (snd x)))
                             (\ _ ->
                               Sum_Type.Inl
                                 (Term_Rewriting.showsl_lit
                                   "missing collapsing dependency pair")))
                           (\ _ ->
                             Error_Monad.bind
                               (Error_Monad.catch_error
                                 (Error_Monad.catch_error
                                   (Error_Monad.forallM
                                     (\ x ->
                                       (if Arith.membera s x
 then Sum_Type.Inr () else Sum_Type.Inl x))
                                     (CSR_Innermost_Unhiding_Proofs.muterm_exact_unhiding_rules_list
                                       Labelings.Sharp mu d r))
                                   (\ x -> Sum_Type.Inl (snd x)))
                                 (\ _ ->
                                   Sum_Type.Inl
                                     (Term_Rewriting.showsl_lit
                                       "missing exact MU-TERM unhiding rule")))
                               (\ _ ->
                                 Check_Monad.check
                                   (CSR_Innermost_Unhiding_Proofs.muterm_unhiding_safe_list
                                     mu r)
                                   (Term_Rewriting.showsl_lit
                                     "MU-TERM unhiding safety condition failed"))))))
         of {
         Sum_Type.Inl a -> Sum_Type.Inl a;
         Sum_Type.Inr _ ->
           Sum_Type.Inr
             (Dependency_Pair_Problem_Spec.mk j False False p [] [] []
               (r ++ s));
       });

check_gm_extended_csr_termination_proof ::
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
 [((Labelings.Lab b [Arith.Nat], Arith.Nat), [Arith.Nat])] ->
   [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
      Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
     Gm_extended_csr_termination_proof b [Arith.Nat] [Arith.Char] ->
       Sum_Type.Sum (String -> String) ();
check_gm_extended_csr_termination_proof ia j a i mu r (Existing_CSR_Proof prf) =
  CSR_Conservative_Checker.check_extended_csr_termination_proof ia j a i mu r
    prf;
check_gm_extended_csr_termination_proof ia j a i mu r (Guarded_CSR_Proof prf) =
  CSR_Guarded_List_Checker.check_guarded_csr_termination_proof ia j i mu r prf;
check_gm_extended_csr_termination_proof ia j a i mu r
  (Innermost_CSR_Dependency_Pairs p s prf) =
  (if null s
    then CSR_Innermost_Unhiding_RTA08.check_innermost_csr_or_rta08_termination_proof
           ia j i mu r p prf
    else FOR_Preliminaries.debug i "direct innermost CSR dependency pairs"
           (Error_Monad.bind
             (CSR_Innermost_Unhiding_Checker.direct_innermost_csr_dependency_pairs_tt
               j mu r p (r ++ s))
             (\ dpp ->
               CSR_Checker_Base.check_csr_dp_termination_proof ia j False
                 (Term_Rewriting.add_index i Arith.one_nat) dpp prf)));
check_gm_extended_csr_termination_proof ia j a i mu r
  (Muterm_Innermost_CSR_Dependency_Pairs p s prf) =
  FOR_Preliminaries.debug i "MU-TERM innermost CSR dependency pairs"
    (Error_Monad.bind (muterm_innermost_csr_dependency_pairs_tt j mu r p s)
      (\ dpp ->
        CSR_Checker_Base.check_csr_dp_termination_proof ia j False
          (Term_Rewriting.add_index i Arith.one_nat) dpp prf));
check_gm_extended_csr_termination_proof ia j a i mu r
  (Muterm_Usable_CSR_Dependency_Pairs p s w prf) =
  FOR_Preliminaries.debug i "MU-TERM CSR dependency pairs with usable rules"
    (Error_Monad.bind (muterm_usable_csr_dependency_pairs_tt j mu r p s w)
      (\ dpp ->
        CSR_Checker_Base.check_csr_dp_termination_proof ia j False
          (Term_Rewriting.add_index i Arith.one_nat) dpp prf));
check_gm_extended_csr_termination_proof ia j a i mu r
  (Muterm_Typed_CSR_Dependency_Pairs p s prf) =
  FOR_Preliminaries.debug i "typed recursive MU-TERM CSR dependency pairs"
    (Error_Monad.bind (Term_Rewriting.check_wf_trs r)
      (\ _ ->
        Error_Monad.bind (CSR_Innermost_Switch.check_csr_orthogonal r)
          (\ _ ->
            Error_Monad.bind (CSR_Checker_Base.csr_sharp_mu_check mu)
              (\ _ ->
                let {
                  d = Term_Rewriting.defined_list r;
                } in Error_Monad.bind
                       (Check_Monad.check
                         (all (\ (f, _) ->
                                not (CSR_Checker_Base.is_sharp_lab f))
                           (Term_Rewriting.funas_trs_list r))
                         (Term_Rewriting.showsl_lit
                           "MU-TERM source signature contains marked symbols"))
                       (\ _ ->
                         let {
                           mu_i = muterm_internal_mu mu d;
                         } in Error_Monad.bind
                                (Check_Monad.check
                                  (all (\ aa ->
 (case aa of {
   (Labelings.Lab _ _, _) -> True;
   (Labelings.FunLab _ _, _) -> True;
   (Labelings.UnLab _, _) -> True;
   (Labelings.Sharp _, _) -> False;
 }))
                                    d)
                                  (Term_Rewriting.showsl_lit
                                    "MU-TERM source rules already contain marked defined symbols"))
                                (\ _ ->
                                  Error_Monad.bind
                                    (Error_Monad.catch_error
                                      (Error_Monad.forallM
(\ (f, n) ->
  Check_Monad.check (not (Arith.membera d (Labelings.Sharp f, n)))
    (Term_Rewriting.showsl_lit "sharping yields a defined symbol"))
d)
                                      (\ x -> Sum_Type.Inl (snd x)))
                                    (\ _ ->
                                      Error_Monad.bind
(Error_Monad.catch_error
  (Error_Monad.catch_error
    (Error_Monad.forallM
      (\ x -> (if Arith.membera p x then Sum_Type.Inr () else Sum_Type.Inl x))
      (CSR_Checker_Base.mu_CSDP_list Labelings.Sharp r mu_i d))
    (\ x -> Sum_Type.Inl (snd x)))
  (\ _ ->
    Sum_Type.Inl
      (Term_Rewriting.showsl_lit "missing replacement-map dependency pair")))
(\ _ ->
  Error_Monad.bind
    (Error_Monad.catch_error
      (Error_Monad.catch_error
        (Error_Monad.forallM
          (\ x ->
            (if Arith.membera p x then Sum_Type.Inr () else Sum_Type.Inl x))
          (CSR_Minimal_CSDP_Proofs.csr_rta08_collapsing_CSDP_list
            Labelings.Sharp mu_i r))
        (\ x -> Sum_Type.Inl (snd x)))
      (\ _ ->
        Sum_Type.Inl
          (Term_Rewriting.showsl_lit "missing collapsing dependency pair")))
    (\ _ ->
      Error_Monad.bind
        (Check_Monad.check
          (Arith.set_eq (Arith.set s)
            (Arith.set
              (CSR_Innermost_Unhiding_Proofs.muterm_exact_unhiding_rules_list
                Labelings.Sharp mu_i d r)))
          (Term_Rewriting.showsl_lit "MU-TERM unhiding rules are not exact"))
        (\ _ ->
          Error_Monad.bind
            (Check_Monad.check
              (CSR_Innermost_Unhiding_Proofs.muterm_unhiding_safe_list mu_i r)
              (Term_Rewriting.showsl_lit
                "MU-TERM unhiding safety condition failed"))
            (\ _ ->
              let {
                t = r ++ p ++ s;
                delta = Arith.set (Term_Rewriting.funas_trs_list t);
              } in Error_Monad.bind
                     (Check_Monad.check
                       (CSR_Muterm_Typed_Checker.muterm_recursive_pairs_safe_check_exec
                         r mu_i (Context_Sensitive_Impl.mu_of mu_i) delta p s)
                       (Term_Rewriting.showsl_lit
                         "recursive MU-TERM pair safety check failed"))
                     (\ _ ->
                       Error_Monad.bind
                         (Check_Monad.check
                           (CSR_Muterm_Typed_Checker.muterm_recursive_bridges_safe_check_exec
                             (Term_Rewriting.defined_list r)
                             (Context_Sensitive_Impl.mu_of mu_i) delta s)
                           (Term_Rewriting.showsl_lit
                             "recursive MU-TERM bridge safety check failed"))
                         (\ _ ->
                           Error_Monad.bind
                             (Check_Monad.check
                               (CSR_Muterm_Typed_Checker.muterm_recursive_target_shape_check_exec
                                 p s)
                               (Term_Rewriting.showsl_lit
                                 "recursive MU-TERM target-shape check failed"))
                             (\ _ ->
                               Error_Monad.bind
                                 (Check_Monad.check
                                   (CSR_Muterm_Usable_Rules.muterm_marked_mu_equal_check
                                     mu_i)
                                   (Term_Rewriting.showsl_lit
                                     "marked replacement-map entries differ from source symbols"))
                                 (\ _ ->
                                   CSR_Muterm_Typed_Checker.check_muterm_i4_root_proof
                                     ia j mu_i
                                     (Term_Rewriting.add_index i Arith.one_nat)
                                     r s p prf)))))))))))))));
check_gm_extended_csr_termination_proof ia j a i mu r
  (Muterm_Expanded_Innermost_CSR_Dependency_Pairs p s prf) =
  FOR_Preliminaries.debug i
    "orthogonal CSR via expanded innermost MU-TERM pairs"
    (Error_Monad.bind (Term_Rewriting.check_wf_trs r)
      (\ _ ->
        Error_Monad.bind (CSR_Innermost_Switch.check_csr_orthogonal r)
          (\ _ ->
            Error_Monad.bind (CSR_Checker_Base.csr_sharp_mu_check mu)
              (\ _ ->
                let {
                  d = Term_Rewriting.defined_list r;
                } in Error_Monad.bind
                       (Check_Monad.check
                         (all (\ (f, _) ->
                                not (CSR_Checker_Base.is_sharp_lab f))
                           (Term_Rewriting.funas_trs_list r))
                         (Term_Rewriting.showsl_lit
                           "MU-TERM source signature contains marked symbols"))
                       (\ _ ->
                         let {
                           mu_i = muterm_internal_mu mu d;
                         } in Error_Monad.bind
                                (Check_Monad.check
                                  (all (\ aa ->
 (case aa of {
   (Labelings.Lab _ _, _) -> True;
   (Labelings.FunLab _ _, _) -> True;
   (Labelings.UnLab _, _) -> True;
   (Labelings.Sharp _, _) -> False;
 }))
                                    d)
                                  (Term_Rewriting.showsl_lit
                                    "source TRS already contains reserved sharp symbols"))
                                (\ _ ->
                                  Error_Monad.bind
                                    (Error_Monad.catch_error
                                      (Error_Monad.catch_error
(Error_Monad.forallM
  (\ x -> (if Arith.membera p x then Sum_Type.Inr () else Sum_Type.Inl x))
  (CSR_Checker_Base.mu_CSDP_list Labelings.Sharp r mu_i d))
(\ x -> Sum_Type.Inl (snd x)))
                                      (\ _ ->
Sum_Type.Inl
  (Term_Rewriting.showsl_lit "missing replacement-map dependency pair")))
                                    (\ _ ->
                                      Error_Monad.bind
(Error_Monad.catch_error
  (Error_Monad.catch_error
    (Error_Monad.forallM
      (\ x -> (if Arith.membera p x then Sum_Type.Inr () else Sum_Type.Inl x))
      (CSR_Minimal_CSDP_Proofs.csr_rta08_collapsing_CSDP_list Labelings.Sharp
        mu_i r))
    (\ x -> Sum_Type.Inl (snd x)))
  (\ _ ->
    Sum_Type.Inl
      (Term_Rewriting.showsl_lit "missing collapsing dependency pair")))
(\ _ ->
  Error_Monad.bind
    (Error_Monad.catch_error
      (Error_Monad.catch_error
        (Error_Monad.forallM
          (\ x ->
            (if Arith.membera s x then Sum_Type.Inr () else Sum_Type.Inl x))
          (CSR_Innermost_Unhiding_Proofs.muterm_exact_unhiding_rules_list
            Labelings.Sharp mu_i d r))
        (\ x -> Sum_Type.Inl (snd x)))
      (\ _ ->
        Sum_Type.Inl
          (Term_Rewriting.showsl_lit "missing exact MU-TERM unhiding rule")))
    (\ _ ->
      Error_Monad.bind
        (Check_Monad.check
          (CSR_Innermost_Unhiding_Proofs.muterm_unhiding_safe_list mu_i r)
          (Term_Rewriting.showsl_lit
            "MU-TERM unhiding safety condition failed"))
        (\ _ ->
          let {
            e = CSR_Muterm_Usable_Rules.muterm_expanded_pairs_list
                  RenamingN_String.string_renameN p s;
            dpp = Dependency_Pair_Problem_Spec.mk j False False e [] [] [] r;
          } in CSR_Muterm_Innermost_Usable.check_muterm_expanded_innermost_proof
                 ia j mu_i (Term_Rewriting.add_index i Arith.one_nat) dpp
                 prf))))))))));
check_gm_extended_csr_termination_proof ia j a i mu r
  (Muterm_Expanded_Innermost_Usable_CSR_Dependency_Pairs p s u prf) =
  FOR_Preliminaries.debug i
    "orthogonal CSR via expanded innermost MU-TERM usable rules"
    (Error_Monad.bind (Term_Rewriting.check_wf_trs r)
      (\ _ ->
        Error_Monad.bind (CSR_Innermost_Switch.check_csr_orthogonal r)
          (\ _ ->
            Error_Monad.bind (CSR_Checker_Base.csr_sharp_mu_check mu)
              (\ _ ->
                let {
                  d = Term_Rewriting.defined_list r;
                } in Error_Monad.bind
                       (Check_Monad.check
                         (all (\ (f, _) ->
                                not (CSR_Checker_Base.is_sharp_lab f))
                           (Term_Rewriting.funas_trs_list r))
                         (Term_Rewriting.showsl_lit
                           "MU-TERM source signature contains marked symbols"))
                       (\ _ ->
                         let {
                           mu_i = muterm_internal_mu mu d;
                         } in Error_Monad.bind
                                (Check_Monad.check
                                  (all (\ aa ->
 (case aa of {
   (Labelings.Lab _ _, _) -> True;
   (Labelings.FunLab _ _, _) -> True;
   (Labelings.UnLab _, _) -> True;
   (Labelings.Sharp _, _) -> False;
 }))
                                    d)
                                  (Term_Rewriting.showsl_lit
                                    "source TRS already contains reserved sharp symbols"))
                                (\ _ ->
                                  Error_Monad.bind
                                    (Error_Monad.catch_error
                                      (Error_Monad.catch_error
(Error_Monad.forallM
  (\ x -> (if Arith.membera p x then Sum_Type.Inr () else Sum_Type.Inl x))
  (CSR_Checker_Base.mu_CSDP_list Labelings.Sharp r mu_i d))
(\ x -> Sum_Type.Inl (snd x)))
                                      (\ _ ->
Sum_Type.Inl
  (Term_Rewriting.showsl_lit "missing replacement-map dependency pair")))
                                    (\ _ ->
                                      Error_Monad.bind
(Error_Monad.catch_error
  (Error_Monad.catch_error
    (Error_Monad.forallM
      (\ x -> (if Arith.membera p x then Sum_Type.Inr () else Sum_Type.Inl x))
      (CSR_Minimal_CSDP_Proofs.csr_rta08_collapsing_CSDP_list Labelings.Sharp
        mu_i r))
    (\ x -> Sum_Type.Inl (snd x)))
  (\ _ ->
    Sum_Type.Inl
      (Term_Rewriting.showsl_lit "missing collapsing dependency pair")))
(\ _ ->
  Error_Monad.bind
    (Error_Monad.catch_error
      (Error_Monad.catch_error
        (Error_Monad.forallM
          (\ x ->
            (if Arith.membera s x then Sum_Type.Inr () else Sum_Type.Inl x))
          (CSR_Innermost_Unhiding_Proofs.muterm_exact_unhiding_rules_list
            Labelings.Sharp mu_i d r))
        (\ x -> Sum_Type.Inl (snd x)))
      (\ _ ->
        Sum_Type.Inl
          (Term_Rewriting.showsl_lit "missing exact MU-TERM unhiding rule")))
    (\ _ ->
      Error_Monad.bind
        (Check_Monad.check
          (CSR_Innermost_Unhiding_Proofs.muterm_unhiding_safe_list mu_i r)
          (Term_Rewriting.showsl_lit
            "MU-TERM unhiding safety condition failed"))
        (\ _ ->
          Error_Monad.bind
            (Check_Monad.check
              (CSR_Muterm_Innermost_Usable_Exec.muterm_expanded_innermost_usable_check
                r u mu_i p s)
              (Term_Rewriting.showsl_lit
                "invalid innermost usable-rule closure or typed MU-TERM target"))
            (\ _ ->
              let {
                e = CSR_Muterm_Usable_Rules.muterm_expanded_pairs_list
                      RenamingN_String.string_renameN p s;
                dpp = Dependency_Pair_Problem_Spec.mk j False False e [] [] []
                        u;
              } in Check_Termination.check_dp_termination_proof ia j False
                     (Term_Rewriting.add_index i Arith.one_nat) dpp
                     prf)))))))))));
check_gm_extended_csr_termination_proof ia j a i mu r
  (Muterm_Expanded_Innermost_Filtered_Usable_CSR_Dependency_Pairs p s prf) =
  FOR_Preliminaries.debug i
    "orthogonal CSR via expanded innermost filtered MU-TERM usable rules"
    (Error_Monad.bind (Term_Rewriting.check_wf_trs r)
      (\ _ ->
        Error_Monad.bind (CSR_Innermost_Switch.check_csr_orthogonal r)
          (\ _ ->
            Error_Monad.bind (CSR_Checker_Base.csr_sharp_mu_check mu)
              (\ _ ->
                let {
                  d = Term_Rewriting.defined_list r;
                } in Error_Monad.bind
                       (Check_Monad.check
                         (all (\ (f, _) ->
                                not (CSR_Checker_Base.is_sharp_lab f))
                           (Term_Rewriting.funas_trs_list r))
                         (Term_Rewriting.showsl_lit
                           "MU-TERM source signature contains marked symbols"))
                       (\ _ ->
                         let {
                           mu_i = muterm_internal_mu mu d;
                         } in Error_Monad.bind
                                (Check_Monad.check
                                  (all (\ aa ->
 (case aa of {
   (Labelings.Lab _ _, _) -> True;
   (Labelings.FunLab _ _, _) -> True;
   (Labelings.UnLab _, _) -> True;
   (Labelings.Sharp _, _) -> False;
 }))
                                    d)
                                  (Term_Rewriting.showsl_lit
                                    "source TRS already contains reserved sharp symbols"))
                                (\ _ ->
                                  Error_Monad.bind
                                    (Error_Monad.catch_error
                                      (Error_Monad.catch_error
(Error_Monad.forallM
  (\ x -> (if Arith.membera p x then Sum_Type.Inr () else Sum_Type.Inl x))
  (CSR_Checker_Base.mu_CSDP_list Labelings.Sharp r mu_i d))
(\ x -> Sum_Type.Inl (snd x)))
                                      (\ _ ->
Sum_Type.Inl
  (Term_Rewriting.showsl_lit "missing replacement-map dependency pair")))
                                    (\ _ ->
                                      Error_Monad.bind
(Error_Monad.catch_error
  (Error_Monad.catch_error
    (Error_Monad.forallM
      (\ x -> (if Arith.membera p x then Sum_Type.Inr () else Sum_Type.Inl x))
      (CSR_Minimal_CSDP_Proofs.csr_rta08_collapsing_CSDP_list Labelings.Sharp
        mu_i r))
    (\ x -> Sum_Type.Inl (snd x)))
  (\ _ ->
    Sum_Type.Inl
      (Term_Rewriting.showsl_lit "missing collapsing dependency pair")))
(\ _ ->
  Error_Monad.bind
    (Error_Monad.catch_error
      (Error_Monad.catch_error
        (Error_Monad.forallM
          (\ x ->
            (if Arith.membera s x then Sum_Type.Inr () else Sum_Type.Inl x))
          (CSR_Innermost_Unhiding_Proofs.muterm_exact_unhiding_rules_list
            Labelings.Sharp mu_i d r))
        (\ x -> Sum_Type.Inl (snd x)))
      (\ _ ->
        Sum_Type.Inl
          (Term_Rewriting.showsl_lit "missing exact MU-TERM unhiding rule")))
    (\ _ ->
      Error_Monad.bind
        (Check_Monad.check
          (CSR_Innermost_Unhiding_Proofs.muterm_unhiding_safe_list mu_i r)
          (Term_Rewriting.showsl_lit
            "MU-TERM unhiding safety condition failed"))
        (\ _ ->
          let {
            e = CSR_Muterm_Usable_Rules.muterm_expanded_pairs_list
                  RenamingN_String.string_renameN p s;
            dpp = Dependency_Pair_Problem_Spec.mk j False False e [] [] [] r;
          } in CSR_Muterm_Innermost_Usable.check_muterm_expanded_innermost_proof
                 ia j mu_i (Term_Rewriting.add_index i Arith.one_nat) dpp
                 prf))))))))));
check_gm_extended_csr_termination_proof ia j a i mu r
  (GM_CSR_Transformation mark c active prf) =
  FOR_Preliminaries.debug i "Giesl-Middeldorp CSR transformation"
    (Error_Monad.bind (Term_Rewriting.check_wf_trs r)
      (\ _ ->
        let {
          d = Term_Rewriting.defined_list r;
          f = Arith.remdups (Term_Rewriting.funas_trs_list r);
        } in Error_Monad.bind
               (Check_Monad.check
                 (Arith.distinct (map fst active) &&
                   Arith.set_eq (Arith.set (map fst active)) (Arith.set d))
                 (Term_Rewriting.showsl_lit
                   "active-symbol map does not cover the defined signature exactly"))
               (\ _ ->
                 Error_Monad.bind
                   (Check_Monad.check (Arith.membera f (c, Arith.zero_nat))
                     (Term_Rewriting.showsl_lit
                       "ground source-signature constant is missing"))
                   (\ _ ->
                     let {
                       act = (\ fn -> Arith.the (Map.map_of active fn));
                       t = gm_transformed_rules_list
                             (Context_Sensitive_Impl.mu_of mu) (Arith.set d) act
                             mark f r d;
                     } in Check_Termination.check_trs_termination_proof ia j
                            False (Term_Rewriting.add_index i Arith.one_nat)
                            (Termination_Problem_Spec.mk ia False [] t [])
                            prf))));

}
