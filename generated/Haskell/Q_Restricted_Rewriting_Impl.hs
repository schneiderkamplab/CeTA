{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Q_Restricted_Rewriting_Impl(qrewrite, rseq_last, check_prop_rstep,
                               check_qrstep, check_qsteps, check_rstep,
                               check_qrsteps, check_rsteps, is_NF_subset,
                               nF_subst_impl, applicable_rule_impl,
                               wwf_qtrs_impl, check_wwf_qtrs, is_NF_trs_subset,
                               check_NF_terms_subset, check_NF_terms_eq,
                               check_rsteps_last, check_NF_trs_subset,
                               check_NF_vars_subset, check_no_defined_root,
                               check_non_applicable_rules)
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
import qualified HOL;
import qualified Compare;
import qualified Position;
import qualified Error_Monad;
import qualified Check_Monad;
import qualified Sum_Type;
import qualified Option_Util;
import qualified Mapping;
import qualified Arith;
import qualified Term_Rewriting;

qrewrite ::
  forall a b.
    (Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => Bool ->
                                   (Term_Rewriting.Term a b -> Bool) ->
                                     [(Term_Rewriting.Term a b,
Term_Rewriting.Term a b)] ->
                                       Term_Rewriting.Term a b ->
 [Term_Rewriting.Term a b];
qrewrite nfs nfq r s =
  Arith.remdups
    (if all nfq (Term_Rewriting.args s)
      then concatMap
             (\ (l, ra) ->
               concatMap
                 (\ sigma ->
                   (if (case l of {
                         Term_Rewriting.Var x ->
                           (if nfs then nfq (sigma x) else True);
                         Term_Rewriting.Fun _ _ -> True;
                       })
                     then [Term_Rewriting.eval_term Term_Rewriting.Fun ra sigma]
                     else []))
                 (Option_Util.option_to_list (Term_Rewriting.match s l)))
             r
      else []) ++
    (case s of {
      Term_Rewriting.Var _ -> [];
      Term_Rewriting.Fun f ss ->
        concatMap
          (\ i ->
            map (\ ti -> Term_Rewriting.Fun f (Arith.list_update ss i ti))
              (qrewrite nfs nfq r (Arith.nth ss i)))
          (Arith.upt Arith.zero_nat (Arith.size_list ss));
    });

rseq_last ::
  forall a b.
    Term_Rewriting.Term a b ->
      [([Arith.Nat],
         ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
           Term_Rewriting.Term a b))] ->
        Term_Rewriting.Term a b;
rseq_last s steps = Arith.last (s : map (\ (_, (_, sa)) -> sa) steps);

check_prop_rstep_rule ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Term_Rewriting.Showl b) => Bool ->
                                   (Term_Rewriting.Term a b ->
                                     Sum_Type.Sum (String -> String) ()) ->
                                     [Arith.Nat] ->
                                       (Term_Rewriting.Term a b,
 Term_Rewriting.Term a b) ->
 Term_Rewriting.Term a b ->
   Term_Rewriting.Term a b -> Sum_Type.Sum (String -> String) ();
check_prop_rstep_rule nfs pa p rule s t =
  Error_Monad.bind
    (Check_Monad.check (Term_Rewriting.in_poss p s)
      (((Position.showsl_pos p .
          Term_Rewriting.showsl_literal " is not a position of ") .
         Term_Rewriting.showsl_terma s) .
        Term_Rewriting.showsl_literal "\n"))
    (\ _ ->
      Error_Monad.bind
        (Check_Monad.check (Term_Rewriting.in_poss p t)
          (((Position.showsl_pos p .
              Term_Rewriting.showsl_literal " is not a position of ") .
             Term_Rewriting.showsl_terma t) .
            Term_Rewriting.showsl_literal "\n"))
        (\ _ ->
          let {
            c = Term_Rewriting.ctxt_of_pos_term p s;
            d = Term_Rewriting.ctxt_of_pos_term p t;
            u = Term_Rewriting.subt_at s p;
            v = Term_Rewriting.subt_at t p;
          } in (case Term_Rewriting.match_list Term_Rewriting.Var
                       [(fst rule, u), (snd rule, v)]
                 of {
                 Nothing ->
                   Sum_Type.Inl
                     ((((((Term_Rewriting.showsl_literal "the term " .
                            Term_Rewriting.showsl_terma t) .
                           Term_Rewriting.showsl_literal
                             " does not result from a proper application of rule\n") .
                          Term_Rewriting.showsl_rule rule) .
                         Term_Rewriting.showsl_literal " at position ") .
                        Position.showsl_pos p) .
                       Term_Rewriting.showsl_literal "\n");
                 Just tau ->
                   Error_Monad.bind
                     (Error_Monad.catch_error
                       (Error_Monad.forallM pa
                         (Term_Rewriting.args u ++
                           (if nfs
                             then map tau (Term_Rewriting.vars_rule_list rule)
                             else [])))
                       (\ x -> Sum_Type.Inl (snd x)))
                     (\ _ ->
                       Check_Monad.check (Term_Rewriting.equal_actxt c d)
                         ((((((Term_Rewriting.showsl_literal "the term " .
                                Term_Rewriting.showsl_terma t) .
                               Term_Rewriting.showsl_literal
                                 " does not result from a proper application of rule\n") .
                              Term_Rewriting.showsl_rule rule) .
                             Term_Rewriting.showsl_literal " at position ") .
                            Position.showsl_pos p) .
                           Term_Rewriting.showsl_literal "\n"));
               })));

check_prop_rstep ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Term_Rewriting.Showl b) => Bool ->
                                   (Term_Rewriting.Term a b ->
                                     Sum_Type.Sum (String -> String) ()) ->
                                     [(Term_Rewriting.Term a b,
Term_Rewriting.Term a b)] ->
                                       [Arith.Nat] ->
 (Term_Rewriting.Term a b, Term_Rewriting.Term a b) ->
   Term_Rewriting.Term a b ->
     Term_Rewriting.Term a b -> Sum_Type.Sum (String -> String) ();
check_prop_rstep nfs pa r p rule s t =
  Check_Monad.check
    (any (\ ra ->
           Term_Rewriting.eq_rule_mod_vars rule ra &&
             Error_Monad.isOK (check_prop_rstep_rule nfs pa p ra s t))
      r)
    ((((((((Term_Rewriting.showsl_literal "the step from " .
             Term_Rewriting.showsl_terma s) .
            Term_Rewriting.showsl_literal " to ") .
           Term_Rewriting.showsl_terma t) .
          Term_Rewriting.showsl_literal " via rule ") .
         Term_Rewriting.showsl_rule rule) .
        Term_Rewriting.showsl_literal " at position ") .
       Position.showsl_pos p) .
      Term_Rewriting.showsl_literal " is problematic\n");

check_qrstep ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Term_Rewriting.Showl b) => (Term_Rewriting.Term a b -> Bool) ->
                                   Bool ->
                                     [(Term_Rewriting.Term a b,
Term_Rewriting.Term a b)] ->
                                       [Arith.Nat] ->
 (Term_Rewriting.Term a b, Term_Rewriting.Term a b) ->
   Term_Rewriting.Term a b ->
     Term_Rewriting.Term a b -> Sum_Type.Sum (String -> String) ();
check_qrstep nf nfs =
  check_prop_rstep nfs
    (\ t ->
      Check_Monad.check (nf t)
        (Term_Rewriting.showsl_terma t .
          Term_Rewriting.showsl_literal " is not in Q-normal form"));

check_rqrstep ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Term_Rewriting.Showl b) => (Term_Rewriting.Term a b -> Bool) ->
                                   Bool ->
                                     [(Term_Rewriting.Term a b,
Term_Rewriting.Term a b)] ->
                                       (Term_Rewriting.Term a b,
 Term_Rewriting.Term a b) ->
 Term_Rewriting.Term a b ->
   Term_Rewriting.Term a b -> Sum_Type.Sum (String -> String) ();
check_rqrstep nf nfs r rule s t = check_qrstep nf nfs r [] rule s t;

check_qsteps ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Term_Rewriting.Showl b) => (Term_Rewriting.Term a b -> Bool) ->
                                   Bool ->
                                     [(Term_Rewriting.Term a b,
Term_Rewriting.Term a b)] ->
                                       [(Term_Rewriting.Term a b,
  Term_Rewriting.Term a b)] ->
 [([Arith.Nat],
    ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
      (Bool, Term_Rewriting.Term a b)))] ->
   Term_Rewriting.Term a b ->
     Term_Rewriting.Term a b -> Sum_Type.Sum (String -> String) ();
check_qsteps nf nfs p r [] s u =
  Check_Monad.check (Term_Rewriting.equal_term s u)
    ((((Term_Rewriting.showsl_literal
          "the last term of the rewrite sequence\n" .
         Term_Rewriting.showsl_terma s) .
        Term_Rewriting.showsl_literal
          "\ndoes not correspond to the goal term\n") .
       Term_Rewriting.showsl_terma u) .
      Term_Rewriting.showsl_literal "\n");
check_qsteps nf nfs p ra ((uu, (r, (True, t))) : prts) s u =
  Error_Monad.bind (check_rqrstep nf nfs p r s t)
    (\ _ -> check_qsteps nf nfs p ra prts t u);
check_qsteps nf nfs pa ra ((p, (r, (False, t))) : prts) s u =
  Error_Monad.bind (check_qrstep nf nfs ra p r s t)
    (\ _ -> check_qsteps nf nfs pa ra prts t u);

check_prop_rstepa ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Term_Rewriting.Showl b) => Bool ->
                                   (Term_Rewriting.Term a b ->
                                     Sum_Type.Sum (String -> String) ()) ->
                                     [(Term_Rewriting.Term a b,
Term_Rewriting.Term a b)] ->
                                       [Arith.Nat] ->
 (Term_Rewriting.Term a b, Term_Rewriting.Term a b) ->
   Term_Rewriting.Term a b ->
     Term_Rewriting.Term a b -> Sum_Type.Sum (String -> String) ();
check_prop_rstepa nfs pa r p rule s t =
  Error_Monad.bind
    (Check_Monad.check (Arith.membera r rule)
      (((Term_Rewriting.showsl_rule rule .
          Term_Rewriting.showsl_literal " is not a rule of\n") .
         Term_Rewriting.showsl_trs r) .
        Term_Rewriting.showsl_literal "\n"))
    (\ _ -> check_prop_rstep_rule nfs pa p rule s t);

check_rstep ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Term_Rewriting.Showl b) => [(Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b)] ->
                                   [Arith.Nat] ->
                                     (Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b) ->
                                       Term_Rewriting.Term a b ->
 Term_Rewriting.Term a b -> Sum_Type.Sum (String -> String) ();
check_rstep = check_prop_rstepa False (\ _ -> Sum_Type.Inr ());

check_qrsteps ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Term_Rewriting.Showl b) => (Term_Rewriting.Term a b -> Bool) ->
                                   Bool ->
                                     [(Term_Rewriting.Term a b,
Term_Rewriting.Term a b)] ->
                                       [([Arith.Nat],
  ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
    Term_Rewriting.Term a b))] ->
 Term_Rewriting.Term a b ->
   Term_Rewriting.Term a b -> Sum_Type.Sum (String -> String) ();
check_qrsteps nf nfs r prts s u =
  check_qsteps nf nfs [] r (map (\ (p, (ra, t)) -> (p, (ra, (False, t)))) prts)
    s u;

check_rsteps ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Term_Rewriting.Showl b) => [(Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b)] ->
                                   [([Arith.Nat],
                                      ((Term_Rewriting.Term a b,
 Term_Rewriting.Term a b),
Term_Rewriting.Term a b))] ->
                                     Term_Rewriting.Term a b ->
                                       Term_Rewriting.Term a b ->
 Sum_Type.Sum (String -> String) ();
check_rsteps = check_qrsteps (\ _ -> True) False;

is_NF_subset ::
  forall a b.
    (Term_Rewriting.Term a b -> Bool) -> [Term_Rewriting.Term a b] -> Bool;
is_NF_subset is_Q_nf q = all (\ qa -> not (is_Q_nf qa)) q;

nF_subst_impl ::
  forall a b.
    (Term_Rewriting.Term a b -> Bool) ->
      Bool ->
        (Term_Rewriting.Term a b, Term_Rewriting.Term a b) ->
          (b -> Term_Rewriting.Term a b) -> Bool;
nF_subst_impl nf nfs r sigma =
  (if nfs then all (\ x -> nf (sigma x)) (Term_Rewriting.vars_rule_list r)
    else True);

applicable_rule_impl ::
  forall a b.
    (Term_Rewriting.Term a b -> Bool) ->
      (Term_Rewriting.Term a b, Term_Rewriting.Term a b) -> Bool;
applicable_rule_impl isNF = (\ (l, _) -> all isNF (Term_Rewriting.args l));

wwf_qtrs_impl ::
  forall a b.
    (Eq b) => (Term_Rewriting.Term a b -> Bool) ->
                [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] -> Bool;
wwf_qtrs_impl nf r =
  all (\ ra -> Term_Rewriting.wf_rule ra || not (applicable_rule_impl nf ra)) r;

check_wwf_qtrs ::
  forall a b.
    (Term_Rewriting.Showl a, Eq b,
      Term_Rewriting.Showl b) => (Term_Rewriting.Term a b -> Bool) ->
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)] ->
                                     Sum_Type.Sum (String -> String) ();
check_wwf_qtrs nf r =
  Error_Monad.catch_error
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ ra ->
          (if applicable_rule_impl nf ra
            then Error_Monad.catch_error
                   (Error_Monad.bind
                     (Check_Monad.check (not (Term_Rewriting.is_Var (fst ra)))
                       (Term_Rewriting.showsl_literal
                         "variable left-hand side in"))
                     (\ _ ->
                       Error_Monad.catch_error
                         (Check_Monad.check_subseteq
                           (Term_Rewriting.vars_term_list (snd ra))
                           (Term_Rewriting.vars_term_list (fst ra)))
                         (\ x ->
                           Sum_Type.Inl
                             ((Term_Rewriting.showsl_literal "free variable " .
                                Term_Rewriting.showsl x) .
                               Term_Rewriting.showsl_literal
                                 " in right-hand side of"))))
                   (\ x ->
                     Sum_Type.Inl
                       (((x . Term_Rewriting.showsl_literal " rule ") .
                          Term_Rewriting.showsl_rule ra) .
                         Term_Rewriting.showsl_literal "\n"))
            else Sum_Type.Inr ()))
        r)
      (\ x -> Sum_Type.Inl (snd x)))
    (\ x ->
      Sum_Type.Inl
        (Term_Rewriting.showsl_literal "the Q-TRS is not weakly well-formed\n" .
          x));

is_NF_trs_subset ::
  forall a b.
    (Term_Rewriting.Term a b -> Bool) ->
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] -> Bool;
is_NF_trs_subset is_Q_nf r = is_NF_subset is_Q_nf (map fst r);

check_NF_terms_subset ::
  forall a b.
    (Term_Rewriting.Term a b -> Bool) ->
      [Term_Rewriting.Term a b] -> Sum_Type.Sum (Term_Rewriting.Term a b) ();
check_NF_terms_subset is_Q_nf =
  (\ q ->
    Error_Monad.catch_error
      (Error_Monad.forallM
        (\ x -> (if not (is_Q_nf x) then Sum_Type.Inr () else Sum_Type.Inl x))
        q)
      (\ x -> Sum_Type.Inl (snd x)));

check_NF_terms_eq ::
  forall a b.
    (Compare.Compare_order a, Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => [Term_Rewriting.Term a b] ->
                                   [Term_Rewriting.Term a b] ->
                                     Sum_Type.Sum (Term_Rewriting.Term a b) ();
check_NF_terms_eq qa q =
  Error_Monad.bind (check_NF_terms_subset (Term_Rewriting.is_NF_terms qa) q)
    (\ _ -> check_NF_terms_subset (Term_Rewriting.is_NF_terms q) qa);

check_rsteps_last ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Term_Rewriting.Showl b) => [(Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b)] ->
                                   Term_Rewriting.Term a b ->
                                     [([Arith.Nat],
((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
  Term_Rewriting.Term a b))] ->
                                       Sum_Type.Sum (String -> String) ();
check_rsteps_last = (\ r s steps -> check_rsteps r steps s (rseq_last s steps));

check_NF_trs_subset ::
  forall a b.
    (Compare.Compare_order a, Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => [(Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b)] ->
                                   [Term_Rewriting.Term a b] ->
                                     Sum_Type.Sum (Term_Rewriting.Term a b) ();
check_NF_trs_subset r = check_NF_terms_subset (Term_Rewriting.is_NF_trs r);

check_NF_vars_subset ::
  forall a b.
    (Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => [Term_Rewriting.Term a b] ->
                                   [Term_Rewriting.Term a b] ->
                                     Sum_Type.Sum (Term_Rewriting.Term a b) ();
check_NF_vars_subset qa q =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ qaa -> Check_Monad.check (any (Term_Rewriting.matches qaa) q) qaa) qa)
    (\ x -> Sum_Type.Inl (snd x));

check_no_defined_root ::
  forall a b.
    (Term_Rewriting.Showl a,
      Term_Rewriting.Showl b) => ((a, Arith.Nat) -> Bool) ->
                                   Term_Rewriting.Term a b ->
                                     Sum_Type.Sum (String -> String) ();
check_no_defined_root isdef t =
  Check_Monad.check (not (isdef (Arith.the (Term_Rewriting.root t))))
    ((Term_Rewriting.showsl_literal "the root of " .
       Term_Rewriting.showsl_terma t) .
      Term_Rewriting.showsl_literal " is defined");

check_non_applicable_rules ::
  forall a b.
    (Term_Rewriting.Term a b -> Bool) ->
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
        Sum_Type.Sum (Term_Rewriting.Term a b, Term_Rewriting.Term a b) ();
check_non_applicable_rules isNF r =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ x ->
        (if not (applicable_rule_impl isNF x) then Sum_Type.Inr ()
          else Sum_Type.Inl x))
      r)
    (\ x -> Sum_Type.Inl (snd x));

}
