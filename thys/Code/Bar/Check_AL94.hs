{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Check_AL94(Unfeasible_proof(..), Context_joinable_proof(..), orig_term,
              check_al94, orig_cstep)
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
import qualified Fresh;
import qualified Trs_Impl_More;
import qualified Conditional_Rewriting;
import qualified AL94;
import qualified Dependency_Pair_Problem_Spec;
import qualified Termination_Problem_Spec;
import qualified Check_Infeasibility;
import qualified Countable;
import qualified HOL;
import qualified Compare;
import qualified Labelings_Impl;
import qualified Labelings;
import qualified Mapping;
import qualified Lists_are_Infinite;
import qualified Position;
import qualified Error_Monad;
import qualified Check_Monad;
import qualified Sum_Type;
import qualified Shows_Literal;
import qualified Arith;
import qualified Conditional_Rewriting_Impl;
import qualified Term_Rewriting;

data Unfeasible_proof a b =
  UnfeasibleOverlap (Term_Rewriting.Term a b) (Term_Rewriting.Term a b)
    (Term_Rewriting.Term a b) [Conditional_Rewriting_Impl.Cstep_proof a b]
    [Conditional_Rewriting_Impl.Cstep_proof a b]
    ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)])
    ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]);

data Context_joinable_proof a b =
  Contextual_Join (Term_Rewriting.Term a b)
    [Conditional_Rewriting_Impl.Cstep_proof a b]
    [Conditional_Rewriting_Impl.Cstep_proof a b];

orig_term ::
  forall a b.
    (a -> Maybe b) -> Term_Rewriting.Term a b -> Term_Rewriting.Term a b;
orig_term m (Term_Rewriting.Var x) = Term_Rewriting.Var x;
orig_term m (Term_Rewriting.Fun f []) = (case m f of {
  Nothing -> Term_Rewriting.Fun f [];
  Just a -> Term_Rewriting.Var a;
});
orig_term m (Term_Rewriting.Fun f (v : va)) =
  Term_Rewriting.Fun f (map (orig_term m) (v : va));

check_airr ::
  forall a.
    (Eq a,
      Shows_Literal.Showl a) => [((Term_Rewriting.Term a [Arith.Char],
                                    Term_Rewriting.Term a [Arith.Char]),
                                   [(Term_Rewriting.Term a [Arith.Char],
                                      Term_Rewriting.Term a [Arith.Char])])] ->
                                  Term_Rewriting.Term a [Arith.Char] ->
                                    Sum_Type.Sum (String -> String) ();
check_airr r t =
  Error_Monad.catch_error
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ cr ->
          Error_Monad.catch_error
            (Error_Monad.forallM
              (\ p ->
                Check_Monad.check
                  (Arith.is_none
                    (Term_Rewriting.mgu_vd_string (Term_Rewriting.subt_at t p)
                      (fst (fst cr))))
                  (((((Shows_Literal.showsl_lit "the term " .
                        Term_Rewriting.showsl_terma t) .
                       Shows_Literal.showsl_lit
                         " is unifiable with the left-hand side of rule ") .
                      Conditional_Rewriting_Impl.showsl_crule cr) .
                     Shows_Literal.showsl_lit " at position ") .
                    Position.showsl_pos p))
              (Term_Rewriting.fun_poss_list t))
            (\ x -> Sum_Type.Inl (snd x)))
        r)
      (\ x -> Sum_Type.Inl (snd x)))
    (\ x ->
      Sum_Type.Inl
        (((Shows_Literal.showsl_lit "the term " .
            Term_Rewriting.showsl_terma t) .
           Shows_Literal.showsl_lit " is not absolutely irreducible") .
          x));

skol_crule ::
  forall a b.
    (Compare.Compare a, Eq a, Arith.Ceq b, Arith.Ccompare b, Compare.Compare b,
      Eq b) => Arith.Set
                 ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                   [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]) ->
                 Arith.Set b ->
                   ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                     [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]) ->
                     ((Term_Rewriting.Term (Sum_Type.Sum a b) b,
                        Term_Rewriting.Term (Sum_Type.Sum a b) b),
                       [(Term_Rewriting.Term (Sum_Type.Sum a b) b,
                          Term_Rewriting.Term (Sum_Type.Sum a b) b)]);
skol_crule ra v r =
  (if Arith.member r ra then Conditional_Rewriting.map_funs_crule Sum_Type.Inl r
    else ((AL94.skol v (fst (fst r)), AL94.skol v (snd (fst r))),
           map (\ (s, t) -> (AL94.skol v s, AL94.skol v t)) (snd r)));

skol_cstep_proof ::
  forall a b.
    (Compare.Compare a, Eq a, Arith.Ceq b, Arith.Ccompare b, Compare.Compare b,
      Eq b) => Arith.Set
                 ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                   [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]) ->
                 Arith.Set b ->
                   Conditional_Rewriting_Impl.Cstep_proof a b ->
                     Conditional_Rewriting_Impl.Cstep_proof (Sum_Type.Sum a b)
                       b;
skol_cstep_proof r v (Conditional_Rewriting_Impl.Cstep_step rho p sigma s t pss)
  = Conditional_Rewriting_Impl.Cstep_step (skol_crule r v rho) p
      (AL94.skol v . sigma) (AL94.skol v s) (AL94.skol v t)
      (map (map (skol_cstep_proof r v)) pss);

map_funs_crules ::
  forall a b c.
    (a -> b) ->
      [((Term_Rewriting.Term a c, Term_Rewriting.Term a c),
         [(Term_Rewriting.Term a c, Term_Rewriting.Term a c)])] ->
        [((Term_Rewriting.Term b c, Term_Rewriting.Term b c),
           [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)])];
map_funs_crules f r = map (Conditional_Rewriting.map_funs_crule f) r;

rules2crules ::
  forall a b.
    [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
      [((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
         [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)])];
rules2crules rs = map (\ r -> (r, [])) rs;

skol_rules ::
  forall a b.
    (Compare.Compare a, Eq a, Arith.Finite_UNIV b, Arith.Cenum b, Arith.Ceq b,
      Arith.Cproper_interval b, Compare.Compare b, Eq b,
      Arith.Set_impl b) => [(Term_Rewriting.Term a b,
                              Term_Rewriting.Term a b)] ->
                             [(Term_Rewriting.Term (Sum_Type.Sum a b) b,
                                Term_Rewriting.Term (Sum_Type.Sum a b) b)];
skol_rules cs = let {
                  v = Term_Rewriting.vars_trs (Arith.set cs);
                } in map (\ (l, r) -> (AL94.skol v l, AL94.skol v r)) cs;

check_context_joinablea ::
  forall a b.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a, Arith.Finite_UNIV b,
      Arith.Cenum b, Arith.Ceq b, Arith.Cproper_interval b, Compare.Compare b,
      Eq b, Mapping.Mapping_impl b, Arith.Set_impl b,
      Shows_Literal.Showl b) => Context_joinable_proof a b ->
                                  [((Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b),
                                     [(Term_Rewriting.Term a b,
Term_Rewriting.Term a b)])] ->
                                    Term_Rewriting.Term a b ->
                                      Term_Rewriting.Term a b ->
[(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
  Sum_Type.Sum (String -> String) ();
check_context_joinablea (Contextual_Join u ps qs) r s t cs =
  Error_Monad.catch_error
    (let {
       c = skol_rules cs;
       v = Term_Rewriting.vars_trs (Arith.set cs);
       sa = AL94.skol v s;
       ta = AL94.skol v t;
       ua = AL94.skol v u;
       psa = map (skol_cstep_proof (Arith.set r) v) ps;
       qsa = map (skol_cstep_proof (Arith.set r) v) qs;
       ra = map_funs_crules Sum_Type.Inl r ++ rules2crules c;
     } in Error_Monad.bind
            (Conditional_Rewriting_Impl.check_csteps ra sa ua psa)
            (\ _ -> Conditional_Rewriting_Impl.check_csteps ra ta ua qsa))
    (\ x ->
      Sum_Type.Inl
        ((((Term_Rewriting.showsl_terma s . Shows_Literal.showsl_lit " and ") .
            Term_Rewriting.showsl_terma t) .
           Shows_Literal.showsl_lit " are not context-joinable\n") .
          x));

check_context_joinable ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a, Arith.Finite_UNIV b,
      Arith.Cenum b, Arith.Ceq b, Arith.Cproper_interval b, Compare.Compare b,
      Fresh.Infinite b, Eq b, Mapping.Mapping_impl b, Arith.Set_impl b,
      Shows_Literal.Showl b) => [(Term_Rewriting.Term a b,
                                   (Term_Rewriting.Term a b,
                                     ([(Term_Rewriting.Term a b,
 Term_Rewriting.Term a b)],
                                       Context_joinable_proof a b)))] ->
                                  [((Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b),
                                     [(Term_Rewriting.Term a b,
Term_Rewriting.Term a b)])] ->
                                    Term_Rewriting.Term a b ->
                                      Term_Rewriting.Term a b ->
[(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
  Sum_Type.Sum (String -> String) ();
check_context_joinable cj r s t cs =
  Error_Monad.catch_error
    (Error_Monad.existsM
      (\ (sa, (ta, (csa, p))) ->
        Error_Monad.bind
          (Check_Monad.check
            (not (Arith.is_none
                   (Trs_Impl_More.match_rules ((s, t) : cs) ((sa, ta) : csa))))
            id)
          (\ _ ->
            Error_Monad.bind
              (Check_Monad.check
                (not (Arith.is_none
                       (Trs_Impl_More.match_rules ((sa, ta) : csa)
                         ((s, t) : cs))))
                id)
              (\ _ -> check_context_joinablea p r sa ta csa)))
      cj)
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_sep id (Shows_Literal.showsl_literal "\n") x));

check_overlap ::
  forall a b.
    (Arith.Ccompare a, Fresh.Infinite a, Eq a, Mapping.Mapping_impl a,
      Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => (a -> a) ->
                                  (a -> a) ->
                                    ([((Term_Rewriting.Term b a,
 Term_Rewriting.Term b a),
[(Term_Rewriting.Term b a, Term_Rewriting.Term b a)])] ->
                                      Term_Rewriting.Term b a ->
Term_Rewriting.Term b a ->
  [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
    Sum_Type.Sum (String -> String) ()) ->
                                      ([((Term_Rewriting.Term b a,
   Term_Rewriting.Term b a),
  [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)])] ->
[(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
  Sum_Type.Sum (String -> String) ()) ->
([((Term_Rewriting.Term b a, Term_Rewriting.Term b a),
    [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)])] ->
  Term_Rewriting.Term b a ->
    (a -> Term_Rewriting.Term b a) ->
      [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
        Sum_Type.Sum (String -> String) ()) ->
  [((Term_Rewriting.Term b a, Term_Rewriting.Term b a),
     [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)])] ->
    ((Term_Rewriting.Term b a, Term_Rewriting.Term b a),
      [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)]) ->
      ((Term_Rewriting.Term b a, Term_Rewriting.Term b a),
        [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)]) ->
        [Arith.Nat] -> Sum_Type.Sum (String -> String) ();
check_overlap xvar yvar check_context_joinable check_infeasible check_unfeasible
  r rho_1 rho_2 p =
  Error_Monad.catch_error
    (case Term_Rewriting.mgu_var_disjoint_generic xvar yvar
            (Term_Rewriting.subt_at (fst (fst rho_1)) p) (fst (fst rho_2))
      of {
      Nothing -> Sum_Type.Inr ();
      Just (sigma_1, sigma_2) ->
        let {
          cs = Term_Rewriting.subst_list sigma_1 (snd rho_1) ++
                 Term_Rewriting.subst_list sigma_2 (snd rho_2);
          s = Term_Rewriting.eval_term Term_Rewriting.Fun (snd (fst rho_1))
                sigma_1;
          t = Term_Rewriting.intp_actxt Term_Rewriting.Fun
                (Term_Rewriting.ctxt_of_pos_term p
                  (Term_Rewriting.eval_term Term_Rewriting.Fun (fst (fst rho_1))
                    sigma_1))
                (Term_Rewriting.eval_term Term_Rewriting.Fun (snd (fst rho_2))
                  sigma_2);
        } in Error_Monad.catch_error
               (Error_Monad.choice
                 [Error_Monad.catch_error
                    (Error_Monad.bind (Check_Monad.check (null p) id)
                      (\ _ ->
                        Conditional_Rewriting_Impl.check_crule_variants rho_1
                          rho_2))
                    (\ x ->
                      Sum_Type.Inl
                        (Shows_Literal.showsl_lit "the overlap is critical\n" .
                          x)),
                   Error_Monad.catch_error (check_context_joinable r s t cs)
                     (\ x ->
                       Sum_Type.Inl
                         (Shows_Literal.showsl_lit
                            "could not be shown to be context-joinable\n" .
                           x)),
                   Error_Monad.catch_error (check_infeasible r cs)
                     (\ x ->
                       Sum_Type.Inl
                         (Shows_Literal.showsl_lit
                            "could not be shown to be infeasible\n" .
                           x)),
                   Error_Monad.catch_error
                     (check_unfeasible r (fst (fst rho_1)) sigma_1 cs)
                     (\ x ->
                       Sum_Type.Inl
                         (Shows_Literal.showsl_lit
                            "could not be shown to be unfeasible\n" .
                           x))])
               (\ x ->
                 Sum_Type.Inl
                   (Shows_Literal.showsl_sep id
                     (Shows_Literal.showsl_literal "\n") x));
    })
    (\ x ->
      Sum_Type.Inl
        ((Conditional_Rewriting_Impl.showsl_coverlap rho_1 rho_2 p .
           Shows_Literal.showsl_lit ":\n\n") .
          x));

check_CCPs ::
  forall a b.
    (Arith.Ccompare a, Fresh.Infinite a, Eq a, Mapping.Mapping_impl a,
      Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => (a -> a) ->
                                  (a -> a) ->
                                    ([((Term_Rewriting.Term b a,
 Term_Rewriting.Term b a),
[(Term_Rewriting.Term b a, Term_Rewriting.Term b a)])] ->
                                      Term_Rewriting.Term b a ->
Term_Rewriting.Term b a ->
  [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
    Sum_Type.Sum (String -> String) ()) ->
                                      ([((Term_Rewriting.Term b a,
   Term_Rewriting.Term b a),
  [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)])] ->
[(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
  Sum_Type.Sum (String -> String) ()) ->
([((Term_Rewriting.Term b a, Term_Rewriting.Term b a),
    [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)])] ->
  Term_Rewriting.Term b a ->
    (a -> Term_Rewriting.Term b a) ->
      [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
        Sum_Type.Sum (String -> String) ()) ->
  [((Term_Rewriting.Term b a, Term_Rewriting.Term b a),
     [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)])] ->
    Sum_Type.Sum (String -> String) ();
check_CCPs xvar yvar check_context_joinable check_infeasible check_unfeasible r
  = Error_Monad.catch_error
      (Error_Monad.forallM
        (\ rho_1 ->
          let {
            l_1 = fst (fst rho_1);
          } in Error_Monad.catch_error
                 (Error_Monad.forallM
                   (\ rho_2 ->
                     Error_Monad.catch_error
                       (Error_Monad.forallM
                         (check_overlap xvar yvar check_context_joinable
                           check_infeasible check_unfeasible r rho_1 rho_2)
                         (Term_Rewriting.fun_poss_list l_1))
                       (\ x -> Sum_Type.Inl (snd x)))
                   r)
                 (\ x -> Sum_Type.Inl (snd x)))
        r)
      (\ x -> Sum_Type.Inl (snd x));

rule2 ::
  forall a b.
    Unfeasible_proof a b ->
      ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
        [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]);
rule2 (UnfeasibleOverlap x1 x2 x3 x4 x5 x6 x7) = x7;

rule1 ::
  forall a b.
    Unfeasible_proof a b ->
      ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
        [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]);
rule1 (UnfeasibleOverlap x1 x2 x3 x4 x5 x6 x7) = x6;

check_unfeasiblea ::
  forall a.
    (Compare.Compare a, Eq a,
      Shows_Literal.Showl a) => Unfeasible_proof a [Arith.Char] ->
                                  [((Term_Rewriting.Term a [Arith.Char],
                                      Term_Rewriting.Term a [Arith.Char]),
                                     [(Term_Rewriting.Term a [Arith.Char],
Term_Rewriting.Term a [Arith.Char])])] ->
                                    Term_Rewriting.Term a [Arith.Char] ->
                                      ([Arith.Char] ->
Term_Rewriting.Term a [Arith.Char]) ->
[(Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char])] ->
  Sum_Type.Sum (String -> String) ();
check_unfeasiblea (UnfeasibleOverlap t u v ps qs rho_1 rho_2) r l mu cs =
  Error_Monad.catch_error
    (let {
       c = skol_rules cs;
       va = Term_Rewriting.vars_trs (Arith.set cs);
       ta = AL94.skol va t;
       ua = AL94.skol va u;
       vb = AL94.skol va v;
       psa = map (skol_cstep_proof (Arith.set r) va) ps;
       qsa = map (skol_cstep_proof (Arith.set r) va) qs;
       ra = map_funs_crules Sum_Type.Inl r ++ rules2crules c;
     } in Error_Monad.bind
            (Check_Monad.check (Term_Rewriting.equal_term l (fst (fst rho_1)))
              id)
            (\ _ ->
              Error_Monad.bind
                (Check_Monad.check
                  (all (\ (a, b) ->
                         (case a of {
                           (la, _) -> (\ _ -> not (Term_Rewriting.is_Var la));
                         })
                           b)
                    r)
                  (Shows_Literal.showsl_lit "variable left-hand side"))
                (\ _ ->
                  Error_Monad.bind
                    (Conditional_Rewriting_Impl.check_variant_in_ctrs r rho_1)
                    (\ _ ->
                      Error_Monad.bind
                        (Conditional_Rewriting_Impl.check_variant_in_ctrs r
                          rho_2)
                        (\ _ ->
                          Error_Monad.bind
                            (Check_Monad.check
                              (Term_Rewriting.equal_term
                                 (Term_Rewriting.eval_term Term_Rewriting.Fun l
                                   mu)
                                 (Term_Rewriting.eval_term Term_Rewriting.Fun
                                   (fst (fst rho_2)) mu) ||
                                Term_Rewriting.supt_impl
                                  (Term_Rewriting.eval_term Term_Rewriting.Fun l
                                    mu)
                                  (Term_Rewriting.eval_term Term_Rewriting.Fun
                                    (fst (fst rho_2)) mu))
                              id)
                            (\ _ ->
                              Error_Monad.bind
                                (Check_Monad.check
                                  (Arith.member t
                                    (Arith.image fst (Arith.set cs)))
                                  id)
                                (\ _ ->
                                  Error_Monad.bind
                                    (Check_Monad.check
                                      (cs ==
Term_Rewriting.subst_list mu (snd rho_1 ++ snd rho_2))
                                      id)
                                    (\ _ ->
                                      Error_Monad.bind
(Conditional_Rewriting_Impl.check_csteps ra ta ua psa)
(\ _ ->
  Error_Monad.bind (Conditional_Rewriting_Impl.check_csteps ra ta vb qsa)
    (\ _ ->
      Error_Monad.bind (check_airr r u)
        (\ _ ->
          Error_Monad.bind (check_airr r v)
            (\ _ ->
              Check_Monad.check (Arith.is_none (Term_Rewriting.mgu u v))
                (((Term_Rewriting.showsl_terma u .
                    Shows_Literal.showsl_lit " and ") .
                   Term_Rewriting.showsl_terma v) .
                  Shows_Literal.showsl_lit " are unifiable")))))))))))))
    (\ x ->
      Sum_Type.Inl
        (((Shows_Literal.showsl_lit "conditions " .
            Conditional_Rewriting_Impl.showsl_conditions cs) .
           Shows_Literal.showsl_lit " are not unfeasible\n") .
          x));

check_unfeasible ::
  forall a.
    (Compare.Compare_order a, Eq a,
      Shows_Literal.Showl a) => [([Arith.Char] ->
                                    Term_Rewriting.Term a [Arith.Char],
                                   Unfeasible_proof a [Arith.Char])] ->
                                  [((Term_Rewriting.Term a [Arith.Char],
                                      Term_Rewriting.Term a [Arith.Char]),
                                     [(Term_Rewriting.Term a [Arith.Char],
Term_Rewriting.Term a [Arith.Char])])] ->
                                    Term_Rewriting.Term a [Arith.Char] ->
                                      ([Arith.Char] ->
Term_Rewriting.Term a [Arith.Char]) ->
[(Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char])] ->
  Sum_Type.Sum (String -> String) ();
check_unfeasible css r l mu cs =
  Error_Monad.catch_error
    (Error_Monad.existsM
      (\ (mua, uo) ->
        let {
          cs_1 = snd (rule1 uo);
          cs_2 = snd (rule2 uo);
          csa = Term_Rewriting.subst_list mua (cs_1 ++ cs_2);
          la = fst (fst (rule1 uo));
        } in Error_Monad.bind
               (Check_Monad.check
                 (Arith.equal_nat (Arith.size_list csa) (Arith.size_list cs))
                 (Shows_Literal.showsl_lit "lengths differ"))
               (\ _ ->
                 Error_Monad.bind
                   (Check_Monad.check
                     (not (Arith.is_none
                            (Trs_Impl_More.match_rules
                              ((Term_Rewriting.eval_term Term_Rewriting.Fun l
                                  mu,
                                 Term_Rewriting.eval_term Term_Rewriting.Fun l
                                   mu) :
                                cs)
                              ((Term_Rewriting.eval_term Term_Rewriting.Fun la
                                  mua,
                                 Term_Rewriting.eval_term Term_Rewriting.Fun la
                                   mua) :
                                csa))) &&
                       not (Arith.is_none
                             (Trs_Impl_More.match_rules
                               ((Term_Rewriting.eval_term Term_Rewriting.Fun la
                                   mua,
                                  Term_Rewriting.eval_term Term_Rewriting.Fun la
                                    mua) :
                                 csa)
                               ((Term_Rewriting.eval_term Term_Rewriting.Fun l
                                   mu,
                                  Term_Rewriting.eval_term Term_Rewriting.Fun l
                                    mu) :
                                 cs))))
                     id)
                   (\ _ -> check_unfeasiblea uo r la mua csa)))
      css)
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_sep id (Shows_Literal.showsl_literal "\n") x));

check_infeasible ::
  forall a b c d e.
    (Compare.Compare_order c, Countable.Countable c, HOL.Default c, Eq c,
      Shows_Literal.Showl c) => a -> (String -> String) ->
                                       Termination_Problem_Spec.Tp_ops_ext b
 (Labelings.Lab c [Arith.Nat]) [Arith.Char] () ->
 Dependency_Pair_Problem_Spec.Dpp_ops_ext d (Labelings.Lab c [Arith.Nat])
   [Arith.Char] () ->
   [([(Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char],
        Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char])],
      Check_Infeasibility.Infeasibility_proof c [Arith.Char] e [Arith.Nat])] ->
     [((Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char],
         Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char]),
        [(Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char],
           Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char])])] ->
       [(Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char],
          Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char])] ->
         Sum_Type.Sum (String -> String) ();
check_infeasible a ia i j css r cs =
  Error_Monad.catch_error
    (Error_Monad.existsM
      (\ (csa, p) ->
        Error_Monad.bind
          (Check_Monad.check
            (Arith.equal_nat (Arith.size_list csa) (Arith.size_list cs))
            (Shows_Literal.showsl_lit "lengths differ"))
          (\ _ ->
            Error_Monad.bind
              (Check_Monad.check
                (not (Arith.is_none (Trs_Impl_More.match_rules cs csa)) &&
                  not (Arith.is_none (Trs_Impl_More.match_rules csa cs)))
                id)
              (\ _ -> Check_Infeasibility.check_infeasible a ia i j r csa p)))
      css)
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_sep id (Shows_Literal.showsl_literal "\n") x));

check_adtrs ::
  forall a.
    (Eq a,
      Shows_Literal.Showl a) => [((Term_Rewriting.Term a [Arith.Char],
                                    Term_Rewriting.Term a [Arith.Char]),
                                   [(Term_Rewriting.Term a [Arith.Char],
                                      Term_Rewriting.Term a [Arith.Char])])] ->
                                  Sum_Type.Sum (String -> String) ();
check_adtrs r =
  Error_Monad.catch_error
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ cr ->
          Error_Monad.catch_error
            (Error_Monad.forallM (\ i -> let {
   a = snd (Arith.nth (snd cr) i);
 } in check_airr r a)
              (Arith.upt Arith.zero_nat (Arith.size_list (snd cr))))
            (\ x -> Sum_Type.Inl (snd x)))
        r)
      (\ x -> Sum_Type.Inl (snd x)))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit "the CTRS is not absolutely deterministic\n" .
          x));

check_al94 ::
  forall a b c d e.
    (Compare.Compare_order c, Countable.Countable c, HOL.Default c, Eq c,
      Shows_Literal.Showl c) => a -> (String -> String) ->
                                       Termination_Problem_Spec.Tp_ops_ext b
 (Labelings.Lab c [Arith.Nat]) [Arith.Char] () ->
 Dependency_Pair_Problem_Spec.Dpp_ops_ext d (Labelings.Lab c [Arith.Nat])
   [Arith.Char] () ->
   [(Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char],
      (Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char],
        ([(Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char],
            Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char])],
          Context_joinable_proof (Labelings.Lab c [Arith.Nat])
            [Arith.Char])))] ->
     [([(Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char],
          Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char])],
        Check_Infeasibility.Infeasibility_proof c [Arith.Char] e
          [Arith.Nat])] ->
       [([Arith.Char] ->
           Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char],
          Unfeasible_proof (Labelings.Lab c [Arith.Nat]) [Arith.Char])] ->
         [((Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char],
             Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char]),
            [(Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char],
               Term_Rewriting.Term (Labelings.Lab c [Arith.Nat])
                 [Arith.Char])])] ->
           Sum_Type.Sum (String -> String) ();
check_al94 a ia i j cj css uo r =
  Error_Monad.catch_error
    (Error_Monad.bind (Conditional_Rewriting_Impl.check_wf_ctrs r)
      (\ _ ->
        Error_Monad.bind (check_adtrs r)
          (\ _ ->
            check_CCPs (\ aa -> Arith.char_0x78 : aa)
              (\ aa -> Arith.char_0x79 : aa) (check_context_joinable cj)
              (check_infeasible a ia i j css) (check_unfeasible uo) r)))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "Avenhaus & Loria-Saenz 1994 does not apply\n" .
          x));

orig_crule ::
  forall a b.
    (a -> Maybe b) ->
      ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
        [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]) ->
        ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
          [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]);
orig_crule m r =
  ((orig_term m (fst (fst r)), orig_term m (snd (fst r))),
    map (\ (s, t) -> (orig_term m s, orig_term m t)) (snd r));

orig_cstep ::
  forall a b.
    (a -> Maybe b) ->
      Conditional_Rewriting_Impl.Cstep_proof a b ->
        Conditional_Rewriting_Impl.Cstep_proof a b;
orig_cstep m (Conditional_Rewriting_Impl.Cstep_step rho p sigma s t css) =
  Conditional_Rewriting_Impl.Cstep_step (orig_crule m rho) p
    (orig_term m . sigma) (orig_term m s) (orig_term m t)
    (map (map (orig_cstep m)) css);

}
