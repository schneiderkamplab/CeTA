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
import qualified Subterm_and_Context;
import qualified Fresh;
import qualified Unification;
import qualified Trs_Impl_More;
import qualified List;
import qualified Trs;
import qualified Conditional_Rewriting;
import qualified AL94;
import qualified Set;
import qualified Container_Setup;
import qualified Product_Type;
import qualified Dependency_Pair_Problem_Spec;
import qualified Termination_Problem_Spec;
import qualified Check_Infeasibility;
import qualified Countable;
import qualified HOL;
import qualified Compare;
import qualified Labelings_Impl;
import qualified Labelings;
import qualified Mapping_Impl;
import qualified Collection_Order;
import qualified Cardinality;
import qualified Collection_Enum;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Lists_are_Infinite;
import qualified Compare_Instances;
import qualified Unification_String;
import qualified Term_Impl;
import qualified Position;
import qualified Error_Monad;
import qualified Term_More;
import qualified Check_Monad;
import qualified Sum_Type;
import qualified Str;
import qualified Arith;
import qualified Shows_Literal;
import qualified Option;
import qualified Conditional_Rewriting_Impl;
import qualified Term;

data Unfeasible_proof a b =
  UnfeasibleOverlap (Term.Term a b) (Term.Term a b) (Term.Term a b)
    [Conditional_Rewriting_Impl.Cstep_proof a b]
    [Conditional_Rewriting_Impl.Cstep_proof a b]
    ((Term.Term a b, Term.Term a b), [(Term.Term a b, Term.Term a b)])
    ((Term.Term a b, Term.Term a b), [(Term.Term a b, Term.Term a b)]);

data Context_joinable_proof a b =
  Contextual_Join (Term.Term a b) [Conditional_Rewriting_Impl.Cstep_proof a b]
    [Conditional_Rewriting_Impl.Cstep_proof a b];

orig_term :: forall a b. (a -> Maybe b) -> Term.Term a b -> Term.Term a b;
orig_term m (Term.Var x) = Term.Var x;
orig_term m (Term.Fun f []) = (case m f of {
                                Nothing -> Term.Fun f [];
                                Just a -> Term.Var a;
                              });
orig_term m (Term.Fun f (v : va)) = Term.Fun f (map (orig_term m) (v : va));

check_airr ::
  forall a.
    (Eq a,
      Shows_Literal.Showl a) => [((Term.Term a [Str.Char],
                                    Term.Term a [Str.Char]),
                                   [(Term.Term a [Str.Char],
                                      Term.Term a [Str.Char])])] ->
                                  Term.Term a [Str.Char] ->
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
                  (Option.is_none
                    (Unification_String.mgu_vd_string (Term_More.subt_at t p)
                      (fst (fst cr))))
                  (((((Shows_Literal.showsl_lit "the term " .
                        Term_More.showsl_terma t) .
                       Shows_Literal.showsl_lit
                         " is unifiable with the left-hand side of rule ") .
                      Conditional_Rewriting_Impl.showsl_crule cr) .
                     Shows_Literal.showsl_lit " at position ") .
                    Position.showsl_pos p))
              (Term_Impl.fun_poss_list t))
            (\ x -> Sum_Type.Inl (snd x)))
        r)
      (\ x -> Sum_Type.Inl (snd x)))
    (\ x ->
      Sum_Type.Inl
        (((Shows_Literal.showsl_lit "the term " . Term_More.showsl_terma t) .
           Shows_Literal.showsl_lit " is not absolutely irreducible") .
          x));

skol_crule ::
  forall a b.
    (Compare.Compare a, Eq a, Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Compare.Compare b,
      Eq b) => Set.Set
                 ((Term.Term a b, Term.Term a b),
                   [(Term.Term a b, Term.Term a b)]) ->
                 Set.Set b ->
                   ((Term.Term a b, Term.Term a b),
                     [(Term.Term a b, Term.Term a b)]) ->
                     ((Term.Term (Sum_Type.Sum a b) b,
                        Term.Term (Sum_Type.Sum a b) b),
                       [(Term.Term (Sum_Type.Sum a b) b,
                          Term.Term (Sum_Type.Sum a b) b)]);
skol_crule ra v r =
  (if Set.member r ra then Conditional_Rewriting.map_funs_crule Sum_Type.Inl r
    else ((AL94.skol v (fst (fst r)), AL94.skol v (snd (fst r))),
           map (\ (s, t) -> (AL94.skol v s, AL94.skol v t)) (snd r)));

skol_cstep_proof ::
  forall a b.
    (Compare.Compare a, Eq a, Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Compare.Compare b,
      Eq b) => Set.Set
                 ((Term.Term a b, Term.Term a b),
                   [(Term.Term a b, Term.Term a b)]) ->
                 Set.Set b ->
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
      [((Term.Term a c, Term.Term a c), [(Term.Term a c, Term.Term a c)])] ->
        [((Term.Term b c, Term.Term b c), [(Term.Term b c, Term.Term b c)])];
map_funs_crules f r = map (Conditional_Rewriting.map_funs_crule f) r;

rules2crules ::
  forall a b.
    [(Term.Term a b, Term.Term a b)] ->
      [((Term.Term a b, Term.Term a b), [(Term.Term a b, Term.Term a b)])];
rules2crules rs = map (\ r -> (r, [])) rs;

skol_rules ::
  forall a b.
    (Compare.Compare a, Eq a, Cardinality.Finite_UNIV b,
      Collection_Enum.Cenum b, Collection_Eq.Ceq b,
      Collection_Order.Cproper_interval b, Compare.Compare b, Eq b,
      Set_Impl.Set_impl b) => [(Term.Term a b, Term.Term a b)] ->
                                [(Term.Term (Sum_Type.Sum a b) b,
                                   Term.Term (Sum_Type.Sum a b) b)];
skol_rules cs = let {
                  v = Trs.vars_trs (List.set cs);
                } in map (\ (l, r) -> (AL94.skol v l, AL94.skol v r)) cs;

check_context_joinablea ::
  forall a b.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a, Cardinality.Finite_UNIV b,
      Collection_Enum.Cenum b, Collection_Eq.Ceq b,
      Collection_Order.Cproper_interval b, Compare.Compare b, Eq b,
      Mapping_Impl.Mapping_impl b, Set_Impl.Set_impl b,
      Shows_Literal.Showl b) => Context_joinable_proof a b ->
                                  [((Term.Term a b, Term.Term a b),
                                     [(Term.Term a b, Term.Term a b)])] ->
                                    Term.Term a b ->
                                      Term.Term a b ->
[(Term.Term a b, Term.Term a b)] -> Sum_Type.Sum (String -> String) ();
check_context_joinablea (Contextual_Join u ps qs) r s t cs =
  Error_Monad.catch_error
    (let {
       c = skol_rules cs;
       v = Trs.vars_trs (List.set cs);
       sa = AL94.skol v s;
       ta = AL94.skol v t;
       ua = AL94.skol v u;
       psa = map (skol_cstep_proof (List.set r) v) ps;
       qsa = map (skol_cstep_proof (List.set r) v) qs;
       ra = map_funs_crules Sum_Type.Inl r ++ rules2crules c;
     } in Error_Monad.bind
            (Conditional_Rewriting_Impl.check_csteps ra sa ua psa)
            (\ _ -> Conditional_Rewriting_Impl.check_csteps ra ta ua qsa))
    (\ x ->
      Sum_Type.Inl
        ((((Term_More.showsl_terma s . Shows_Literal.showsl_lit " and ") .
            Term_More.showsl_terma t) .
           Shows_Literal.showsl_lit " are not context-joinable\n") .
          x));

check_context_joinable ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a,
      Cardinality.Finite_UNIV b, Collection_Enum.Cenum b, Collection_Eq.Ceq b,
      Collection_Order.Cproper_interval b, Compare.Compare b, Fresh.Infinite b,
      Eq b, Mapping_Impl.Mapping_impl b, Set_Impl.Set_impl b,
      Shows_Literal.Showl b) => [(Term.Term a b,
                                   (Term.Term a b,
                                     ([(Term.Term a b, Term.Term a b)],
                                       Context_joinable_proof a b)))] ->
                                  [((Term.Term a b, Term.Term a b),
                                     [(Term.Term a b, Term.Term a b)])] ->
                                    Term.Term a b ->
                                      Term.Term a b ->
[(Term.Term a b, Term.Term a b)] -> Sum_Type.Sum (String -> String) ();
check_context_joinable cj r s t cs =
  Error_Monad.catch_error
    (Error_Monad.existsM
      (\ (sa, (ta, (csa, p))) ->
        Error_Monad.bind
          (Check_Monad.check
            (not (Option.is_none
                   (Trs_Impl_More.match_rules ((s, t) : cs) ((sa, ta) : csa))))
            id)
          (\ _ ->
            Error_Monad.bind
              (Check_Monad.check
                (not (Option.is_none
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
    (Collection_Order.Ccompare a, Fresh.Infinite a, Eq a,
      Mapping_Impl.Mapping_impl a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => (a -> a) ->
                                  (a -> a) ->
                                    ([((Term.Term b a, Term.Term b a),
[(Term.Term b a, Term.Term b a)])] ->
                                      Term.Term b a ->
Term.Term b a ->
  [(Term.Term b a, Term.Term b a)] -> Sum_Type.Sum (String -> String) ()) ->
                                      ([((Term.Term b a, Term.Term b a),
  [(Term.Term b a, Term.Term b a)])] ->
[(Term.Term b a, Term.Term b a)] -> Sum_Type.Sum (String -> String) ()) ->
([((Term.Term b a, Term.Term b a), [(Term.Term b a, Term.Term b a)])] ->
  Term.Term b a ->
    (a -> Term.Term b a) ->
      [(Term.Term b a, Term.Term b a)] -> Sum_Type.Sum (String -> String) ()) ->
  [((Term.Term b a, Term.Term b a), [(Term.Term b a, Term.Term b a)])] ->
    ((Term.Term b a, Term.Term b a), [(Term.Term b a, Term.Term b a)]) ->
      ((Term.Term b a, Term.Term b a), [(Term.Term b a, Term.Term b a)]) ->
        [Arith.Nat] -> Sum_Type.Sum (String -> String) ();
check_overlap xvar yvar check_context_joinable check_infeasible check_unfeasible
  r rho_1 rho_2 p =
  Error_Monad.catch_error
    (case Unification.mgu_var_disjoint_generic xvar yvar
            (Term_More.subt_at (fst (fst rho_1)) p) (fst (fst rho_2))
      of {
      Nothing -> Sum_Type.Inr ();
      Just (sigma_1, sigma_2) ->
        let {
          cs = Unification.subst_list sigma_1 (snd rho_1) ++
                 Unification.subst_list sigma_2 (snd rho_2);
          s = Term.eval_term Term.Fun (snd (fst rho_1)) sigma_1;
          t = Subterm_and_Context.intp_actxt Term.Fun
                (Term_More.ctxt_of_pos_term p
                  (Term.eval_term Term.Fun (fst (fst rho_1)) sigma_1))
                (Term.eval_term Term.Fun (snd (fst rho_2)) sigma_2);
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
    (Collection_Order.Ccompare a, Fresh.Infinite a, Eq a,
      Mapping_Impl.Mapping_impl a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => (a -> a) ->
                                  (a -> a) ->
                                    ([((Term.Term b a, Term.Term b a),
[(Term.Term b a, Term.Term b a)])] ->
                                      Term.Term b a ->
Term.Term b a ->
  [(Term.Term b a, Term.Term b a)] -> Sum_Type.Sum (String -> String) ()) ->
                                      ([((Term.Term b a, Term.Term b a),
  [(Term.Term b a, Term.Term b a)])] ->
[(Term.Term b a, Term.Term b a)] -> Sum_Type.Sum (String -> String) ()) ->
([((Term.Term b a, Term.Term b a), [(Term.Term b a, Term.Term b a)])] ->
  Term.Term b a ->
    (a -> Term.Term b a) ->
      [(Term.Term b a, Term.Term b a)] -> Sum_Type.Sum (String -> String) ()) ->
  [((Term.Term b a, Term.Term b a), [(Term.Term b a, Term.Term b a)])] ->
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
                         (Term_Impl.fun_poss_list l_1))
                       (\ x -> Sum_Type.Inl (snd x)))
                   r)
                 (\ x -> Sum_Type.Inl (snd x)))
        r)
      (\ x -> Sum_Type.Inl (snd x));

rule2 ::
  forall a b.
    Unfeasible_proof a b ->
      ((Term.Term a b, Term.Term a b), [(Term.Term a b, Term.Term a b)]);
rule2 (UnfeasibleOverlap x1 x2 x3 x4 x5 x6 x7) = x7;

rule1 ::
  forall a b.
    Unfeasible_proof a b ->
      ((Term.Term a b, Term.Term a b), [(Term.Term a b, Term.Term a b)]);
rule1 (UnfeasibleOverlap x1 x2 x3 x4 x5 x6 x7) = x6;

check_unfeasiblea ::
  forall a.
    (Compare.Compare a, Eq a,
      Shows_Literal.Showl a) => Unfeasible_proof a [Str.Char] ->
                                  [((Term.Term a [Str.Char],
                                      Term.Term a [Str.Char]),
                                     [(Term.Term a [Str.Char],
Term.Term a [Str.Char])])] ->
                                    Term.Term a [Str.Char] ->
                                      ([Str.Char] -> Term.Term a [Str.Char]) ->
[(Term.Term a [Str.Char], Term.Term a [Str.Char])] ->
  Sum_Type.Sum (String -> String) ();
check_unfeasiblea (UnfeasibleOverlap t u v ps qs rho_1 rho_2) r l mu cs =
  Error_Monad.catch_error
    (let {
       c = skol_rules cs;
       va = Trs.vars_trs (List.set cs);
       ta = AL94.skol va t;
       ua = AL94.skol va u;
       vb = AL94.skol va v;
       psa = map (skol_cstep_proof (List.set r) va) ps;
       qsa = map (skol_cstep_proof (List.set r) va) qs;
       ra = map_funs_crules Sum_Type.Inl r ++ rules2crules c;
     } in Error_Monad.bind
            (Check_Monad.check (Term.equal_term l (fst (fst rho_1))) id)
            (\ _ ->
              Error_Monad.bind
                (Check_Monad.check
                  (all (\ (a, b) ->
                         (case a of {
                           (la, _) -> (\ _ -> not (Term.is_Var la));
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
                              (Term.equal_term (Term.eval_term Term.Fun l mu)
                                 (Term.eval_term Term.Fun (fst (fst rho_2))
                                   mu) ||
                                Term_Impl.supt_impl
                                  (Term.eval_term Term.Fun l mu)
                                  (Term.eval_term Term.Fun (fst (fst rho_2))
                                    mu))
                              id)
                            (\ _ ->
                              Error_Monad.bind
                                (Check_Monad.check
                                  (Set.member t (Set.image fst (List.set cs)))
                                  id)
                                (\ _ ->
                                  Error_Monad.bind
                                    (Check_Monad.check
                                      (cs ==
Unification.subst_list mu (snd rho_1 ++ snd rho_2))
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
              Check_Monad.check (Option.is_none (Unification.mgu u v))
                (((Term_More.showsl_terma u .
                    Shows_Literal.showsl_lit " and ") .
                   Term_More.showsl_terma v) .
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
      Shows_Literal.Showl a) => [([Str.Char] -> Term.Term a [Str.Char],
                                   Unfeasible_proof a [Str.Char])] ->
                                  [((Term.Term a [Str.Char],
                                      Term.Term a [Str.Char]),
                                     [(Term.Term a [Str.Char],
Term.Term a [Str.Char])])] ->
                                    Term.Term a [Str.Char] ->
                                      ([Str.Char] -> Term.Term a [Str.Char]) ->
[(Term.Term a [Str.Char], Term.Term a [Str.Char])] ->
  Sum_Type.Sum (String -> String) ();
check_unfeasible css r l mu cs =
  Error_Monad.catch_error
    (Error_Monad.existsM
      (\ (mua, uo) ->
        let {
          cs_1 = snd (rule1 uo);
          cs_2 = snd (rule2 uo);
          csa = Unification.subst_list mua (cs_1 ++ cs_2);
          la = fst (fst (rule1 uo));
        } in Error_Monad.bind
               (Check_Monad.check
                 (Arith.equal_nat (List.size_list csa) (List.size_list cs))
                 (Shows_Literal.showsl_lit "lengths differ"))
               (\ _ ->
                 Error_Monad.bind
                   (Check_Monad.check
                     (not (Option.is_none
                            (Trs_Impl_More.match_rules
                              ((Term.eval_term Term.Fun l mu,
                                 Term.eval_term Term.Fun l mu) :
                                cs)
                              ((Term.eval_term Term.Fun la mua,
                                 Term.eval_term Term.Fun la mua) :
                                csa))) &&
                       not (Option.is_none
                             (Trs_Impl_More.match_rules
                               ((Term.eval_term Term.Fun la mua,
                                  Term.eval_term Term.Fun la mua) :
                                 csa)
                               ((Term.eval_term Term.Fun l mu,
                                  Term.eval_term Term.Fun l mu) :
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
 (Labelings.Lab c [Arith.Nat]) [Str.Char] () ->
 Dependency_Pair_Problem_Spec.Dpp_ops_ext d (Labelings.Lab c [Arith.Nat])
   [Str.Char] () ->
   [([(Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char],
        Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char])],
      Check_Infeasibility.Infeasibility_proof c [Str.Char] e [Arith.Nat])] ->
     [((Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char],
         Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char]),
        [(Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char],
           Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char])])] ->
       [(Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char],
          Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char])] ->
         Sum_Type.Sum (String -> String) ();
check_infeasible a ia i j css r cs =
  Error_Monad.catch_error
    (Error_Monad.existsM
      (\ (csa, p) ->
        Error_Monad.bind
          (Check_Monad.check
            (Arith.equal_nat (List.size_list csa) (List.size_list cs))
            (Shows_Literal.showsl_lit "lengths differ"))
          (\ _ ->
            Error_Monad.bind
              (Check_Monad.check
                (not (Option.is_none (Trs_Impl_More.match_rules cs csa)) &&
                  not (Option.is_none (Trs_Impl_More.match_rules csa cs)))
                id)
              (\ _ -> Check_Infeasibility.check_infeasible a ia i j r csa p)))
      css)
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_sep id (Shows_Literal.showsl_literal "\n") x));

check_adtrs ::
  forall a.
    (Eq a,
      Shows_Literal.Showl a) => [((Term.Term a [Str.Char],
                                    Term.Term a [Str.Char]),
                                   [(Term.Term a [Str.Char],
                                      Term.Term a [Str.Char])])] ->
                                  Sum_Type.Sum (String -> String) ();
check_adtrs r =
  Error_Monad.catch_error
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ cr ->
          Error_Monad.catch_error
            (Error_Monad.forallM (\ i -> let {
   a = snd (List.nth (snd cr) i);
 } in check_airr r a)
              (List.upt Arith.zero_nat (List.size_list (snd cr))))
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
 (Labelings.Lab c [Arith.Nat]) [Str.Char] () ->
 Dependency_Pair_Problem_Spec.Dpp_ops_ext d (Labelings.Lab c [Arith.Nat])
   [Str.Char] () ->
   [(Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char],
      (Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char],
        ([(Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char],
            Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char])],
          Context_joinable_proof (Labelings.Lab c [Arith.Nat]) [Str.Char])))] ->
     [([(Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char],
          Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char])],
        Check_Infeasibility.Infeasibility_proof c [Str.Char] e [Arith.Nat])] ->
       [([Str.Char] -> Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char],
          Unfeasible_proof (Labelings.Lab c [Arith.Nat]) [Str.Char])] ->
         [((Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char],
             Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char]),
            [(Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char],
               Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char])])] ->
           Sum_Type.Sum (String -> String) ();
check_al94 a ia i j cj css uo r =
  Error_Monad.catch_error
    (Error_Monad.bind (Conditional_Rewriting_Impl.check_wf_ctrs r)
      (\ _ ->
        Error_Monad.bind (check_adtrs r)
          (\ _ ->
            check_CCPs (\ aa -> Str.char_0x78 : aa) (\ aa -> Str.char_0x79 : aa)
              (check_context_joinable cj) (check_infeasible a ia i j css)
              (check_unfeasible uo) r)))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "Avenhaus & Loria-Saenz 1994 does not apply\n" .
          x));

orig_crule ::
  forall a b.
    (a -> Maybe b) ->
      ((Term.Term a b, Term.Term a b), [(Term.Term a b, Term.Term a b)]) ->
        ((Term.Term a b, Term.Term a b), [(Term.Term a b, Term.Term a b)]);
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
