{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Innermost_Loops_Impl(w_impl, subst_incr, ident_decision, gmatch_decision,
                        match_decision, check_NF_iteration, check_qsteps_subst,
                        check_qrsteps_subst)
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
import qualified Q_Restricted_Rewriting_Impl;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Mapping;
import qualified Shows_Literal;
import qualified Sum_Type;
import qualified Option_Monad;
import qualified Compare;
import qualified Inductive_Set_Impl;
import qualified Innermost_Loops;
import qualified Transitive_Closure_List_Impl;
import qualified Arith;
import qualified HOL;
import qualified Term_Rewriting;

w_impl ::
  forall a b.
    (Eq a) => [(a, Term_Rewriting.Term b a)] -> Term_Rewriting.Term b a -> [a];
w_impl d =
  let {
    filt = filter (\ (x, y) -> not (x == y));
    xvs = concatMap
            (\ (x, t) -> map (\ a -> (x, a)) (Term_Rewriting.vars_term_list t))
            d;
    rel = filt xvs;
    rtran = Transitive_Closure_List_Impl.rtrancl_list_impl rel;
  } in (\ t -> rtran (Term_Rewriting.vars_term_list t));

v_incr_impl ::
  forall a b. (Eq a, Eq b) => [(a, Term_Rewriting.Term b a)] -> [a];
v_incr_impl mu =
  Inductive_Set_Impl.inductive_set_impl (map fst mu) (\ a b -> a == b)
    (\ x ->
      concatMap
        (\ (y, t) ->
          (if Term_Rewriting.equal_term t (Term_Rewriting.Var x) then [y]
            else []))
        mu)
    (concatMap (\ (y, t) -> (if not (Term_Rewriting.is_Var t) then [y] else []))
      mu);

subst_incr ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Eq a, Arith.Set_impl a,
      Eq b) => [(a, Term_Rewriting.Term b a)] -> Innermost_Loops.Subst_incr b a;
subst_incr xa =
  Innermost_Loops.Abs_subst_incr
    (let {
       dom = Term_Rewriting.mk_subst_domain xa;
     } in (Term_Rewriting.mk_subst Term_Rewriting.Var xa,
            (Arith.set (v_incr_impl dom), w_impl dom)));

ident_decision ::
  forall a b.
    (Compare.Compare a, Eq a, Compare.Compare b,
      Eq b) => Innermost_Loops.Subst_incr a b ->
                 (Term_Rewriting.Term a b, Term_Rewriting.Term a b) -> Bool;
ident_decision sigma ip =
  not (Arith.is_none (Innermost_Loops.ident_solve sigma ip));

gmatch_decision ::
  forall a b.
    (Compare.Compare a, Eq a, Arith.Ceq b, Arith.Ccompare b, Compare.Compare b,
      Eq b) => Innermost_Loops.Subst_incr a b ->
                 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] -> Bool;
gmatch_decision sigma mp =
  not (Arith.is_none
        (Arith.bind (Innermost_Loops.simplify_mp sigma mp [])
          (\ (smp, _) ->
            Option_Monad.guard
              (all (ident_decision sigma)
                (Innermost_Loops.ident_prob_of_smp smp)))));

match_decision ::
  forall a b.
    (Compare.Compare a, Eq a, Arith.Ceq b, Arith.Ccompare b, Compare.Compare b,
      Eq b) => Innermost_Loops.Subst_incr a b ->
                 (Term_Rewriting.Term a b, Term_Rewriting.Term a b) -> Bool;
match_decision mu mp = gmatch_decision mu [mp];

match_prob_of_rp_impl ::
  forall a b.
    (Eq a,
      Eq b) => Innermost_Loops.Subst_incr a b ->
                 (Term_Rewriting.Term a b, Term_Rewriting.Term a b) ->
                   [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
match_prob_of_rp_impl mu (t, Term_Rewriting.Var x) =
  [(t, Term_Rewriting.Var x)];
match_prob_of_rp_impl mu (t, Term_Rewriting.Fun v va) =
  let {
    sterms =
      Arith.remdups
        (t : map (Innermost_Loops.si_subst mu) (Innermost_Loops.si_W mu t));
    uterms =
      concatMap
        (filter (\ ta -> not (Term_Rewriting.is_Var ta)) .
          Term_Rewriting.supteq_list)
        sterms;
  } in map (\ u -> (u, Term_Rewriting.Fun v va)) (Arith.remdups uterms);

redex_decision ::
  forall a b.
    (Compare.Compare a, Eq a, Arith.Ceq b, Arith.Ccompare b, Compare.Compare b,
      Eq b) => Innermost_Loops.Subst_incr a b ->
                 (Term_Rewriting.Term a b, Term_Rewriting.Term a b) -> Bool;
redex_decision mu rp = any (match_decision mu) (match_prob_of_rp_impl mu rp);

redex_rps_decision ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Compare.Compare a, Eq a, Arith.Set_impl a,
      Compare.Compare b,
      Eq b) => [(a, Term_Rewriting.Term b a)] ->
                 [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
                   Sum_Type.Sum
                     (Term_Rewriting.Term b a, Term_Rewriting.Term b a) ();
redex_rps_decision mu =
  let {
    mua = subst_incr mu;
    main = redex_decision mua;
  } in (\ xs ->
         Error_Monad.catch_error
           (Error_Monad.forallM (\ tl -> Check_Monad.check (not (main tl)) tl)
             xs)
           (\ x -> Sum_Type.Inl (snd x)));

check_NF_iteration ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Compare.Compare a, Eq a, Arith.Set_impl a,
      Compare.Compare b,
      Eq b) => [(a, Term_Rewriting.Term b a)] ->
                 [Term_Rewriting.Term b a] ->
                   Term_Rewriting.Term b a ->
                     Sum_Type.Sum
                       (Term_Rewriting.Term b a, Term_Rewriting.Term b a) ();
check_NF_iteration mu = let {
                          dec = redex_rps_decision mu;
                        } in (\ q t -> dec (map (\ a -> (t, a)) q));

check_qrstep_subst ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => (Term_Rewriting.Term a b ->
                                  Sum_Type.Sum
                                    (Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)
                                    ()) ->
                                  Bool ->
                                    [(Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b)] ->
                                      [Arith.Nat] ->
(Term_Rewriting.Term a b, Term_Rewriting.Term a b) ->
  Term_Rewriting.Term a b ->
    Term_Rewriting.Term a b -> Sum_Type.Sum (String -> String) ();
check_qrstep_subst cni nfs =
  let {
    main =
      Q_Restricted_Rewriting_Impl.check_prop_rstep nfs
        (\ t ->
          Error_Monad.catch_error (cni t)
            (\ _ ->
              Sum_Type.Inl
                (Term_Rewriting.showsl_terma t .
                  Shows_Literal.showsl_lit
                    " mu ^^ i is not in Q-normal form for all i")));
  } in (\ r p ra s t ->
         Error_Monad.bind
           (Check_Monad.check (not (Term_Rewriting.is_Var (fst ra)))
             (Shows_Literal.showsl_lit
               "loop check requires lhss to be non-variable"))
           (\ _ -> main r p ra s t));

check_rqrstep_subst ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => (Term_Rewriting.Term a b ->
                                  Sum_Type.Sum
                                    (Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)
                                    ()) ->
                                  Bool ->
                                    [(Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b)] ->
                                      (Term_Rewriting.Term a b,
Term_Rewriting.Term a b) ->
Term_Rewriting.Term a b ->
  Term_Rewriting.Term a b -> Sum_Type.Sum (String -> String) ();
check_rqrstep_subst cni nfs = (\ r -> check_qrstep_subst cni nfs r []);

check_qsteps_subst ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => (Term_Rewriting.Term a b ->
                                  Sum_Type.Sum
                                    (Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)
                                    ()) ->
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
check_qsteps_subst cni nfs p r [] s u =
  Check_Monad.check (Term_Rewriting.equal_term s u)
    ((((Shows_Literal.showsl_lit "the last term of the rewrite sequence\n" .
         Term_Rewriting.showsl_terma s) .
        Shows_Literal.showsl_lit "\ndoes not correspond to the goal term\n") .
       Term_Rewriting.showsl_terma u) .
      Shows_Literal.showsl_literal "\n");
check_qsteps_subst cni nfs p ra ((uu, (r, (True, t))) : prts) s u =
  Error_Monad.bind (check_rqrstep_subst cni nfs p r s t)
    (\ _ -> check_qsteps_subst cni nfs p ra prts t u);
check_qsteps_subst cni nfs pa ra ((p, (r, (False, t))) : prts) s u =
  Error_Monad.bind (check_qrstep_subst cni nfs ra p r s t)
    (\ _ -> check_qsteps_subst cni nfs pa ra prts t u);

check_qrsteps_subst ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => (Term_Rewriting.Term a b ->
                                  Sum_Type.Sum
                                    (Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)
                                    ()) ->
                                  Bool ->
                                    [(Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b)] ->
                                      [([Arith.Nat],
 ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
   Term_Rewriting.Term a b))] ->
Term_Rewriting.Term a b ->
  Term_Rewriting.Term a b -> Sum_Type.Sum (String -> String) ();
check_qrsteps_subst cni nfs r prts s u =
  check_qsteps_subst cni nfs [] r
    (map (\ (p, (ra, t)) -> (p, (ra, (False, t)))) prts) s u;

}
