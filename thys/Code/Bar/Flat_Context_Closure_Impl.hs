{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Flat_Context_Closure_Impl(fcc_tt, fcc_proc, fcc_split_proc) where {

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
import qualified Flat_Context_Closure;
import qualified Map_Choice;
import qualified Compare;
import qualified Compare_Order_Instances;
import qualified QDP_Framework_Impl;
import qualified Missing_List;
import qualified Dependency_Pair_Problem_Spec;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified HOL;
import qualified Termination_Problem_Spec;
import qualified Sum_Type;
import qualified Term_Rewriting;
import qualified Mapping;
import qualified Arith;
import qualified Shows_Literal;

check_flat_ctxt_complete ::
  forall a b.
    (Eq a, Shows_Literal.Showl a,
      Shows_Literal.Showl b) => [Term_Rewriting.Actxt a
                                   (Term_Rewriting.Term a b)] ->
                                  (a, Arith.Nat) ->
                                    Sum_Type.Sum (String -> String) ();
check_flat_ctxt_complete fcs fa =
  Check_Monad.check
    (all (\ i -> any (Flat_Context_Closure.hole_at (snd fa) i (fst fa)) fcs)
      (Arith.upt Arith.zero_nat (snd fa)))
    (Shows_Literal.showsl_lit "the list of flat contexts is incomplete\n");

check_rule_preserving ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => [Term_Rewriting.Actxt a
                                   (Term_Rewriting.Term a b)] ->
                                  [(Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b)] ->
                                    (Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b) ->
                                      Sum_Type.Sum (String -> String) ();
check_rule_preserving fcs rs rule =
  Check_Monad.check
    (any (Term_Rewriting.instance_rule rule) rs ||
      all (\ c ->
            any (Term_Rewriting.instance_rule
                  (Term_Rewriting.intp_actxt Term_Rewriting.Fun c (fst rule),
                    Term_Rewriting.intp_actxt Term_Rewriting.Fun c (snd rule)))
              rs)
        fcs)
    ((Shows_Literal.showsl_lit "the rule " . Term_Rewriting.showsl_rule rule) .
      Shows_Literal.showsl_lit
        " is neither contained in the resulting set of rules nor closed under all flat contexts\n");

is_flat_ctxt_list ::
  forall a b.
    (Eq a,
      Eq b) => [a] ->
                 [(b, Arith.Nat)] ->
                   Term_Rewriting.Actxt b (Term_Rewriting.Term b a) -> Bool;
is_flat_ctxt_list vs fas (Term_Rewriting.More f ss1 Term_Rewriting.Hole ss2) =
  let {
    ss = ss1 ++ ss2;
  } in Arith.membera fas (f, Arith.suc (Arith.size_list ss)) &&
         all Term_Rewriting.is_Var ss &&
           Arith.distinct ss &&
             null (Arith.inter_list_set (map Term_Rewriting.the_Var ss) vs);
is_flat_ctxt_list vs fas Term_Rewriting.Hole = False;
is_flat_ctxt_list vs fas
  (Term_Rewriting.More v va (Term_Rewriting.More vd ve vf vg) vc) = False;

check_is_flat_ctxt ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => [a] ->
                                  [(b, Arith.Nat)] ->
                                    Term_Rewriting.Actxt b
                                      (Term_Rewriting.Term b a) ->
                                      Sum_Type.Sum (String -> String) ();
check_is_flat_ctxt vs fas c =
  Check_Monad.check (is_flat_ctxt_list vs fas c)
    (Term_Rewriting.showsl_actxta c .
      Shows_Literal.showsl_lit " is not a flat context\n");

partition_rules ::
  forall a b.
    (Eq a,
      Eq b) => [Term_Rewriting.Actxt a (Term_Rewriting.Term a b)] ->
                 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                   [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                     ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
                       [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]);
partition_rules cs r =
  Arith.partition
    (\ lr ->
      any (\ (u, v) ->
            any (\ c ->
                  lr == (Term_Rewriting.intp_actxt Term_Rewriting.Fun c u,
                          Term_Rewriting.intp_actxt Term_Rewriting.Fun c v))
              (Term_Rewriting.Hole : cs))
        r);

check_flat_ctxt ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => [a] ->
                                  Term_Rewriting.Actxt b
                                    (Term_Rewriting.Term b a) ->
                                    Sum_Type.Sum (String -> String) ();
check_flat_ctxt vs c =
  (case c of {
    Term_Rewriting.Hole ->
      Sum_Type.Inl
        (Term_Rewriting.showsl_actxta c .
          Shows_Literal.showsl_lit " is not a flat context\n");
    Term_Rewriting.More _ ss1 Term_Rewriting.Hole ss2 ->
      let {
        ss = ss1 ++ ss2;
      } in Error_Monad.bind
             (Check_Monad.check (Arith.distinct ss)
               (Term_Rewriting.showsl_actxta c .
                 Shows_Literal.showsl_lit " contains duplicate variables\n"))
             (\ _ ->
               Error_Monad.bind
                 (Check_Monad.check (all Term_Rewriting.is_Var ss)
                   (Term_Rewriting.showsl_actxta c .
                     Shows_Literal.showsl_lit
                       " is not flat, i.e., has depth greater than one\n"))
                 (\ _ ->
                   Check_Monad.check
                     (all (\ t ->
                            not (Arith.membera vs (Term_Rewriting.the_Var t)))
                       (ss1 ++ ss2))
                     (Term_Rewriting.showsl_actxta c .
                       Shows_Literal.showsl_lit
                         " has to contain only fresh variables\n")));
    Term_Rewriting.More _ _ (Term_Rewriting.More _ _ _ _) _ ->
      Sum_Type.Inl
        (Term_Rewriting.showsl_actxta c .
          Shows_Literal.showsl_lit " is not a flat context\n");
  });

fcc_tt ::
  forall a b c.
    (Eq b, Shows_Literal.Showl b, Arith.Ccompare c, Eq c,
      Mapping.Mapping_impl c,
      Shows_Literal.Showl c) => Termination_Problem_Spec.Tp_ops_ext a b c () ->
                                  [Term_Rewriting.Actxt b
                                     (Term_Rewriting.Term b c)] ->
                                    [(Term_Rewriting.Term b c,
                                       Term_Rewriting.Term b c)] ->
                                      a -> Sum_Type.Sum (String -> String) a;
fcc_tt i fcs cRb tp =
  let {
    r = Termination_Problem_Spec.r i tp;
    rw = Termination_Problem_Spec.rw i tp;
    nfs = Termination_Problem_Spec.nfs i tp;
    rb = r ++ rw;
  } in (case partition_rules fcs r cRb of {
         (cR, cRw) ->
           let {
             _ = Termination_Problem_Spec.q i tp;
             vs = Term_Rewriting.vars_trs_list rb;
             fas = Term_Rewriting.funas_trs_list rb;
           } in (case Error_Monad.bind
                        (Check_Monad.check (not (null fcs))
                          (Shows_Literal.showsl_lit
                            "at least one flat context is required for flat context closure\n"))
                        (\ _ ->
                          Error_Monad.bind
                            (Error_Monad.catch_error
                              (Error_Monad.forallM (check_flat_ctxt vs) fcs)
                              (\ x -> Sum_Type.Inl (snd x)))
                            (\ _ ->
                              Error_Monad.bind
                                (Error_Monad.catch_error
                                  (Error_Monad.forallM
                                    (check_is_flat_ctxt vs fas) fcs)
                                  (\ x -> Sum_Type.Inl (snd x)))
                                (\ _ ->
                                  Error_Monad.bind
                                    (Error_Monad.catch_error
                                      (Error_Monad.forallM
(check_flat_ctxt_complete fcs) fas)
                                      (\ x -> Sum_Type.Inl (snd x)))
                                    (\ _ ->
                                      Error_Monad.bind
(Error_Monad.catch_error (Error_Monad.forallM (check_rule_preserving fcs cR) r)
  (\ x -> Sum_Type.Inl (snd x)))
(\ _ ->
  Error_Monad.catch_error
    (Error_Monad.forallM (check_rule_preserving fcs cRb) rw)
    (\ x -> Sum_Type.Inl (snd x)))))))
                  of {
                  Sum_Type.Inl a -> Sum_Type.Inl a;
                  Sum_Type.Inr _ ->
                    Sum_Type.Inr (Termination_Problem_Spec.mk i nfs [] cR cRw);
                });
       });

partition_pairs ::
  forall a b.
    (Eq a,
      Eq b) => a -> [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                        ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
                          [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]);
partition_pairs f p =
  Arith.partition
    (\ r -> Arith.membera p (Flat_Context_Closure.unblock_rule f r));

check_no_defined_root_defined ::
  forall a b.
    (Eq a, Shows_Literal.Showl a,
      Shows_Literal.Showl b) => [(a, Arith.Nat)] ->
                                  Term_Rewriting.Term a b ->
                                    Sum_Type.Sum (String -> String) ();
check_no_defined_root_defined f t =
  Check_Monad.check (not (Arith.membera f (Arith.the (Term_Rewriting.root t))))
    ((Shows_Literal.showsl_lit "the root of " . Term_Rewriting.showsl_terma t) .
      Shows_Literal.showsl_lit " is defined");

check_superset_of_blocked ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => a -> [(Term_Rewriting.Term a b,
Term_Rewriting.Term a b)] ->
                                       [(Term_Rewriting.Term a b,
  Term_Rewriting.Term a b)] ->
 Sum_Type.Sum (String -> String) ();
check_superset_of_blocked f pa p =
  Error_Monad.catch_error
    (Error_Monad.catch_error
      (Error_Monad.catch_error
        (Error_Monad.forallM
          (\ x ->
            (if Arith.membera pa (Flat_Context_Closure.block_rule f x)
              then Sum_Type.Inr () else Sum_Type.Inl x))
          p)
        (\ x -> Sum_Type.Inl (snd x)))
      (\ x ->
        Sum_Type.Inl
          ((Shows_Literal.showsl_lit "the rule " .
             Term_Rewriting.showsl_rule (Flat_Context_Closure.block_rule f x)) .
            Shows_Literal.showsl_lit " is missing\n")))
    (\ x ->
      Sum_Type.Inl
        ((((Term_Rewriting.showsl_trs p .
             Shows_Literal.showsl_lit "is not a subset of") .
            Term_Rewriting.showsl_trs pa) .
           x) .
          Shows_Literal.showsl_literal "\n"));

check_rule_reflecting ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => [Term_Rewriting.Actxt a
                                   (Term_Rewriting.Term a b)] ->
                                  [(Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b)] ->
                                    (Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b) ->
                                      Sum_Type.Sum (String -> String) ();
check_rule_reflecting fcs rs rule =
  Check_Monad.check
    (any (\ (l, r) ->
           any (\ c ->
                 Term_Rewriting.equal_term (fst rule)
                   (Term_Rewriting.intp_actxt Term_Rewriting.Fun c l) &&
                   Term_Rewriting.equal_term (snd rule)
                     (Term_Rewriting.intp_actxt Term_Rewriting.Fun c r))
             (Term_Rewriting.Hole : fcs))
      rs)
    ((Shows_Literal.showsl_lit "the rule " . Term_Rewriting.showsl_rule rule) .
      Shows_Literal.showsl_lit
        " is neither contained in the original set of rules nor obtained by applying a flat context\n");

fcc_proc_cond ::
  forall a b c.
    (Eq b, Shows_Literal.Showl b, Arith.Ccompare c, Eq c,
      Mapping.Mapping_impl c,
      Shows_Literal.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b c
                                  () ->
                                  b -> [Term_Rewriting.Actxt b
  (Term_Rewriting.Term b c)] ->
 [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
   [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
     [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
       [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
         a -> Sum_Type.Sum (String -> String) a;
fcc_proc_cond i f fcs p pw r rw dpp =
  let {
    pa = Dependency_Pair_Problem_Spec.p i dpp;
    pwa = Dependency_Pair_Problem_Spec.pw i dpp;
    ra = Dependency_Pair_Problem_Spec.r i dpp;
    rwa = Dependency_Pair_Problem_Spec.rw i dpp;
    nfs = Dependency_Pair_Problem_Spec.nfs i dpp;
    m = Dependency_Pair_Problem_Spec.minimal i dpp;
    new_dpp = Dependency_Pair_Problem_Spec.mk i nfs m p pw [] r rw;
  } in (case Error_Monad.catch_error
               (let {
                  pb = Missing_List.list_union pa pwa;
                  rb = Missing_List.list_union ra rwa;
                  rba = Missing_List.list_union r rw;
                  fa = (f, Arith.one_nat);
                  cf = Term_Rewriting.More f [] Term_Rewriting.Hole [];
                  fcsa = cf : fcs;
                  vs = Term_Rewriting.vars_trs_list rb;
                  fs = Missing_List.list_union
                         (Term_Rewriting.funas_trs_list rb)
                         (Term_Rewriting.funas_args_trs_list pb);
                  fas = fa : fs;
                  ds = Term_Rewriting.defined_list rb;
                } in Error_Monad.bind
                       (Check_Monad.check (not (Arith.membera ds fa))
                         (Shows_Literal.showsl f .
                           Shows_Literal.showsl_lit "is not fresh\n"))
                       (\ _ ->
                         Error_Monad.bind (Term_Rewriting.check_wf_trs rb)
                           (\ _ ->
                             Error_Monad.bind
                               (Error_Monad.catch_error
                                 (Error_Monad.forallM
                                   (\ rc ->
                                     Error_Monad.bind
                                       (Error_Monad.bind
 (Term_Rewriting.check_no_var (fst rc))
 (\ _ -> Term_Rewriting.check_no_var (snd rc)))
                                       (\ _ ->
 check_no_defined_root_defined ds (snd rc)))
                                   pb)
                                 (\ x -> Sum_Type.Inl (snd x)))
                               (\ _ ->
                                 Error_Monad.bind
                                   (Error_Monad.catch_error
                                     (Error_Monad.forallM (check_flat_ctxt vs)
                                       fcsa)
                                     (\ x -> Sum_Type.Inl (snd x)))
                                   (\ _ ->
                                     Error_Monad.bind
                                       (Error_Monad.catch_error
 (Error_Monad.forallM (check_is_flat_ctxt vs fas) fcsa)
 (\ x -> Sum_Type.Inl (snd x)))
                                       (\ _ ->
 Error_Monad.bind
   (Error_Monad.catch_error
     (Error_Monad.forallM (check_flat_ctxt_complete fcsa) fas)
     (\ x -> Sum_Type.Inl (snd x)))
   (\ _ ->
     Error_Monad.bind
       (Error_Monad.catch_error
         (Error_Monad.forallM (check_rule_preserving fcsa r) ra)
         (\ x -> Sum_Type.Inl (snd x)))
       (\ _ ->
         Error_Monad.bind
           (Error_Monad.catch_error
             (Error_Monad.forallM (check_rule_preserving fcsa rba) rwa)
             (\ x -> Sum_Type.Inl (snd x)))
           (\ _ ->
             Error_Monad.bind
               (Error_Monad.catch_error
                 (Error_Monad.forallM (check_rule_reflecting fcsa rb) rba)
                 (\ x -> Sum_Type.Inl (snd x)))
               (\ _ ->
                 Error_Monad.bind (check_superset_of_blocked f p pa)
                   (\ _ -> check_superset_of_blocked f pw pwa)))))))))))
               (\ x ->
                 Sum_Type.Inl
                   (((((Shows_Literal.showsl_lit
                          "problem when checking flat context closure conditions to switch from\n" .
                         QDP_Framework_Impl.showsl_dpp i dpp) .
                        Shows_Literal.showsl_lit "\nto the DP problem\n") .
                       QDP_Framework_Impl.showsl_dpp i new_dpp) .
                      Shows_Literal.showsl_literal "\n") .
                     x))
         of {
         Sum_Type.Inl a -> Sum_Type.Inl a;
         Sum_Type.Inr _ -> Sum_Type.Inr new_dpp;
       });

fcc_proc ::
  forall a b c.
    (Eq b, Shows_Literal.Showl b, Arith.Ceq c, Arith.Ccompare c, Eq c,
      Mapping.Mapping_impl c, Arith.Set_impl c,
      Shows_Literal.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b c
                                  () ->
                                  b -> [Term_Rewriting.Actxt b
  (Term_Rewriting.Term b c)] ->
 [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
   [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
     a -> Sum_Type.Sum (String -> String) a;
fcc_proc i f fcs pb rw dpp =
  let {
    p = Dependency_Pair_Problem_Spec.p i dpp;
    q = Dependency_Pair_Problem_Spec.q i dpp;
    r = Dependency_Pair_Problem_Spec.r i dpp;
  } in (case partition_pairs f p pb of {
         (pa, pw) ->
           Error_Monad.bind
             (Check_Monad.check (null q)
               (Shows_Literal.showsl_lit "Q is not empty"))
             (\ _ ->
               Error_Monad.bind
                 (Check_Monad.check (null r)
                   (Shows_Literal.showsl_lit "strict rules not allowed"))
                 (\ _ ->
                   Error_Monad.bind
                     (Term_Rewriting.check_left_linear_trs
                       (Dependency_Pair_Problem_Spec.rw i dpp))
                     (\ _ -> fcc_proc_cond i f fcs pa pw [] rw dpp)));
       });

fcc_split_proc ::
  forall a b c.
    (Compare.Compare_order b, Eq b, Shows_Literal.Showl b, Arith.Ceq c,
      Arith.Ccompare c, Compare.Compare_order c, Eq c, Mapping.Mapping_impl c,
      Arith.Set_impl c,
      Shows_Literal.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b c
                                  () ->
                                  b -> [Term_Rewriting.Actxt b
  (Term_Rewriting.Term b c)] ->
 [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
   [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
     [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
       [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
         a -> Sum_Type.Sum (String -> String) (a, a);
fcc_split_proc i f fcs pb rb ps rs dpp =
  let {
    p = Dependency_Pair_Problem_Spec.p i dpp;
    pw = Dependency_Pair_Problem_Spec.pw i dpp;
    r = Dependency_Pair_Problem_Spec.r i dpp;
    rw = Dependency_Pair_Problem_Spec.rw i dpp;
    q = Dependency_Pair_Problem_Spec.q i dpp;
    nfs = Dependency_Pair_Problem_Spec.nfs i dpp;
    m = Dependency_Pair_Problem_Spec.minimal i dpp;
    pba = Missing_List.list_union p pw;
    rba = rw;
    pns = Map_Choice.ceta_list_diff pba ps;
    rns = Map_Choice.ceta_list_diff rba rs;
  } in (case partition_pairs f ps pb of {
         (pa, pwa) ->
           (case partition_rules
                   (Term_Rewriting.More f [] Term_Rewriting.Hole [] : fcs) rs rb
             of {
             (ra, rwa) ->
               let {
                 two = Dependency_Pair_Problem_Spec.mk i nfs m
                         (Map_Choice.ceta_list_diff p ps)
                         (Map_Choice.ceta_list_diff pw ps) [] [] rns;
                 dpp_mid =
                   Dependency_Pair_Problem_Spec.mk i nfs m ps pns [] rs rns;
               } in Error_Monad.bind
                      (Error_Monad.bind
                        (Error_Monad.catch_error
                          (Check_Monad.check_subseteq ps pba)
                          (\ x ->
                            Sum_Type.Inl
                              ((Shows_Literal.showsl_lit "pair " .
                                 Term_Rewriting.showsl_rule x) .
                                Shows_Literal.showsl_lit
                                  " should be deleted but is not present")))
                        (\ _ ->
                          Error_Monad.bind
                            (Error_Monad.catch_error
                              (Check_Monad.check_subseteq rs rba)
                              (\ x ->
                                Sum_Type.Inl
                                  ((Shows_Literal.showsl_lit "rule " .
                                     Term_Rewriting.showsl_rule x) .
                                    Shows_Literal.showsl_lit
                                      " should be deleted but is not present")))
                            (\ _ ->
                              Error_Monad.bind
                                (Check_Monad.check (null q)
                                  (Shows_Literal.showsl_lit "Q is not empty\n"))
                                (\ _ ->
                                  Error_Monad.bind
                                    (Check_Monad.check (null r)
                                      (Shows_Literal.showsl_lit
"strict rules not allowed\n"))
                                    (\ _ ->
                                      Error_Monad.bind
(Term_Rewriting.check_left_linear_trs rw)
(\ _ -> fcc_proc_cond i f fcs pa pwa ra rwa dpp_mid))))))
                      (\ one -> Sum_Type.Inr (one, two));
           });
       });

}
