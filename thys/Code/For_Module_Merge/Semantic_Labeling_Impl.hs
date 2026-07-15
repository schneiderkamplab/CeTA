{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Semantic_Labeling_Impl(Sl_ops_ext(..), Slm_ops_ext(..), sl_C, sl_I, sl_c,
                          model_splitter, quasi_splitter, sem_lab_fin_tt,
                          sem_lab_fin_proc, slm_gen_to_sl_gen,
                          sem_lab_fin_root_proc, sem_lab_fin_quasi_root_proc)
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
import qualified Missing_List;
import qualified Termination_Problem_Spec;
import qualified Trs;
import qualified Trs_Impl;
import qualified Product_Type;
import qualified List;
import qualified Dependency_Pair_Problem_Spec;
import qualified Set;
import qualified Compare;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Container_Setup;
import qualified Term_Impl;
import qualified Semantic_Labeling;
import qualified Util;
import qualified Q_Restricted_Rewriting_Impl;
import qualified Term_More;
import qualified Error_Monad;
import qualified Check_Monad;
import qualified Matching;
import qualified HOL;
import qualified Mapping_Impl;
import qualified Collection_Order;
import qualified Shows_Literal;
import qualified Sum_Type;
import qualified Term;
import qualified Arith;

data Sl_ops_ext a b c d e =
  Sl_ops_ext (a -> [b] -> c) (a -> Arith.Nat -> c -> Bool) (a -> [b] -> b) [b] b
    ([(Term.Term a d, Term.Term a d)] -> Sum_Type.Sum (String -> String) ())
    (a -> [b] -> c) (a -> Arith.Nat -> c -> Bool) (c -> [c])
    (a -> Arith.Nat -> [c]) e;

data Slm_ops_ext a b c d =
  Slm_ops_ext (a -> [b] -> c) (a -> [b] -> b) [b] b (a -> [b] -> c) d;

slm_La :: forall a b c d. Slm_ops_ext a b c d -> a -> [b] -> c;
slm_La (Slm_ops_ext slm_La slm_I slm_C slm_c slm_L more) = slm_L;

slm_c :: forall a b c d. Slm_ops_ext a b c d -> b;
slm_c (Slm_ops_ext slm_La slm_I slm_C slm_c slm_L more) = slm_c;

slm_L :: forall a b c d. Slm_ops_ext a b c d -> a -> [b] -> c;
slm_L (Slm_ops_ext slm_La slm_I slm_C slm_c slm_L more) = slm_La;

slm_I :: forall a b c d. Slm_ops_ext a b c d -> a -> [b] -> b;
slm_I (Slm_ops_ext slm_La slm_I slm_C slm_c slm_L more) = slm_I;

slm_C :: forall a b c d. Slm_ops_ext a b c d -> [b];
slm_C (Slm_ops_ext slm_La slm_I slm_C slm_c slm_L more) = slm_C;

slm_to_sl :: forall a b c d. Slm_ops_ext a b c () -> Sl_ops_ext a b c d ();
slm_to_sl ops =
  Sl_ops_ext (slm_L ops) (\ _ _ _ -> True) (slm_I ops) (slm_C ops) (slm_c ops)
    (\ _ -> Sum_Type.Inr ()) (slm_La ops) (\ _ _ _ -> True) (\ l -> [l])
    (\ _ _ -> []) ();

check_sl_Q ::
  forall a b c.
    (Eq a, Shows_Literal.Showl a, Collection_Order.Ccompare c, Eq c,
      Mapping_Impl.Mapping_impl c,
      Shows_Literal.Showl c) => (a -> (a, b)) ->
                                  [Term.Term a c] ->
                                    [Term.Term a c] ->
                                      Sum_Type.Sum (String -> String) ();
check_sl_Q ld lQ q =
  let {
    u = (\ l -> fst (ld l));
  } in Error_Monad.catch_error
         (Error_Monad.forallM
           (\ lq ->
             Check_Monad.check
               (let {
                  mlq = Term.map_term u (\ x -> x) lq;
                } in any (\ qa ->
                           Matching.matches mlq qa && Matching.matches qa mlq)
                       q)
               ((Shows_Literal.showsl_lit "unlabeling " .
                  Term_More.showsl_terma lq) .
                 Shows_Literal.showsl_lit " yields a term not in Q"))
           lQ)
         (\ x -> Sum_Type.Inl (snd x));

lab_lhs_list ::
  forall a b c d e.
    (Eq e) => (a -> [b] -> b) ->
                (a -> [b] -> c) ->
                  (a -> Arith.Nat -> c -> d) ->
                    [b] -> Term.Term a e -> [Term.Term d e];
lab_lhs_list i l lc c t =
  map (\ alpha -> snd (Semantic_Labeling.eval_lab i l lc alpha t))
    (map Util.fun_of (Util.enum_vectors c (Term_Impl.insert_vars_term t [])));

lab_lhss_list ::
  forall a b c d e.
    (Eq e) => (a -> [b] -> b) ->
                (a -> [b] -> c) ->
                  (a -> Arith.Nat -> c -> d) ->
                    [b] -> [Term.Term a e] -> [Term.Term d e];
lab_lhss_list i l lc c q = concatMap (lab_lhs_list i l lc c) q;

check_sl_Qa ::
  forall a b c d.
    (Eq a, Shows_Literal.Showl a, Collection_Order.Ccompare d, Eq d,
      Mapping_Impl.Mapping_impl d,
      Shows_Literal.Showl d) => (a -> [b] -> b) ->
                                  (a -> [b] -> c) ->
                                    (a -> Arith.Nat -> c -> a) ->
                                      [b] ->
[Term.Term a d] -> [Term.Term a d] -> Sum_Type.Sum (String -> String) ();
check_sl_Qa i l lc c lQ q =
  Error_Monad.bind
    (Check_Monad.check (not (null c))
      (Shows_Literal.showsl_lit "carrier must be non-empty"))
    (\ _ ->
      Error_Monad.catch_error
        (Q_Restricted_Rewriting_Impl.check_NF_vars_subset
          (lab_lhss_list i l lc c q) lQ)
        (\ x ->
          Sum_Type.Inl
            ((Shows_Literal.showsl_lit "labeled term " .
               Term_More.showsl_terma x) .
              Shows_Literal.showsl_lit " is missing")));

sl_C :: forall a b c d e. Sl_ops_ext a b c d e -> [b];
sl_C (Sl_ops_ext sl_La sl_LSa sl_I sl_C sl_c sl_check_decr sl_L sl_LS sl_lgen
       sl_LS_gen more)
  = sl_C;

sl_I :: forall a b c d e. Sl_ops_ext a b c d e -> a -> [b] -> b;
sl_I (Sl_ops_ext sl_La sl_LSa sl_I sl_C sl_c sl_check_decr sl_L sl_LS sl_lgen
       sl_LS_gen more)
  = sl_I;

sl_L :: forall a b c d e. Sl_ops_ext a b c d e -> a -> [b] -> c;
sl_L (Sl_ops_ext sl_La sl_LSa sl_I sl_C sl_c sl_check_decr sl_L sl_LS sl_lgen
       sl_LS_gen more)
  = sl_La;

sl_c :: forall a b c d e. Sl_ops_ext a b c d e -> b;
sl_c (Sl_ops_ext sl_La sl_LSa sl_I sl_C sl_c sl_check_decr sl_L sl_LS sl_lgen
       sl_LS_gen more)
  = sl_c;

lab_rule_ass ::
  forall a b c d e.
    (a -> [b] -> b) ->
      (a -> [b] -> c) ->
        (a -> Arith.Nat -> c -> d) ->
          (e -> b) ->
            (Term.Term a e, Term.Term a e) -> (Term.Term d e, Term.Term d e);
lab_rule_ass i l lc alpha rule =
  (snd (Semantic_Labeling.eval_lab i l lc alpha (fst rule)),
    snd (Semantic_Labeling.eval_lab i l lc alpha (snd rule)));

lab_rule_list ::
  forall a b c d e.
    (Eq e) => (a -> [b] -> b) ->
                (a -> [b] -> c) ->
                  (a -> Arith.Nat -> c -> d) ->
                    [b] ->
                      (Term.Term a e, Term.Term a e) ->
                        [(Term.Term d e, Term.Term d e)];
lab_rule_list i l lc c lr =
  map (\ alpha -> lab_rule_ass i l lc alpha lr)
    (map Util.fun_of (Util.enum_vectors c (Trs_Impl.insert_vars_rule lr [])));

lab_trs_list ::
  forall a b c d e.
    (Eq e) => (a -> [b] -> b) ->
                (a -> [b] -> c) ->
                  (a -> Arith.Nat -> c -> d) ->
                    [b] ->
                      [(Term.Term a e, Term.Term a e)] ->
                        [(Term.Term d e, Term.Term d e)];
lab_trs_list i l lc c r = concatMap (lab_rule_list i l lc c) r;

model_splitter ::
  forall a b c.
    (Compare.Compare a, Eq a, Compare.Compare c,
      Eq c) => (a -> (a, b)) ->
                 [(Term.Term a c, Term.Term a c)] ->
                   Set.Set (Term.Term a c, Term.Term a c) ->
                     ([(Term.Term a c, Term.Term a c)],
                       ([(Term.Term a c, Term.Term a c)],
                         [(Term.Term a c, Term.Term a c)]));
model_splitter ld lAll uRw =
  let {
    unlab = (\ lf -> fst (ld lf));
    la = map (\ r -> (r, Trs.map_funs_rule unlab r)) lAll;
  } in (case List.partition (\ (_, ur) -> Set.member ur uRw) la of {
         (rw, r) -> (map fst r, (map fst rw, []));
       });

sem_lab_proc ::
  forall a b c d.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a,
      Collection_Order.Ccompare d, Compare.Compare d, Eq d,
      Mapping_Impl.Mapping_impl d,
      Shows_Literal.Showl d) => (a -> (a, b)) ->
                                  Dependency_Pair_Problem_Spec.Dpp_ops_ext c a d
                                    () ->
                                    Sum_Type.Sum (String -> String) () ->
                                      ([Term.Term a d] ->
[Term.Term a d] -> Sum_Type.Sum (String -> String) ()) ->
(Set.Set (Term.Term a d, Term.Term a d) ->
  [(Term.Term a d, Term.Term a d)] -> Sum_Type.Sum (String -> String) ()) ->
  ([(Term.Term a d, Term.Term a d)] ->
    [(Term.Term a d, Term.Term a d)] -> Sum_Type.Sum (String -> String) ()) ->
    (Set.Set (Term.Term a d, Term.Term a d) ->
      [(Term.Term a d, Term.Term a d)] -> Sum_Type.Sum (String -> String) ()) ->
      [(Term.Term a d, Term.Term a d)] ->
        [Term.Term a d] ->
          [(Term.Term a d, Term.Term a d)] ->
            c -> Sum_Type.Sum (String -> String) c;
sem_lab_proc ld i valid check_Q check_laba check_lab check_model_lab lPAll lQ
  lRAll dpp =
  let {
    r = Dependency_Pair_Problem_Spec.r i dpp;
    rw = Dependency_Pair_Problem_Spec.rw i dpp;
    pw = Dependency_Pair_Problem_Spec.pw i dpp;
    p = Dependency_Pair_Problem_Spec.p i dpp;
    nfs = Dependency_Pair_Problem_Spec.nfs i dpp;
    m = Dependency_Pair_Problem_Spec.minimal i dpp;
  } in (case model_splitter ld lPAll (List.set pw) of {
         (lP, (lPw, _)) ->
           (case model_splitter ld lRAll (List.set rw) of {
             (lR, (lRw, _)) ->
               (case Error_Monad.bind valid
                       (\ _ ->
                         let {
                           q = Dependency_Pair_Problem_Spec.q i dpp;
                         } in Error_Monad.catch_error
                                (Error_Monad.bind
                                  (Check_Monad.check
                                    (if nfs
                                      then (if not
         (Dependency_Pair_Problem_Spec.q_empty i dpp)
     then Dependency_Pair_Problem_Spec.wwf_rules i dpp else True)
                                      else True)
                                    (Shows_Literal.showsl_lit
                                      "well formedness required"))
                                  (\ _ ->
                                    Error_Monad.bind (check_Q lQ q)
                                      (\ _ ->
Error_Monad.bind (check_sl_Q ld lQ q)
  (\ _ ->
    Error_Monad.bind (check_laba (List.set lP) p)
      (\ _ ->
        Error_Monad.bind (check_laba (List.set lPw) pw)
          (\ _ ->
            Error_Monad.bind (check_model_lab (List.set lR) r)
              (\ _ ->
                Error_Monad.bind (check_model_lab (List.set lRw) rw)
                  (\ _ ->
                    Error_Monad.bind (check_lab lR r)
                      (\ _ -> check_lab lRw rw)))))))))
                                (\ x ->
                                  Sum_Type.Inl
                                    (Shows_Literal.showsl_lit
                                       "problem during labeling:\n" .
                                      x)))
                 of {
                 Sum_Type.Inl a -> Sum_Type.Inl a;
                 Sum_Type.Inr _ ->
                   Sum_Type.Inr
                     (Dependency_Pair_Problem_Spec.mk i nfs m lP lPw lQ lR lRw);
               });
           });
       });

sl_LS :: forall a b c d e. Sl_ops_ext a b c d e -> a -> Arith.Nat -> c -> Bool;
sl_LS (Sl_ops_ext sl_La sl_LSa sl_I sl_C sl_c sl_check_decr sl_L sl_LS sl_lgen
        sl_LS_gen more)
  = sl_LSa;

check_sl_lab ::
  forall a b c d.
    (Eq a, Shows_Literal.Showl a, Eq d,
      Shows_Literal.Showl d) => (a -> [b] -> b) ->
                                  (a -> [b] -> c) ->
                                    (a -> Arith.Nat -> c -> a) ->
                                      [b] ->
[(Term.Term a d, Term.Term a d)] ->
  [(Term.Term a d, Term.Term a d)] -> Sum_Type.Sum (String -> String) ();
check_sl_lab i l lc c lR r =
  Error_Monad.bind
    (Check_Monad.check (not (null c))
      (Shows_Literal.showsl_lit "carrier must be non-empty"))
    (\ _ ->
      Error_Monad.catch_error
        (Check_Monad.check_subseteq lR (lab_trs_list i l lc c r))
        (\ x ->
          Sum_Type.Inl
            ((Shows_Literal.showsl_lit "labeled rule " .
               Trs_Impl.showsl_rule x) .
              Shows_Literal.showsl_lit " is not allowed")));

check_sl_rule_ass ::
  forall a b c d e.
    (Shows_Literal.Showl a, Shows_Literal.Showl b, Compare.Compare d, Eq d,
      Shows_Literal.Showl d, Compare.Compare e, Eq e,
      Shows_Literal.Showl e) => Bool ->
                                  (a -> [b] -> b) ->
                                    (a -> [b] -> c) ->
                                      (a -> Arith.Nat -> c -> d) ->
(b -> b -> Bool) ->
  Set.Set (Term.Term d e, Term.Term d e) ->
    (e -> b) ->
      (Term.Term a e, Term.Term a e) -> Sum_Type.Sum (String -> String) ();
check_sl_rule_ass mc i la lc cge lR alpha (l, r) =
  let {
    cl_ll = Semantic_Labeling.eval_lab i la lc alpha l;
    cr_lr = Semantic_Labeling.eval_lab i la lc alpha r;
  } in Error_Monad.bind
         (Check_Monad.check (if mc then cge (fst cl_ll) (fst cr_lr) else True)
           (((((Shows_Literal.showsl_lit "rule " .
                 Trs_Impl.showsl_rule (l, r)) .
                Shows_Literal.showsl_lit
                  " violates the model condition, [lhs] = ") .
               Shows_Literal.showsl (fst cl_ll)) .
              Shows_Literal.showsl_lit ", [rhs] = ") .
             Shows_Literal.showsl (fst cr_lr)))
         (\ _ ->
           Check_Monad.check (Set.member (snd cl_ll, snd cr_lr) lR)
             ((Shows_Literal.showsl_lit "labeled rule " .
                Trs_Impl.showsl_rule (snd cl_ll, snd cr_lr)) .
               Shows_Literal.showsl_lit " missing"));

check_sl_rule ::
  forall a b c d e.
    (Shows_Literal.Showl a, Shows_Literal.Showl b, Compare.Compare d, Eq d,
      Shows_Literal.Showl d, Compare.Compare e, Eq e,
      Shows_Literal.Showl e) => (a -> [b] -> b) ->
                                  (a -> [b] -> c) ->
                                    (a -> Arith.Nat -> c -> d) ->
                                      [b] ->
(b -> b -> Bool) ->
  Bool ->
    Set.Set (Term.Term d e, Term.Term d e) ->
      (Term.Term a e, Term.Term a e) -> Sum_Type.Sum (String -> String) ();
check_sl_rule i l lc c cge mc lR lr =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ alpha -> check_sl_rule_ass mc i l lc cge lR alpha lr)
      (map Util.fun_of (Util.enum_vectors c (Trs_Impl.insert_vars_rule lr []))))
    (\ x -> Sum_Type.Inl (snd x));

sl_La :: forall a b c d e. Sl_ops_ext a b c d e -> a -> [b] -> c;
sl_La (Sl_ops_ext sl_La sl_LSa sl_I sl_C sl_c sl_check_decr sl_L sl_LS sl_lgen
        sl_LS_gen more)
  = sl_L;

check_sl_decr_rule ::
  forall a b c d.
    (Eq a, Eq b, Eq c,
      Eq d) => (a -> Arith.Nat -> b -> c) ->
                 (c -> (a, b)) ->
                   (a -> Arith.Nat -> b -> Bool) ->
                     (a -> Arith.Nat -> b -> b -> Bool) ->
                       (Term.Term c d, Term.Term c d) -> Bool;
check_sl_decr_rule lc ld ls lge (Term.Fun lf ts, Term.Fun lg us) =
  (case ld lf of {
    (f, l1) ->
      (case ld lg of {
        (g, l2) ->
          let {
            n = List.size_list ts;
          } in f == g &&
                 ts == us &&
                   lf == lc f n l1 &&
                     lg == lc f n l2 &&
                       ls f n l1 &&
                         ls f n l2 &&
                           Semantic_Labeling.lge_to_lgr lge ls f n l1 l2;
      });
  });
check_sl_decr_rule uu uv uw ux (Term.Var vb, va) = False;
check_sl_decr_rule uu uv uw ux (v, Term.Var vb) = False;

check_sl_decr ::
  forall a b c d.
    (Eq a, Eq b, Eq c, Shows_Literal.Showl c, Eq d,
      Shows_Literal.Showl d) => (a -> Arith.Nat -> b -> c) ->
                                  (c -> (a, b)) ->
                                    (a -> Arith.Nat -> b -> Bool) ->
                                      (a -> Arith.Nat -> b -> b -> Bool) ->
[(Term.Term c d, Term.Term c d)] -> Sum_Type.Sum (String -> String) ();
check_sl_decr lc ld ls lge d =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ lr ->
        Check_Monad.check (check_sl_decr_rule lc ld ls lge lr)
          (Trs_Impl.showsl_rule lr .
            Shows_Literal.showsl_lit " is not a decreasing rule"))
      d)
    (\ x -> Sum_Type.Inl (snd x));

quasi_splitter ::
  forall a b c.
    (Compare.Compare a, Eq a, Compare.Compare c,
      Eq c) => (a -> (a, b)) ->
                 [(Term.Term a c, Term.Term a c)] ->
                   Set.Set (Term.Term a c, Term.Term a c) ->
                     ([(Term.Term a c, Term.Term a c)],
                       ([(Term.Term a c, Term.Term a c)],
                         [(Term.Term a c, Term.Term a c)]));
quasi_splitter ld lAll uRw =
  let {
    unlab = (\ lf -> fst (ld lf));
    la = map (\ r -> (r, Trs.map_funs_rule unlab r)) lAll;
  } in (case List.partition
               (\ (r, ur) ->
                 Term.equal_term (fst ur) (snd ur) &&
                   not (Term.equal_term (fst r) (snd r)))
               la
         of {
         (d, nD) ->
           (case List.partition (\ (_, ur) -> Set.member ur uRw) nD of {
             (rw, r) -> (map fst r, (map fst rw, map fst d));
           });
       });

check_sl_model_lab_trs_set ::
  forall a b c d.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a, Shows_Literal.Showl b,
      Compare.Compare d, Eq d,
      Shows_Literal.Showl d) => (a -> [b] -> b) ->
                                  (a -> [b] -> c) ->
                                    [b] ->
                                      (b -> b -> Bool) ->
(a -> Arith.Nat -> c -> a) ->
  Set.Set (Term.Term a d, Term.Term a d) ->
    [(Term.Term a d, Term.Term a d)] -> Sum_Type.Sum (String -> String) ();
check_sl_model_lab_trs_set i l c cge labl lR r =
  Error_Monad.catch_error
    (Error_Monad.forallM (check_sl_rule i l labl c cge True lR) r)
    (\ x -> Sum_Type.Inl (snd x));

check_sl_model_lab_trs ::
  forall a b c d.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a, Shows_Literal.Showl b,
      Compare.Compare d, Eq d,
      Shows_Literal.Showl d) => (a -> [b] -> b) ->
                                  (a -> [b] -> c) ->
                                    [b] ->
                                      (b -> b -> Bool) ->
(a -> Arith.Nat -> c -> a) ->
  Set.Set (Term.Term a d, Term.Term a d) ->
    [(Term.Term a d, Term.Term a d)] -> Sum_Type.Sum (String -> String) ();
check_sl_model_lab_trs i l c cge labl lR r =
  check_sl_model_lab_trs_set i l c cge labl lR r;

sl_check_decr ::
  forall a b c d e.
    Sl_ops_ext a b c d e ->
      [(Term.Term a d, Term.Term a d)] -> Sum_Type.Sum (String -> String) ();
sl_check_decr
  (Sl_ops_ext sl_La sl_LSa sl_I sl_C sl_c sl_check_decr sl_L sl_LS sl_lgen
    sl_LS_gen more)
  = sl_check_decr;

sem_lab_rel_tt ::
  forall a b c d.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a,
      Collection_Order.Ccompare b, Compare.Compare b, Eq b,
      Mapping_Impl.Mapping_impl b,
      Shows_Literal.Showl b) => ([(Term.Term a b, Term.Term a b)] ->
                                  Set.Set (Term.Term a b, Term.Term a b) ->
                                    ([(Term.Term a b, Term.Term a b)],
                                      ([(Term.Term a b, Term.Term a b)],
[(Term.Term a b, Term.Term a b)]))) ->
                                  (a -> (a, c)) ->
                                    Termination_Problem_Spec.Tp_ops_ext d a b
                                      () ->
                                      Sum_Type.Sum (String -> String) () ->
([(Term.Term a b, Term.Term a b)] -> Sum_Type.Sum (String -> String) ()) ->
  (Set.Set (Term.Term a b, Term.Term a b) ->
    [(Term.Term a b, Term.Term a b)] -> Sum_Type.Sum (String -> String) ()) ->
    [Term.Term a b] ->
      [(Term.Term a b, Term.Term a b)] ->
        d -> Sum_Type.Sum (String -> String) d;
sem_lab_rel_tt splitter ld i valid check_decr check_model_lab lQ lAll tp =
  let {
    r = Termination_Problem_Spec.r i tp;
    rw = Termination_Problem_Spec.rw i tp;
    nfs = Termination_Problem_Spec.nfs i tp;
  } in (case splitter lAll (List.set rw) of {
         (lR, (lRw, d)) ->
           (case Error_Monad.bind valid
                   (\ _ ->
                     let {
                       q = Termination_Problem_Spec.q i tp;
                     } in Error_Monad.catch_error
                            (Error_Monad.bind
                              (if nfs &&
                                    not (Termination_Problem_Spec.q_empty i tp)
                                then Trs_Impl.check_wf_trs d
                                else Sum_Type.Inr ())
                              (\ _ ->
                                Error_Monad.bind (check_decr d)
                                  (\ _ ->
                                    Error_Monad.bind (check_sl_Q ld lQ q)
                                      (\ _ ->
Error_Monad.bind (check_model_lab (List.set lR) r)
  (\ _ -> check_model_lab (List.set lRw) rw)))))
                            (\ x ->
                              Sum_Type.Inl
                                (Shows_Literal.showsl_lit
                                   "problem with labeled TRS:\n" .
                                  x)))
             of {
             Sum_Type.Inl a -> Sum_Type.Inl a;
             Sum_Type.Inr _ ->
               Sum_Type.Inr
                 (Termination_Problem_Spec.mk i nfs lQ lR (lRw ++ d));
           });
       });

sem_lab_fin_tt ::
  forall a b c d e.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a,
      Collection_Order.Ccompare b, Compare.Compare b, Eq b,
      Mapping_Impl.Mapping_impl b, Shows_Literal.Showl b,
      Shows_Literal.Showl d) => ([(Term.Term a b, Term.Term a b)] ->
                                  Set.Set (Term.Term a b, Term.Term a b) ->
                                    ([(Term.Term a b, Term.Term a b)],
                                      ([(Term.Term a b, Term.Term a b)],
[(Term.Term a b, Term.Term a b)]))) ->
                                  (a -> Arith.Nat -> c -> a) ->
                                    (a -> (a, c)) ->
                                      (d -> d -> Bool) ->
Termination_Problem_Spec.Tp_ops_ext e a b () ->
  ([(a, Arith.Nat)] ->
    [(a, Arith.Nat)] ->
      Sum_Type.Sum (String -> String) (Sl_ops_ext a d c b ())) ->
    [Term.Term a b] ->
      [(Term.Term a b, Term.Term a b)] ->
        e -> Sum_Type.Sum (String -> String) e;
sem_lab_fin_tt splitter lc ld cge i gen lQ lAll tp =
  Error_Monad.bind
    (gen (Trs_Impl.insert_funas_trs (Termination_Problem_Spec.rules i tp) [])
      [])
    (\ ops ->
      let {
        check_ml =
          check_sl_model_lab_trs (sl_I ops) (sl_L ops) (sl_C ops) cge lc;
        check_d = sl_check_decr ops;
      } in sem_lab_rel_tt splitter ld i (Sum_Type.Inr ()) check_d check_ml lQ
             lAll tp);

sl_lgen :: forall a b c d e. Sl_ops_ext a b c d e -> c -> [c];
sl_lgen
  (Sl_ops_ext sl_La sl_LSa sl_I sl_C sl_c sl_check_decr sl_L sl_LS sl_lgen
    sl_LS_gen more)
  = sl_lgen;

check_sl_lab_trs_set ::
  forall a b c d.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a, Shows_Literal.Showl b,
      Compare.Compare d, Eq d,
      Shows_Literal.Showl d) => (a -> [b] -> b) ->
                                  (a -> [b] -> c) ->
                                    [b] ->
                                      (b -> b -> Bool) ->
(a -> Arith.Nat -> c -> a) ->
  Set.Set (Term.Term a d, Term.Term a d) ->
    [(Term.Term a d, Term.Term a d)] -> Sum_Type.Sum (String -> String) ();
check_sl_lab_trs_set i l c cge labl lP p =
  Error_Monad.catch_error
    (Error_Monad.forallM (check_sl_rule i l labl c cge False lP) p)
    (\ x -> Sum_Type.Inl (snd x));

check_sl_lab_trs ::
  forall a b c d.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a, Shows_Literal.Showl b,
      Compare.Compare d, Eq d,
      Shows_Literal.Showl d) => (a -> [b] -> b) ->
                                  (a -> [b] -> c) ->
                                    [b] ->
                                      (b -> b -> Bool) ->
(a -> Arith.Nat -> c -> a) ->
  Set.Set (Term.Term a d, Term.Term a d) ->
    [(Term.Term a d, Term.Term a d)] -> Sum_Type.Sum (String -> String) ();
check_sl_lab_trs i l c cge labl lP p = check_sl_lab_trs_set i l c cge labl lP p;

sem_lab_fin_proc ::
  forall a b c d e.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a,
      Collection_Order.Ccompare d, Compare.Compare d, Eq d,
      Mapping_Impl.Mapping_impl d, Shows_Literal.Showl d, Eq e,
      Shows_Literal.Showl e) => (a -> Arith.Nat -> b -> a) ->
                                  (a -> (a, b)) ->
                                    Dependency_Pair_Problem_Spec.Dpp_ops_ext c a
                                      d () ->
                                      ([(a, Arith.Nat)] ->
[(a, Arith.Nat)] -> Sum_Type.Sum (String -> String) (Sl_ops_ext a e b d ())) ->
[(Term.Term a d, Term.Term a d)] ->
  [Term.Term a d] ->
    [(Term.Term a d, Term.Term a d)] -> c -> Sum_Type.Sum (String -> String) c;
sem_lab_fin_proc lc ld i gen lPAll lQ lRAll dp =
  Error_Monad.bind
    (gen (Missing_List.list_union
           (Trs_Impl.insert_funas_trs (Dependency_Pair_Problem_Spec.rules i dp)
             [])
           (Trs_Impl.insert_funas_args_trs
             (Dependency_Pair_Problem_Spec.pairs i dp) []))
      [])
    (\ ops ->
      let {
        check_q = check_sl_Qa (sl_I ops) (sl_L ops) lc (sl_C ops);
        check_ml =
          check_sl_model_lab_trs (sl_I ops) (sl_L ops) (sl_C ops)
            (\ a b -> a == b) lc;
        check_l =
          check_sl_lab_trs (sl_I ops) (sl_L ops) (sl_C ops) (\ a b -> a == b)
            lc;
        check_la = check_sl_lab (sl_I ops) (sl_L ops) lc (sl_C ops);
      } in sem_lab_proc ld i (Sum_Type.Inr ()) check_q check_l check_la check_ml
             lPAll lQ lRAll dp);

sl_LS_gen :: forall a b c d e. Sl_ops_ext a b c d e -> a -> Arith.Nat -> [c];
sl_LS_gen
  (Sl_ops_ext sl_La sl_LSa sl_I sl_C sl_c sl_check_decr sl_L sl_LS sl_lgen
    sl_LS_gen more)
  = sl_LS_gen;

check_wf_sym_F_all ::
  forall a b c.
    (Eq c,
      Shows_Literal.Showl c) => (a -> Arith.Nat -> b -> c) ->
                                  (c -> (a, b)) ->
                                    (a -> Arith.Nat -> b -> Bool) ->
                                      (c, Arith.Nat) ->
Sum_Type.Sum (String -> String) ();
check_wf_sym_F_all lc ld ls =
  (\ (lf, n) ->
    (case ld lf of {
      (f, l) ->
        Check_Monad.check (ls f n l && lf == lc f n l)
          ((Shows_Literal.showsl_lit "labeled symbol " .
             Shows_Literal.showsl lf) .
            Shows_Literal.showsl_lit " not allowed");
    }));

check_wf_terms_F_all ::
  forall a b c d.
    (Eq c,
      Shows_Literal.Showl c) => (a -> Arith.Nat -> b -> c) ->
                                  (c -> (a, b)) ->
                                    (a -> Arith.Nat -> b -> Bool) ->
                                      Term.Term c d ->
Sum_Type.Sum (String -> String) ();
check_wf_terms_F_all lc ld ls lt =
  let {
    lfs = Term_Impl.insert_funas_term lt [];
  } in Error_Monad.catch_error
         (Error_Monad.forallM (check_wf_sym_F_all lc ld ls) lfs)
         (\ x -> Sum_Type.Inl (snd x));

check_Lab_all_trs ::
  forall a b c.
    (Eq a, Shows_Literal.Showl a, Eq c,
      Shows_Literal.Showl c) => (a -> Arith.Nat -> b -> a) ->
                                  (a -> (a, b)) ->
                                    (a -> Arith.Nat -> b -> Bool) ->
                                      [(Term.Term a c, Term.Term a c)] ->
[(Term.Term a c, Term.Term a c)] -> Sum_Type.Sum (String -> String) ();
check_Lab_all_trs lc ld ls lR r =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ (l, ra) ->
        Error_Monad.catch_error
          (Error_Monad.bind (check_wf_terms_F_all lc ld ls ra)
            (\ _ ->
              Check_Monad.check
                (List.member r
                  (Trs.map_funs_rule (\ lf -> fst (ld lf)) (l, ra)))
                (Shows_Literal.showsl_lit
                  "unlabeling of the rule does not yield original rule")))
          (\ x ->
            Sum_Type.Inl
              (((Shows_Literal.showsl_lit "problem with labeled rule" .
                  Trs_Impl.showsl_rule (l, ra)) .
                 Shows_Literal.showsl_literal "\n") .
                x)))
      lR)
    (\ x -> Sum_Type.Inl (snd x));

check_sl_rule_all_ass ::
  forall a b c d e.
    (Shows_Literal.Showl a, Shows_Literal.Showl b, Compare.Compare d, Eq d,
      Shows_Literal.Showl d, Compare.Compare e, Eq e,
      Shows_Literal.Showl e) => (a -> [b] -> b) ->
                                  (a -> [b] -> c) ->
                                    (a -> [b] -> c) ->
                                      (a -> Arith.Nat -> c -> d) ->
(c -> [c]) ->
  Set.Set (Term.Term d e, Term.Term d e) ->
    (e -> b) ->
      (Term.Term a e, Term.Term a e) -> Sum_Type.Sum (String -> String) ();
check_sl_rule_all_ass i lb la lc gen_smaller lR alpha (l, Term.Fun f ts) =
  let {
    ll = Semantic_Labeling.lab_root i lb la lc alpha l;
    clts = map (Semantic_Labeling.eval_lab i lb lc alpha) ts;
    lts = map snd clts;
    ld = la f (map fst clts);
    n = List.size_list ts;
    small = gen_smaller ld;
  } in Error_Monad.catch_error
         (Error_Monad.forallM
           (\ le ->
             Check_Monad.check (Set.member (ll, Term.Fun (lc f n le) lts) lR)
               ((Shows_Literal.showsl_lit "labeled rule " .
                  Trs_Impl.showsl_rule (ll, Term.Fun (lc f n le) lts)) .
                 Shows_Literal.showsl_lit " missing"))
           small)
         (\ x -> Sum_Type.Inl (snd x));
check_sl_rule_all_ass i lb la lc gen_smaller lR alpha (l, Term.Var x) =
  let {
    ll = Semantic_Labeling.lab_root i lb la lc alpha l;
    lr = Semantic_Labeling.lab_root i lb la lc alpha (Term.Var x);
  } in Check_Monad.check (Set.member (ll, lr) lR)
         ((Shows_Literal.showsl_lit "labeled rule " .
            Trs_Impl.showsl_rule (ll, lr)) .
           Shows_Literal.showsl_lit " missing");

check_sl_rule_all ::
  forall a b c d e.
    (Shows_Literal.Showl a, Shows_Literal.Showl b, Compare.Compare d, Eq d,
      Shows_Literal.Showl d, Compare.Compare e, Eq e,
      Shows_Literal.Showl e) => (a -> [b] -> b) ->
                                  (a -> [b] -> c) ->
                                    (a -> [b] -> c) ->
                                      (a -> Arith.Nat -> c -> d) ->
[b] ->
  (c -> [c]) ->
    Set.Set (Term.Term d e, Term.Term d e) ->
      (Term.Term a e, Term.Term a e) -> Sum_Type.Sum (String -> String) ();
check_sl_rule_all i la l lc c gen_smaller lR lr =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ alpha -> check_sl_rule_all_ass i la l lc gen_smaller lR alpha lr)
      (map Util.fun_of (Util.enum_vectors c (Trs_Impl.insert_vars_rule lr []))))
    (\ x -> Sum_Type.Inl (snd x));

sem_lab_root_proc ::
  forall a b c d.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a,
      Collection_Order.Ccompare d, Compare.Compare d, Eq d,
      Mapping_Impl.Mapping_impl d,
      Shows_Literal.Showl d) => (a -> (a, b)) ->
                                  Dependency_Pair_Problem_Spec.Dpp_ops_ext c a d
                                    () ->
                                    Sum_Type.Sum (String -> String) () ->
                                      ([Term.Term a d] ->
[Term.Term a d] -> Sum_Type.Sum (String -> String) ()) ->
(Set.Set (Term.Term a d, Term.Term a d) ->
  [(Term.Term a d, Term.Term a d)] -> Sum_Type.Sum (String -> String) ()) ->
  ([(Term.Term a d, Term.Term a d)] ->
    [(Term.Term a d, Term.Term a d)] -> Sum_Type.Sum (String -> String) ()) ->
    (Set.Set (Term.Term a d, Term.Term a d) ->
      [(Term.Term a d, Term.Term a d)] -> Sum_Type.Sum (String -> String) ()) ->
      [(Term.Term a d, Term.Term a d)] ->
        [Term.Term a d] ->
          [(Term.Term a d, Term.Term a d)] ->
            c -> Sum_Type.Sum (String -> String) c;
sem_lab_root_proc ld i valid check_Q check_laba check_lab check_model_lab lPAll
  lQ lRAll dpp =
  let {
    r = Dependency_Pair_Problem_Spec.r i dpp;
    rw = Dependency_Pair_Problem_Spec.rw i dpp;
    pw = Dependency_Pair_Problem_Spec.pw i dpp;
    p = Dependency_Pair_Problem_Spec.p i dpp;
    nfs = Dependency_Pair_Problem_Spec.nfs i dpp;
    m = Dependency_Pair_Problem_Spec.minimal i dpp;
  } in (case model_splitter ld lPAll (List.set pw) of {
         (lP, (lPw, _)) ->
           (case model_splitter ld lRAll (List.set rw) of {
             (lR, (lRw, _)) ->
               (case Error_Monad.bind valid
                       (\ _ ->
                         Error_Monad.bind
                           (Error_Monad.catch_error
                             (Error_Monad.forallM
                               (\ (l, ra) ->
                                 Error_Monad.bind (Term_Impl.check_no_var l)
                                   (\ _ ->
                                     Error_Monad.bind
                                       (Term_Impl.check_no_var ra)
                                       (\ _ ->
 Q_Restricted_Rewriting_Impl.check_no_defined_root
   (\ fn -> not (null (Dependency_Pair_Problem_Spec.rules_map i dpp fn))) ra)))
                               (Dependency_Pair_Problem_Spec.pairs i dpp))
                             (\ x -> Sum_Type.Inl (snd x)))
                           (\ _ ->
                             Error_Monad.bind
                               (Error_Monad.catch_error
                                 (Error_Monad.forallM
                                   (\ (l, _) -> Term_Impl.check_no_var l)
                                   (Dependency_Pair_Problem_Spec.rules i dpp))
                                 (\ x -> Sum_Type.Inl (snd x)))
                               (\ _ ->
                                 let {
                                   q = Dependency_Pair_Problem_Spec.q i dpp;
                                 } in Error_Monad.catch_error
(Error_Monad.bind
  (Check_Monad.check
    (if nfs
      then (if not (Dependency_Pair_Problem_Spec.q_empty i dpp)
             then Dependency_Pair_Problem_Spec.wwf_rules i dpp else True)
      else True)
    (Shows_Literal.showsl_lit "well formedness required"))
  (\ _ ->
    Error_Monad.bind (check_Q lQ q)
      (\ _ ->
        Error_Monad.bind (check_sl_Q ld lQ q)
          (\ _ ->
            Error_Monad.bind (check_laba (List.set lP) p)
              (\ _ ->
                Error_Monad.bind (check_laba (List.set lPw) pw)
                  (\ _ ->
                    Error_Monad.bind (check_model_lab (List.set lR) r)
                      (\ _ ->
                        Error_Monad.bind (check_model_lab (List.set lRw) rw)
                          (\ _ ->
                            Error_Monad.bind (check_lab lR r)
                              (\ _ -> check_lab lRw rw)))))))))
(\ x ->
  Sum_Type.Inl (Shows_Literal.showsl_lit "problem during labeling:\n" . x)))))
                 of {
                 Sum_Type.Inl a -> Sum_Type.Inl a;
                 Sum_Type.Inr _ ->
                   Sum_Type.Inr
                     (Dependency_Pair_Problem_Spec.mk i nfs m lP lPw lQ lR lRw);
               });
           });
       });

slm_gen_to_sl_gen ::
  forall a b c d.
    ([(a, Arith.Nat)] ->
      [(a, Arith.Nat)] ->
        Sum_Type.Sum (String -> String) (Slm_ops_ext a b c ())) ->
      [(a, Arith.Nat)] ->
        [(a, Arith.Nat)] ->
          Sum_Type.Sum (String -> String) (Sl_ops_ext a b c d ());
slm_gen_to_sl_gen gen =
  (\ f g -> Error_Monad.bind (gen f g) (\ ops -> Sum_Type.Inr (slm_to_sl ops)));

lab_lhss_more_impl ::
  forall a b c d.
    (a -> Arith.Nat -> b -> c) ->
      (a -> Arith.Nat -> [b]) -> [Term.Term a d] -> [Term.Term c d];
lab_lhss_more_impl lc lS_gen q =
  let {
    f_all = (\ (f, n) -> map (lc f n) (lS_gen f n));
  } in concatMap
         (\ qa ->
           Term_Impl.flatten_term_enum (Term_More.map_funs_term_wa f_all qa))
         q;

check_sl_rule_root ::
  forall a b c d e.
    (Shows_Literal.Showl a, Shows_Literal.Showl b, Compare.Compare d, Eq d,
      Shows_Literal.Showl d, Compare.Compare e, Eq e,
      Shows_Literal.Showl e) => (a -> [b] -> b) ->
                                  (a -> [b] -> c) ->
                                    (a -> [b] -> c) ->
                                      (a -> Arith.Nat -> c -> d) ->
[b] ->
  Set.Set (Term.Term d e, Term.Term d e) ->
    (Term.Term a e, Term.Term a e) -> Sum_Type.Sum (String -> String) ();
check_sl_rule_root i la l lc c lR lr =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ alpha ->
        let {
          laa = Semantic_Labeling.lab_root i la l lc alpha;
          lb = laa (fst lr);
          r = laa (snd lr);
        } in Check_Monad.check (Set.member (lb, r) lR)
               ((Shows_Literal.showsl_lit "labeled rule " .
                  Trs_Impl.showsl_rule (lb, r)) .
                 Shows_Literal.showsl_lit " is missing"))
      (map Util.fun_of (Util.enum_vectors c (Trs_Impl.insert_vars_rule lr []))))
    (\ x -> Sum_Type.Inl (snd x));

check_sl_lab_all_trs ::
  forall a b c d e.
    (Shows_Literal.Showl a, Shows_Literal.Showl b, Compare.Compare d, Eq d,
      Shows_Literal.Showl d, Compare.Compare e, Eq e,
      Shows_Literal.Showl e) => (a -> [b] -> b) ->
                                  (a -> [b] -> c) ->
                                    (a -> [b] -> c) ->
                                      [b] ->
(c -> [c]) ->
  (a -> Arith.Nat -> c -> d) ->
    Set.Set (Term.Term d e, Term.Term d e) ->
      [(Term.Term a e, Term.Term a e)] -> Sum_Type.Sum (String -> String) ();
check_sl_lab_all_trs i la l c gen labl lP p =
  Error_Monad.catch_error
    (Error_Monad.forallM (check_sl_rule_all i la l labl c gen lP) p)
    (\ x -> Sum_Type.Inl (snd x));

check_sl_lab_root_trs ::
  forall a b c d e.
    (Shows_Literal.Showl a, Shows_Literal.Showl b, Compare.Compare d, Eq d,
      Shows_Literal.Showl d, Compare.Compare e, Eq e,
      Shows_Literal.Showl e) => (a -> [b] -> b) ->
                                  (a -> [b] -> c) ->
                                    (a -> [b] -> c) ->
                                      [b] ->
(a -> Arith.Nat -> c -> d) ->
  Set.Set (Term.Term d e, Term.Term d e) ->
    [(Term.Term a e, Term.Term a e)] -> Sum_Type.Sum (String -> String) ();
check_sl_lab_root_trs i la l c labl lP p =
  Error_Monad.catch_error
    (Error_Monad.forallM (check_sl_rule_root i la l labl c lP) p)
    (\ x -> Sum_Type.Inl (snd x));

sem_lab_fin_root_proc ::
  forall a b c d e.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a,
      Collection_Order.Ccompare d, Compare.Compare d, Eq d,
      Mapping_Impl.Mapping_impl d, Shows_Literal.Showl d, Eq e,
      Shows_Literal.Showl e) => (a -> Arith.Nat -> b -> a) ->
                                  (a -> (a, b)) ->
                                    Dependency_Pair_Problem_Spec.Dpp_ops_ext c a
                                      d () ->
                                      ([(a, Arith.Nat)] ->
[(a, Arith.Nat)] -> Sum_Type.Sum (String -> String) (Sl_ops_ext a e b d ())) ->
[(Term.Term a d, Term.Term a d)] ->
  [Term.Term a d] ->
    [(Term.Term a d, Term.Term a d)] -> c -> Sum_Type.Sum (String -> String) c;
sem_lab_fin_root_proc lc ld i gen lPAll lQ lRAll dp =
  let {
    pairs = Dependency_Pair_Problem_Spec.pairs i dp;
  } in Error_Monad.bind
         (gen (Missing_List.list_union
                (Trs_Impl.insert_funas_trs
                  (Dependency_Pair_Problem_Spec.rules i dp) [])
                (Trs_Impl.insert_funas_args_trs pairs []))
           (Trs_Impl.insert_roots_trs pairs []))
         (\ ops ->
           let {
             check_q = check_sl_Qa (sl_I ops) (sl_L ops) lc (sl_C ops);
             check_ml =
               check_sl_model_lab_trs (sl_I ops) (sl_L ops) (sl_C ops)
                 (\ a b -> a == b) lc;
             check_l =
               check_sl_lab_root_trs (sl_I ops) (sl_L ops) (sl_La ops)
                 (sl_C ops) lc;
             check_la = check_sl_lab (sl_I ops) (sl_L ops) lc (sl_C ops);
           } in sem_lab_root_proc ld i (Sum_Type.Inr ()) check_q check_l
                  check_la check_ml lPAll lQ lRAll dp);

check_sl_lab_lhss_more ::
  forall a b c.
    (Eq a, Shows_Literal.Showl a, Collection_Order.Ccompare c, Eq c,
      Mapping_Impl.Mapping_impl c,
      Shows_Literal.Showl c) => (a -> Arith.Nat -> b -> a) ->
                                  (a -> Arith.Nat -> [b]) ->
                                    [Term.Term a c] ->
                                      [Term.Term a c] ->
Sum_Type.Sum (String -> String) ();
check_sl_lab_lhss_more lc lS_gen lQ q =
  Error_Monad.catch_error
    (Q_Restricted_Rewriting_Impl.check_NF_vars_subset
      (lab_lhss_more_impl lc lS_gen q) lQ)
    (\ x ->
      Sum_Type.Inl
        (Term_More.showsl_terma x .
          Shows_Literal.showsl_lit " is missing in labeled Q"));

sem_lab_quasi_root_proc ::
  forall a b c d.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a, Collection_Eq.Ceq d,
      Collection_Order.Ccompare d, Compare.Compare d, Eq d,
      Mapping_Impl.Mapping_impl d, Set_Impl.Set_impl d,
      Shows_Literal.Showl d) => (a -> (a, b)) ->
                                  Dependency_Pair_Problem_Spec.Dpp_ops_ext c a d
                                    () ->
                                    Sum_Type.Sum (String -> String) () ->
                                      ([(Term.Term a d, Term.Term a d)] ->
Sum_Type.Sum (String -> String) ()) ->
([(Term.Term a d, Term.Term a d)] -> Sum_Type.Sum (String -> String) ()) ->
  ([Term.Term a d] -> [Term.Term a d] -> Sum_Type.Sum (String -> String) ()) ->
    (Set.Set (Term.Term a d, Term.Term a d) ->
      [(Term.Term a d, Term.Term a d)] -> Sum_Type.Sum (String -> String) ()) ->
      ([(Term.Term a d, Term.Term a d)] ->
        [(Term.Term a d, Term.Term a d)] ->
          Sum_Type.Sum (String -> String) ()) ->
        (Set.Set (Term.Term a d, Term.Term a d) ->
          [(Term.Term a d, Term.Term a d)] ->
            Sum_Type.Sum (String -> String) ()) ->
          [(Term.Term a d, Term.Term a d)] ->
            [Term.Term a d] ->
              [(Term.Term a d, Term.Term a d)] ->
                c -> Sum_Type.Sum (String -> String) c;
sem_lab_quasi_root_proc ld i valid check_decra check_decr check_lhss_more
  check_lab_all check_lab_all_trs check_model_lab lPAll lQ lRAll dpp =
  let {
    r = Dependency_Pair_Problem_Spec.r i dpp;
    rw = Dependency_Pair_Problem_Spec.rw i dpp;
    pw = Dependency_Pair_Problem_Spec.pw i dpp;
    p = Dependency_Pair_Problem_Spec.p i dpp;
    nfs = Dependency_Pair_Problem_Spec.nfs i dpp;
    m = Dependency_Pair_Problem_Spec.minimal i dpp;
  } in (case model_splitter ld lPAll (List.set pw) of {
         (lP, (lPw, _)) ->
           (case quasi_splitter ld lRAll (List.set rw) of {
             (lR, (lRw, d)) ->
               let {
                 qempty = Dependency_Pair_Problem_Spec.q_empty i dpp;
               } in (case Error_Monad.bind valid
                            (\ _ ->
                              Error_Monad.bind
                                (Check_Monad.check
                                  (if nfs
                                    then (if not qempty
   then Dependency_Pair_Problem_Spec.wwf_rules i dpp else True)
                                    else True)
                                  (Shows_Literal.showsl_lit
                                    "well formedness required"))
                                (\ _ ->
                                  Error_Monad.bind
                                    (Error_Monad.catch_error
                                      (Error_Monad.forallM
(\ (l, ra) ->
  Error_Monad.bind (Term_Impl.check_no_var l)
    (\ _ ->
      Error_Monad.bind (Term_Impl.check_no_var ra)
        (\ _ ->
          Q_Restricted_Rewriting_Impl.check_no_defined_root
            (\ fn ->
              not (null (Dependency_Pair_Problem_Spec.rules_map i dpp fn)))
            ra)))
(Dependency_Pair_Problem_Spec.pairs i dpp))
                                      (\ x -> Sum_Type.Inl (snd x)))
                                    (\ _ ->
                                      Error_Monad.bind
(Error_Monad.catch_error
  (Error_Monad.forallM (\ (l, _) -> Term_Impl.check_no_var l)
    (Dependency_Pair_Problem_Spec.rules i dpp))
  (\ x -> Sum_Type.Inl (snd x)))
(\ _ ->
  let {
    q = Dependency_Pair_Problem_Spec.q i dpp;
  } in Error_Monad.bind
         (if nfs && not qempty then Trs_Impl.check_wf_trs d
           else Sum_Type.Inr ())
         (\ _ ->
           Error_Monad.bind (check_decra d)
             (\ _ ->
               Error_Monad.bind (check_decr d)
                 (\ _ ->
                   Error_Monad.bind
                     (Error_Monad.catch_error
                       (Error_Monad.forallM
                         (\ qa ->
                           Check_Monad.check (Term_More.linear_term qa)
                             (Shows_Literal.showsl_lit
                               "Q must not contain non-linear terms"))
                         q)
                       (\ x -> Sum_Type.Inl (snd x)))
                     (\ _ ->
                       Error_Monad.catch_error
                         (Error_Monad.bind (check_lhss_more lQ q)
                           (\ _ ->
                             Error_Monad.bind (check_sl_Q ld lQ q)
                               (\ _ ->
                                 Error_Monad.bind
                                   (check_lab_all (List.set lP) p)
                                   (\ _ ->
                                     Error_Monad.bind
                                       (check_lab_all (List.set lPw) pw)
                                       (\ _ ->
 Error_Monad.bind (check_model_lab (List.set lR) r)
   (\ _ ->
     Error_Monad.bind (check_model_lab (List.set lRw) rw)
       (\ _ ->
         Error_Monad.bind (check_lab_all_trs lR r)
           (\ _ -> check_lab_all_trs lRw rw))))))))
                         (\ x ->
                           Sum_Type.Inl
                             (Shows_Literal.showsl_lit
                                "problem during labeling:\n" .
                               x))))))))))
                      of {
                      Sum_Type.Inl a -> Sum_Type.Inl a;
                      Sum_Type.Inr _ ->
                        Sum_Type.Inr
                          (Dependency_Pair_Problem_Spec.mk i nfs m lP lPw lQ lR
                            (lRw ++ d));
                    });
           });
       });

sem_lab_fin_quasi_root_proc ::
  forall a b c d e.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl c, Collection_Eq.Ceq e, Collection_Order.Ccompare e,
      Compare.Compare e, Eq e, Mapping_Impl.Mapping_impl e, Set_Impl.Set_impl e,
      Shows_Literal.Showl e) => (a -> Arith.Nat -> b -> a) ->
                                  (a -> (a, b)) ->
                                    (c -> c -> Bool) ->
                                      (a -> Arith.Nat -> b -> b -> Bool) ->
Dependency_Pair_Problem_Spec.Dpp_ops_ext d a e () ->
  ([(a, Arith.Nat)] ->
    [(a, Arith.Nat)] ->
      Sum_Type.Sum (String -> String) (Sl_ops_ext a c b e ())) ->
    [(Term.Term a e, Term.Term a e)] ->
      [Term.Term a e] ->
        [(Term.Term a e, Term.Term a e)] ->
          d -> Sum_Type.Sum (String -> String) d;
sem_lab_fin_quasi_root_proc lc ld cge lge i gen lPAll lQ lRAll dp =
  let {
    pairs = Dependency_Pair_Problem_Spec.pairs i dp;
  } in Error_Monad.bind
         (gen (Missing_List.list_union
                (Trs_Impl.insert_funas_trs
                  (Dependency_Pair_Problem_Spec.rules i dp) [])
                (Trs_Impl.insert_funas_args_trs pairs []))
           (Trs_Impl.insert_roots_trs pairs []))
         (\ ops ->
           let {
             check_d = sl_check_decr ops;
             check_da = check_sl_decr lc ld (sl_LS ops) lge;
             check_q = check_sl_lab_lhss_more lc (sl_LS_gen ops);
             check_ml =
               check_sl_model_lab_trs (sl_I ops) (sl_L ops) (sl_C ops) cge lc;
             check_l =
               check_sl_lab_all_trs (sl_I ops) (sl_L ops) (sl_La ops) (sl_C ops)
                 (sl_lgen ops) lc;
             check_la = check_Lab_all_trs lc ld (sl_LS ops);
           } in sem_lab_quasi_root_proc ld i (Sum_Type.Inr ()) check_d check_da
                  check_q check_l check_la check_ml lPAll lQ lRAll dp);

}
