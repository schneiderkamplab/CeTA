{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module DT_Transformation_Impl(Dt_transformation_info(..), dt_transformation)
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
import qualified Termination_Problem_Spec;
import qualified Mapping;
import qualified Sharp_Syntax;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Multiset;
import qualified Sum_Type;
import qualified HOL;
import qualified Arith;
import qualified Term_Rewriting;

data Dt_transformation_info a b =
  DT_Transformation_Info
    [((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
       (Term_Rewriting.Term a b, Term_Rewriting.Term a b))]
    [((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
       (Term_Rewriting.Term a b, Term_Rewriting.Term a b))]
    [Term_Rewriting.Term a b];

dPos_impl ::
  forall a b.
    (Arith.Ceq a,
      Arith.Ccompare a) => (a -> a) ->
                             Arith.Set (a, Arith.Nat) ->
                               Term_Rewriting.Term a b ->
                                 [([Arith.Nat], Term_Rewriting.Term a b)];
dPos_impl shp d (Term_Rewriting.Var x) = [];
dPos_impl shp d (Term_Rewriting.Fun f ts) =
  let {
    n = Arith.size_list ts;
  } in (if Arith.member (f, n) d
         then (\ a -> ([], Term_Rewriting.Fun (shp f) ts) : a) else id)
         (concatMap
           (\ (i, ti) -> map (\ (p, a) -> (i : p, a)) (dPos_impl shp d ti))
           (zip (Arith.upt Arith.zero_nat n) ts));

check_tup ::
  forall a b.
    (Arith.Ceq a,
      Arith.Ccompare a) => Arith.Set a -> Term_Rewriting.Term a b -> Bool;
check_tup t (Term_Rewriting.Var x) = False;
check_tup t (Term_Rewriting.Fun f ts) = Arith.member f t;

check_rule_dt ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Eq a, Term_Rewriting.Showl a, Eq b,
      Term_Rewriting.Showl b) => (a -> a) ->
                                   Arith.Set (a, Arith.Nat) ->
                                     Arith.Set a ->
                                       ((Term_Rewriting.Term a b,
  Term_Rewriting.Term a b),
 (Term_Rewriting.Term a b, Term_Rewriting.Term a b)) ->
 Sum_Type.Sum (String -> String) ();
check_rule_dt shp d ds =
  (\ (a, b) ->
    (case a of {
      (l, r) ->
        (\ (dl, dr) ->
          Error_Monad.catch_error
            (let {
               sl = Sharp_Syntax.sharp_term shp l;
             } in Error_Monad.bind
                    (Check_Monad.check (Term_Rewriting.equal_term sl dl)
                      (((Term_Rewriting.showsl_lit "wrong lhs, expected " .
                          Term_Rewriting.showsl_terma sl) .
                         Term_Rewriting.showsl_lit " but got ") .
                        Term_Rewriting.showsl_terma dl))
                    (\ _ ->
                      let {
                        pts = dPos_impl shp d r;
                        spts = map snd pts;
                      } in (case Term_Rewriting.split_term (check_tup ds) dr of
                             {
                             (_, dts) ->
                               Check_Monad.check
                                 (Multiset.equal_multiset (Multiset.mset dts)
                                   (Multiset.mset spts))
                                 (Term_Rewriting.showsl_lit
                                   "multiset of subterms with defined roots differs");
                           })))
            (\ x ->
              Sum_Type.Inl
                (((((Term_Rewriting.showsl_lit "could not ensure that " .
                      Term_Rewriting.showsl_rule (dl, dr)) .
                     Term_Rewriting.showsl_lit
                       " is a valid dependency tuple for ") .
                    Term_Rewriting.showsl_rule (l, r)) .
                   Term_Rewriting.showsl_literal "\n") .
                  x)));
    })
      b);

dt_transformation ::
  forall a b c.
    (Arith.Card_UNIV a, Arith.Ceq a, Arith.Cproper_interval a, Eq a,
      Arith.Set_impl a, Term_Rewriting.Showl a, Arith.Ccompare c, Eq c,
      Mapping.Mapping_impl c,
      Term_Rewriting.Showl c) => (a -> a) ->
                                   Termination_Problem_Spec.Tp_ops_ext b a c
                                     () ->
                                     Dt_transformation_info a c ->
                                       Term_Rewriting.Complexity_measure a c ->
 Term_Rewriting.Complexity_class ->
   b -> Sum_Type.Sum (String -> String)
          (Term_Rewriting.Complexity_measure a c, b);
dt_transformation shp i info cm cc cp =
  Error_Monad.catch_error
    (case info of {
      DT_Transformation_Info s_DT_s w_DT_w q ->
        (case cm of {
          Term_Rewriting.Derivational_Complexity _ ->
            Sum_Type.Inl
              (Term_Rewriting.showsl_lit
                "only runtime complexity supported for dependency tuples");
          Term_Rewriting.Runtime_Complexity c d ->
            let {
              s = Termination_Problem_Spec.r i cp;
              w = Termination_Problem_Spec.rw i cp;
              sa = map fst s_DT_s;
              wa = map fst w_DT_w;
              r = sa ++ wa;
              dd = Term_Rewriting.defined_list r;
              dda = Arith.set d;
            } in Error_Monad.bind
                   (Error_Monad.catch_error
                     (Error_Monad.forallM
                       (\ lr ->
                         Check_Monad.check
                           (any (Term_Rewriting.eq_rule_mod_vars lr) sa)
                           (Term_Rewriting.showsl_lit
                              "could not find DT for strict rule " .
                             Term_Rewriting.showsl_prod lr))
                       s)
                     (\ x -> Sum_Type.Inl (snd x)))
                   (\ _ ->
                     Error_Monad.bind
                       (Error_Monad.catch_error
                         (Error_Monad.forallM
                           (\ lr ->
                             Check_Monad.check
                               (any (Term_Rewriting.eq_rule_mod_vars lr) wa)
                               (Term_Rewriting.showsl_lit
                                  "could not find DT for weak rule " .
                                 Term_Rewriting.showsl_prod lr))
                           w)
                         (\ x -> Sum_Type.Inl (snd x)))
                       (\ _ ->
                         Error_Monad.bind
                           (Error_Monad.catch_error
                             (Error_Monad.forallM
                               (\ f ->
                                 Check_Monad.check (Arith.member f dda)
                                   ((Term_Rewriting.showsl_lit
                                       "defined symbol " .
                                      Term_Rewriting.showsl_prod f) .
                                     Term_Rewriting.showsl_lit
                                       " does not occur in defined symbols from RC"))
                               dd)
                             (\ x -> Sum_Type.Inl (snd x)))
                           (\ _ ->
                             let {
                               dTs = map snd s_DT_s;
                               dTw = map snd w_DT_w;
                               da = Arith.set dd;
                               shpf = (\ (f, a) -> (shp f, a));
                               ds = Arith.image shpf da;
                               ddd = Arith.image (shp . fst) da;
                               f = Term_Rewriting.funas_trs_list r ++ c ++ d;
                               fs = Arith.set f;
                             } in Error_Monad.bind
                                    (Error_Monad.catch_error
                                      (Error_Monad.forallM
(\ qa ->
  Check_Monad.check
    (not (Term_Rewriting.is_Var qa) &&
      not (Arith.member (Arith.the (Term_Rewriting.root qa)) fs))
    ((Term_Rewriting.showsl_lit "new Q-term " .
       Term_Rewriting.showsl_terma qa) .
      Term_Rewriting.showsl_lit " not allowed"))
q)
                                      (\ x -> Sum_Type.Inl (snd x)))
                                    (\ _ ->
                                      Error_Monad.bind
(Term_Rewriting.check_wf_trs r)
(\ _ ->
  Error_Monad.bind
    (Error_Monad.catch_error
      (Q_Restricted_Rewriting_Impl.check_NF_terms_subset
        (Termination_Problem_Spec.is_QNF i cp) (map fst r))
      (\ _ -> Sum_Type.Inl (Term_Rewriting.showsl_lit "innermost required")))
    (\ _ ->
      Error_Monad.bind
        (Error_Monad.catch_error
          (Error_Monad.forallM
            (\ fa ->
              Check_Monad.check (not (Arith.member fa ds))
                (Term_Rewriting.showsl_prod fa .
                  Term_Rewriting.showsl_lit " as sharped symbol is not fresh"))
            f)
          (\ x -> Sum_Type.Inl (snd x)))
        (\ _ ->
          Error_Monad.bind
            (Check_Monad.check (Arith.is_empty (Arith.inf_set (Arith.set c) da))
              (Term_Rewriting.showsl_lit
                "constructors of RC and defined symbols of TRSs are not disjoint"))
            (\ _ ->
              Error_Monad.bind
                (Error_Monad.catch_error
                  (Error_Monad.forallM (check_rule_dt shp da ddd) s_DT_s)
                  (\ x -> Sum_Type.Inl (snd x)))
                (\ _ ->
                  Error_Monad.bind
                    (Error_Monad.catch_error
                      (Error_Monad.forallM (check_rule_dt shp da ddd) w_DT_w)
                      (\ x -> Sum_Type.Inl (snd x)))
                    (\ _ ->
                      Sum_Type.Inr
                        (Term_Rewriting.Runtime_Complexity c (map shpf d),
                          Termination_Problem_Spec.mk i False
                            (Termination_Problem_Spec.q i cp ++ q) dTs
                            (r ++ dTw))))))))))));
        });
    })
    (\ x ->
      Sum_Type.Inl
        (Term_Rewriting.showsl_lit
           "error when switching to dependency tuples\n" .
          x));

}
