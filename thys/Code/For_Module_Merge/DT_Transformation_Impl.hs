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
import qualified Trs;
import qualified Option;
import qualified Termination_Problem_Spec;
import qualified Complexity;
import qualified Mapping_Impl;
import qualified Cardinality;
import qualified Set_Impl;
import qualified Term_More;
import qualified Sharp_Syntax;
import qualified Trs_Impl;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Multihole_Context;
import qualified Multiset;
import qualified Sum_Type;
import qualified Shows_Literal;
import qualified Product_Type;
import qualified List;
import qualified HOL;
import qualified Set;
import qualified Arith;
import qualified Collection_Order;
import qualified Collection_Eq;
import qualified Term;

data Dt_transformation_info a b =
  DT_Transformation_Info
    [((Term.Term a b, Term.Term a b), (Term.Term a b, Term.Term a b))]
    [((Term.Term a b, Term.Term a b), (Term.Term a b, Term.Term a b))]
    [Term.Term a b];

dPos_impl ::
  forall a b.
    (Collection_Eq.Ceq a,
      Collection_Order.Ccompare a) => (a -> a) ->
Set.Set (a, Arith.Nat) -> Term.Term a b -> [([Arith.Nat], Term.Term a b)];
dPos_impl shp d (Term.Var x) = [];
dPos_impl shp d (Term.Fun f ts) =
  let {
    n = List.size_list ts;
  } in (if Set.member (f, n) d then (\ a -> ([], Term.Fun (shp f) ts) : a)
         else id)
         (concatMap
           (\ (i, ti) -> map (\ (p, a) -> (i : p, a)) (dPos_impl shp d ti))
           (zip (List.upt Arith.zero_nat n) ts));

check_tup ::
  forall a b.
    (Collection_Eq.Ceq a,
      Collection_Order.Ccompare a) => Set.Set a -> Term.Term a b -> Bool;
check_tup t (Term.Var x) = False;
check_tup t (Term.Fun f ts) = Set.member f t;

check_rule_dt ::
  forall a b.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Eq a,
      Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => (a -> a) ->
                                  Set.Set (a, Arith.Nat) ->
                                    Set.Set a ->
                                      ((Term.Term a b, Term.Term a b),
(Term.Term a b, Term.Term a b)) ->
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
                    (Check_Monad.check (Term.equal_term sl dl)
                      (((Shows_Literal.showsl_lit "wrong lhs, expected " .
                          Term_More.showsl_terma sl) .
                         Shows_Literal.showsl_lit " but got ") .
                        Term_More.showsl_terma dl))
                    (\ _ ->
                      let {
                        pts = dPos_impl shp d r;
                        spts = map snd pts;
                      } in (case Multihole_Context.split_term (check_tup ds) dr
                             of {
                             (_, dts) ->
                               Check_Monad.check
                                 (Multiset.equal_multiset (Multiset.mset dts)
                                   (Multiset.mset spts))
                                 (Shows_Literal.showsl_lit
                                   "multiset of subterms with defined roots differs");
                           })))
            (\ x ->
              Sum_Type.Inl
                (((((Shows_Literal.showsl_lit "could not ensure that " .
                      Trs_Impl.showsl_rule (dl, dr)) .
                     Shows_Literal.showsl_lit
                       " is a valid dependency tuple for ") .
                    Trs_Impl.showsl_rule (l, r)) .
                   Shows_Literal.showsl_literal "\n") .
                  x)));
    })
      b);

dt_transformation ::
  forall a b c.
    (Cardinality.Card_UNIV a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Eq a, Set_Impl.Set_impl a,
      Shows_Literal.Showl a, Collection_Order.Ccompare c, Eq c,
      Mapping_Impl.Mapping_impl c,
      Shows_Literal.Showl c) => (a -> a) ->
                                  Termination_Problem_Spec.Tp_ops_ext b a c
                                    () ->
                                    Dt_transformation_info a c ->
                                      Complexity.Complexity_measure a c ->
Complexity.Complexity_class ->
  b -> Sum_Type.Sum (String -> String) (Complexity.Complexity_measure a c, b);
dt_transformation shp i info cm cc cp =
  Error_Monad.catch_error
    (case info of {
      DT_Transformation_Info s_DT_s w_DT_w q ->
        (case cm of {
          Complexity.Derivational_Complexity _ ->
            Sum_Type.Inl
              (Shows_Literal.showsl_lit
                "only runtime complexity supported for dependency tuples");
          Complexity.Runtime_Complexity c d ->
            let {
              s = Termination_Problem_Spec.r i cp;
              w = Termination_Problem_Spec.rw i cp;
              sa = map fst s_DT_s;
              wa = map fst w_DT_w;
              r = sa ++ wa;
              dd = Trs_Impl.defined_list r;
              dda = List.set d;
            } in Error_Monad.bind
                   (Error_Monad.catch_error
                     (Error_Monad.forallM
                       (\ lr ->
                         Check_Monad.check (any (Trs.eq_rule_mod_vars lr) sa)
                           (Shows_Literal.showsl_lit
                              "could not find DT for strict rule " .
                             Shows_Literal.showsl_prod lr))
                       s)
                     (\ x -> Sum_Type.Inl (snd x)))
                   (\ _ ->
                     Error_Monad.bind
                       (Error_Monad.catch_error
                         (Error_Monad.forallM
                           (\ lr ->
                             Check_Monad.check
                               (any (Trs.eq_rule_mod_vars lr) wa)
                               (Shows_Literal.showsl_lit
                                  "could not find DT for weak rule " .
                                 Shows_Literal.showsl_prod lr))
                           w)
                         (\ x -> Sum_Type.Inl (snd x)))
                       (\ _ ->
                         Error_Monad.bind
                           (Error_Monad.catch_error
                             (Error_Monad.forallM
                               (\ f ->
                                 Check_Monad.check (Set.member f dda)
                                   ((Shows_Literal.showsl_lit
                                       "defined symbol " .
                                      Shows_Literal.showsl_prod f) .
                                     Shows_Literal.showsl_lit
                                       " does not occur in defined symbols from RC"))
                               dd)
                             (\ x -> Sum_Type.Inl (snd x)))
                           (\ _ ->
                             let {
                               dTs = map snd s_DT_s;
                               dTw = map snd w_DT_w;
                               da = List.set dd;
                               shpf = (\ (f, a) -> (shp f, a));
                               ds = Set.image shpf da;
                               ddd = Set.image (shp . fst) da;
                               f = Trs.funas_trs_list r ++ c ++ d;
                               fs = List.set f;
                             } in Error_Monad.bind
                                    (Error_Monad.catch_error
                                      (Error_Monad.forallM
(\ qa ->
  Check_Monad.check
    (not (Term.is_Var qa) && not (Set.member (Option.the (Term.root qa)) fs))
    ((Shows_Literal.showsl_lit "new Q-term " . Term_More.showsl_terma qa) .
      Shows_Literal.showsl_lit " not allowed"))
q)
                                      (\ x -> Sum_Type.Inl (snd x)))
                                    (\ _ ->
                                      Error_Monad.bind (Trs_Impl.check_wf_trs r)
(\ _ ->
  Error_Monad.bind
    (Error_Monad.catch_error
      (Q_Restricted_Rewriting_Impl.check_NF_terms_subset
        (Termination_Problem_Spec.is_QNF i cp) (map fst r))
      (\ _ -> Sum_Type.Inl (Shows_Literal.showsl_lit "innermost required")))
    (\ _ ->
      Error_Monad.bind
        (Error_Monad.catch_error
          (Error_Monad.forallM
            (\ fa ->
              Check_Monad.check (not (Set.member fa ds))
                (Shows_Literal.showsl_prod fa .
                  Shows_Literal.showsl_lit " as sharped symbol is not fresh"))
            f)
          (\ x -> Sum_Type.Inl (snd x)))
        (\ _ ->
          Error_Monad.bind
            (Check_Monad.check (Set.is_empty (Set.inf_set (List.set c) da))
              (Shows_Literal.showsl_lit
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
                        (Complexity.Runtime_Complexity c (map shpf d),
                          Termination_Problem_Spec.mk i False
                            (Termination_Problem_Spec.q i cp ++ q) dTs
                            (r ++ dTw))))))))))));
        });
    })
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "error when switching to dependency tuples\n" .
          x));

}
