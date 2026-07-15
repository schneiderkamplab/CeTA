{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module WDP_Transformation_Impl(Wdp_trans_info(..), check_wdp_trans) where {

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
import qualified Trs;
import qualified Option;
import qualified List;
import qualified Termination_Problem_Spec;
import qualified Complexity;
import qualified Mapping_Impl;
import qualified Multihole_Context_Impl;
import qualified Term_More;
import qualified Product_Type;
import qualified Sharp_Syntax;
import qualified Trs_Impl;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified HOL;
import qualified Multihole_Context;
import qualified Sum_Type;
import qualified Cardinality;
import qualified Collection_Enum;
import qualified Shows_Literal;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Compare;
import qualified Collection_Order;
import qualified Term;
import qualified Set;
import qualified Arith;

data Wdp_trans_info a b =
  WDP_Trans_Info (Set.Set (a, Arith.Nat))
    [((Term.Term a b, Term.Term a b), (Term.Term a b, Term.Term a b))]
    [((Term.Term a b, Term.Term a b), (Term.Term a b, Term.Term a b))]
    [Term.Term a b];

is_compound_context ::
  forall a b.
    (Cardinality.Finite_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Compare.Compare a, Eq a,
      Set_Impl.Set_impl a, Compare.Compare b,
      Eq b) => Set.Set (a, Arith.Nat) -> Multihole_Context.Mctxt a b -> Bool;
is_compound_context cComp c =
  Multihole_Context.ground_mctxt c &&
    Set.less_eq_set (Multihole_Context.funas_mctxt c) cComp;

check_rule_wdp ::
  forall a b.
    (Cardinality.Finite_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Compare.Compare a, Eq a,
      Set_Impl.Set_impl a, Shows_Literal.Showl a, Compare.Compare b, Eq b,
      Shows_Literal.Showl b) => (a -> a) ->
                                  Set.Set (a, Arith.Nat) ->
                                    ((Term.Term a b, Term.Term a b),
                                      (Term.Term a b, Term.Term a b)) ->
                                      Sum_Type.Sum (String -> String) ();
check_rule_wdp shp cComp =
  (\ (a, b) ->
    (case a of {
      (l, r) ->
        (\ (p, q) ->
          Error_Monad.catch_error
            (let {
               la = Sharp_Syntax.sharp_term shp l;
             } in Error_Monad.bind
                    (Check_Monad.check (Term.equal_term la p)
                      (((Shows_Literal.showsl_lit "wrong lhs, expected " .
                          Term_More.showsl_terma la) .
                         Shows_Literal.showsl_lit " but got ") .
                        Term_More.showsl_terma p))
                    (\ _ ->
                      let {
                        us = Multihole_Context.uncap_till
                               (Multihole_Context.if_Fun_in_set
                                 (Set.uminus_set cComp))
                               r;
                      } in (case Multihole_Context.split_term
                                   (Multihole_Context.if_Fun_in_set
                                     (Set.uminus_set cComp))
                                   q
                             of {
                             (c, usa) ->
                               Error_Monad.bind
                                 (Check_Monad.check
                                   (map (Sharp_Syntax.sharp_term shp) us == usa)
                                   (Shows_Literal.showsl_lit
                                     "lists of maximal subterms with defined root differ"))
                                 (\ _ ->
                                   Check_Monad.check
                                     (is_compound_context cComp c)
                                     ((Multihole_Context_Impl.showsl_mctxt c .
Shows_Literal.showsl_lit " is not a proper compound context of ") .
                                       Term_More.showsl_terma q));
                           })))
            (\ x ->
              Sum_Type.Inl
                (((((Shows_Literal.showsl_lit "could not ensure that " .
                      Trs_Impl.showsl_rule (p, q)) .
                     Shows_Literal.showsl_lit
                       " is a valid weak dependency pair for ") .
                    Trs_Impl.showsl_rule (l, r)) .
                   Shows_Literal.showsl_literal "\n") .
                  x)));
    })
      b);

check_wdp_trans ::
  forall a b c.
    (Cardinality.Finite_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Compare.Compare a, Eq a,
      Set_Impl.Set_impl a, Shows_Literal.Showl a, Collection_Order.Ccompare c,
      Compare.Compare c, Eq c, Mapping_Impl.Mapping_impl c,
      Shows_Literal.Showl c) => (a -> a) ->
                                  Termination_Problem_Spec.Tp_ops_ext b a c
                                    () ->
                                    Wdp_trans_info a c ->
                                      Complexity.Complexity_measure a c ->
Complexity.Complexity_class ->
  b -> Sum_Type.Sum (String -> String) (Complexity.Complexity_measure a c, b);
check_wdp_trans shp i info cm cc cp =
  Error_Monad.catch_error
    (case info of {
      WDP_Trans_Info comp s_wdps w_wdps q ->
        (case cm of {
          Complexity.Derivational_Complexity _ ->
            Sum_Type.Inl
              (Shows_Literal.showsl_lit
                "only runtime complexity supported for weak dependency pairs");
          Complexity.Runtime_Complexity c d ->
            let {
              s = Termination_Problem_Spec.r i cp;
              w = Termination_Problem_Spec.rw i cp;
              sa = map fst s_wdps;
              wa = map fst w_wdps;
              r = sa ++ wa;
              fs = Trs.funas_trs_list r;
              ds = Trs_Impl.defined_list r;
            } in Error_Monad.bind
                   (Error_Monad.catch_error
                     (Error_Monad.forallM
                       (\ ra ->
                         Check_Monad.check (any (Trs.eq_rule_mod_vars ra) sa)
                           (Shows_Literal.showsl_lit
                              "could not find weak dependency pair for strict rule " .
                             Shows_Literal.showsl_prod ra))
                       s)
                     (\ x -> Sum_Type.Inl (snd x)))
                   (\ _ ->
                     Error_Monad.bind
                       (Error_Monad.catch_error
                         (Error_Monad.forallM
                           (\ ra ->
                             Check_Monad.check
                               (any (Trs.eq_rule_mod_vars ra) wa)
                               (Shows_Literal.showsl_lit
                                  "could not find weak dependency pair for weak rule " .
                                 Shows_Literal.showsl_prod ra))
                           w)
                         (\ x -> Sum_Type.Inl (snd x)))
                       (\ _ ->
                         let {
                           wDP_S = map snd s_wdps;
                           wDP_W = map snd w_wdps;
                           shpf = (\ (f, a) -> (shp f, a));
                           f = fs ++ c ++ d;
                           f_sharps = map shpf f;
                           _ = Set.image (\ (fa, a) -> (shp fa, a))
                                 (List.set f);
                           cComp =
                             Set.sup_set
                               (Set.minus_set
                                 (Set.minus_set (List.set fs)
                                   (List.set (Trs_Impl.defined_list r)))
                                 (List.set d))
                               comp;
                         } in Error_Monad.bind
                                (Error_Monad.catch_error
                                  (Error_Monad.forallM
                                    (\ qa ->
                                      Check_Monad.check
(not (Term.is_Var qa) && not (List.member f (Option.the (Term.root qa))))
((Shows_Literal.showsl_lit "new Q-term " . Term_More.showsl_terma qa) .
  Shows_Literal.showsl_lit " not allowed"))
                                    q)
                                  (\ x -> Sum_Type.Inl (snd x)))
                                (\ _ ->
                                  Error_Monad.bind (Trs_Impl.check_wf_trs r)
                                    (\ _ ->
                                      Error_Monad.bind
(Error_Monad.catch_error
  (Error_Monad.forallM
    (\ fa ->
      Check_Monad.check (not (Set.member fa cComp))
        (Shows_Literal.showsl_prod fa .
          Shows_Literal.showsl_lit " clashes with sharp symbols"))
    f_sharps)
  (\ x -> Sum_Type.Inl (snd x)))
(\ _ ->
  Error_Monad.bind
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ fa ->
          Check_Monad.check (not (Set.member fa cComp))
            (Shows_Literal.showsl_prod fa .
              Shows_Literal.showsl_lit " clashes with defined symbols of RC"))
        d)
      (\ x -> Sum_Type.Inl (snd x)))
    (\ _ ->
      Error_Monad.bind
        (Error_Monad.catch_error
          (Error_Monad.forallM
            (\ fa ->
              Check_Monad.check (not (Set.member fa cComp))
                (Shows_Literal.showsl_prod fa .
                  Shows_Literal.showsl_lit " clashes with defined symbols"))
            ds)
          (\ x -> Sum_Type.Inl (snd x)))
        (\ _ ->
          Error_Monad.bind
            (Error_Monad.catch_error
              (Error_Monad.forallM (check_rule_wdp shp cComp) s_wdps)
              (\ x -> Sum_Type.Inl (snd x)))
            (\ _ ->
              Error_Monad.bind
                (Error_Monad.catch_error
                  (Error_Monad.forallM (check_rule_wdp shp cComp) w_wdps)
                  (\ x -> Sum_Type.Inl (snd x)))
                (\ _ ->
                  Sum_Type.Inr
                    (Complexity.Runtime_Complexity c (map shpf d),
                      Termination_Problem_Spec.mk i
                        (Termination_Problem_Spec.nfs i cp)
                        (Termination_Problem_Spec.q i cp ++ q) (wDP_S ++ sa)
                        (wDP_W ++ wa)))))))))));
        });
    })
    (\ x ->
      Sum_Type.Inl
        ((Shows_Literal.showsl_lit
            "error when switching to weak dependency pairs" .
           Shows_Literal.showsl_literal "\n") .
          x));

}
