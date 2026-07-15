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
import qualified Termination_Problem_Spec;
import qualified Mapping;
import qualified Sharp_Syntax;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified HOL;
import qualified Sum_Type;
import qualified Compare;
import qualified Term_Rewriting;
import qualified Arith;

data Wdp_trans_info a b =
  WDP_Trans_Info (Arith.Set (a, Arith.Nat))
    [((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
       (Term_Rewriting.Term a b, Term_Rewriting.Term a b))]
    [((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
       (Term_Rewriting.Term a b, Term_Rewriting.Term a b))]
    [Term_Rewriting.Term a b];

is_compound_context ::
  forall a b.
    (Arith.Finite_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Compare.Compare a, Eq a, Arith.Set_impl a, Compare.Compare b,
      Eq b) => Arith.Set (a, Arith.Nat) -> Term_Rewriting.Mctxt a b -> Bool;
is_compound_context cComp c =
  Term_Rewriting.ground_mctxt c &&
    Arith.less_eq_set (Term_Rewriting.funas_mctxt c) cComp;

check_rule_wdp ::
  forall a b.
    (Arith.Finite_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Compare.Compare a, Eq a, Arith.Set_impl a, Term_Rewriting.Showl a,
      Compare.Compare b, Eq b,
      Term_Rewriting.Showl b) => (a -> a) ->
                                   Arith.Set (a, Arith.Nat) ->
                                     ((Term_Rewriting.Term a b,
Term_Rewriting.Term a b),
                                       (Term_Rewriting.Term a b,
 Term_Rewriting.Term a b)) ->
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
                    (Check_Monad.check (Term_Rewriting.equal_term la p)
                      (((Term_Rewriting.showsl_lit "wrong lhs, expected " .
                          Term_Rewriting.showsl_terma la) .
                         Term_Rewriting.showsl_lit " but got ") .
                        Term_Rewriting.showsl_terma p))
                    (\ _ ->
                      let {
                        us = Term_Rewriting.uncap_till
                               (Term_Rewriting.if_Fun_in_set
                                 (Arith.uminus_set cComp))
                               r;
                      } in (case Term_Rewriting.split_term
                                   (Term_Rewriting.if_Fun_in_set
                                     (Arith.uminus_set cComp))
                                   q
                             of {
                             (c, usa) ->
                               Error_Monad.bind
                                 (Check_Monad.check
                                   (map (Sharp_Syntax.sharp_term shp) us == usa)
                                   (Term_Rewriting.showsl_lit
                                     "lists of maximal subterms with defined root differ"))
                                 (\ _ ->
                                   Check_Monad.check
                                     (is_compound_context cComp c)
                                     ((Term_Rewriting.showsl_mctxt c .
Term_Rewriting.showsl_lit " is not a proper compound context of ") .
                                       Term_Rewriting.showsl_terma q));
                           })))
            (\ x ->
              Sum_Type.Inl
                (((((Term_Rewriting.showsl_lit "could not ensure that " .
                      Term_Rewriting.showsl_rule (p, q)) .
                     Term_Rewriting.showsl_lit
                       " is a valid weak dependency pair for ") .
                    Term_Rewriting.showsl_rule (l, r)) .
                   Term_Rewriting.showsl_literal "\n") .
                  x)));
    })
      b);

check_wdp_trans ::
  forall a b c.
    (Arith.Finite_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Compare.Compare a, Eq a, Arith.Set_impl a, Term_Rewriting.Showl a,
      Arith.Ccompare c, Compare.Compare c, Eq c, Mapping.Mapping_impl c,
      Term_Rewriting.Showl c) => (a -> a) ->
                                   Termination_Problem_Spec.Tp_ops_ext b a c
                                     () ->
                                     Wdp_trans_info a c ->
                                       Term_Rewriting.Complexity_measure a c ->
 Term_Rewriting.Complexity_class ->
   b -> Sum_Type.Sum (String -> String)
          (Term_Rewriting.Complexity_measure a c, b);
check_wdp_trans shp i info cm cc cp =
  Error_Monad.catch_error
    (case info of {
      WDP_Trans_Info comp s_wdps w_wdps q ->
        (case cm of {
          Term_Rewriting.Derivational_Complexity _ ->
            Sum_Type.Inl
              (Term_Rewriting.showsl_lit
                "only runtime complexity supported for weak dependency pairs");
          Term_Rewriting.Runtime_Complexity c d ->
            let {
              s = Termination_Problem_Spec.r i cp;
              w = Termination_Problem_Spec.rw i cp;
              sa = map fst s_wdps;
              wa = map fst w_wdps;
              r = sa ++ wa;
              fs = Term_Rewriting.funas_trs_list r;
              ds = Term_Rewriting.defined_list r;
            } in Error_Monad.bind
                   (Error_Monad.catch_error
                     (Error_Monad.forallM
                       (\ ra ->
                         Check_Monad.check
                           (any (Term_Rewriting.eq_rule_mod_vars ra) sa)
                           (Term_Rewriting.showsl_lit
                              "could not find weak dependency pair for strict rule " .
                             Term_Rewriting.showsl_prod ra))
                       s)
                     (\ x -> Sum_Type.Inl (snd x)))
                   (\ _ ->
                     Error_Monad.bind
                       (Error_Monad.catch_error
                         (Error_Monad.forallM
                           (\ ra ->
                             Check_Monad.check
                               (any (Term_Rewriting.eq_rule_mod_vars ra) wa)
                               (Term_Rewriting.showsl_lit
                                  "could not find weak dependency pair for weak rule " .
                                 Term_Rewriting.showsl_prod ra))
                           w)
                         (\ x -> Sum_Type.Inl (snd x)))
                       (\ _ ->
                         let {
                           wDP_S = map snd s_wdps;
                           wDP_W = map snd w_wdps;
                           shpf = (\ (f, a) -> (shp f, a));
                           f = fs ++ c ++ d;
                           f_sharps = map shpf f;
                           _ = Arith.image (\ (fa, a) -> (shp fa, a))
                                 (Arith.set f);
                           cComp =
                             Arith.sup_set
                               (Arith.minus_set
                                 (Arith.minus_set (Arith.set fs)
                                   (Arith.set (Term_Rewriting.defined_list r)))
                                 (Arith.set d))
                               comp;
                         } in Error_Monad.bind
                                (Error_Monad.catch_error
                                  (Error_Monad.forallM
                                    (\ qa ->
                                      Check_Monad.check
(not (Term_Rewriting.is_Var qa) &&
  not (Arith.membera f (Arith.the (Term_Rewriting.root qa))))
((Term_Rewriting.showsl_lit "new Q-term " . Term_Rewriting.showsl_terma qa) .
  Term_Rewriting.showsl_lit " not allowed"))
                                    q)
                                  (\ x -> Sum_Type.Inl (snd x)))
                                (\ _ ->
                                  Error_Monad.bind
                                    (Term_Rewriting.check_wf_trs r)
                                    (\ _ ->
                                      Error_Monad.bind
(Error_Monad.catch_error
  (Error_Monad.forallM
    (\ fa ->
      Check_Monad.check (not (Arith.member fa cComp))
        (Term_Rewriting.showsl_prod fa .
          Term_Rewriting.showsl_lit " clashes with sharp symbols"))
    f_sharps)
  (\ x -> Sum_Type.Inl (snd x)))
(\ _ ->
  Error_Monad.bind
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ fa ->
          Check_Monad.check (not (Arith.member fa cComp))
            (Term_Rewriting.showsl_prod fa .
              Term_Rewriting.showsl_lit " clashes with defined symbols of RC"))
        d)
      (\ x -> Sum_Type.Inl (snd x)))
    (\ _ ->
      Error_Monad.bind
        (Error_Monad.catch_error
          (Error_Monad.forallM
            (\ fa ->
              Check_Monad.check (not (Arith.member fa cComp))
                (Term_Rewriting.showsl_prod fa .
                  Term_Rewriting.showsl_lit " clashes with defined symbols"))
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
                    (Term_Rewriting.Runtime_Complexity c (map shpf d),
                      Termination_Problem_Spec.mk i
                        (Termination_Problem_Spec.nfs i cp)
                        (Termination_Problem_Spec.q i cp ++ q) (wDP_S ++ sa)
                        (wDP_W ++ wa)))))))))));
        });
    })
    (\ x ->
      Sum_Type.Inl
        ((Term_Rewriting.showsl_lit
            "error when switching to weak dependency pairs" .
           Term_Rewriting.showsl_literal "\n") .
          x));

}
