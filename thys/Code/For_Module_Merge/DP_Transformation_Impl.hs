{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module DP_Transformation_Impl(dP_list, dependency_pairs_tt) where {

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
import qualified Product_Type;
import qualified Trs_Impl;
import qualified Trs;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Dependency_Pair_Problem_Spec;
import qualified Termination_Problem_Spec;
import qualified Sum_Type;
import qualified Set;
import qualified Mapping_Impl;
import qualified Shows_Literal;
import qualified Orderings;
import qualified Compare;
import qualified Collection_Order;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Container_Setup;
import qualified Sharp_Syntax;
import qualified Term_Impl;
import qualified Option;
import qualified List;
import qualified HOL;
import qualified Term;
import qualified Arith;

dP_list ::
  forall a b.
    (Eq a,
      Eq b) => (a -> a) ->
                 [(Term.Term a b, Term.Term a b)] ->
                   [(a, Arith.Nat)] -> [(Term.Term a b, Term.Term a b)];
dP_list shp r d_list =
  concatMap
    (\ lr ->
      let {
        l = fst lr;
        s = Sharp_Syntax.sharp_term shp l;
      } in List.map_filter
             (\ x ->
               (if not (Term_Impl.supt_impl l x) &&
                     not (Term.is_Var x) &&
                       List.member d_list (Option.the (Term.root x))
                 then Just (s, Sharp_Syntax.sharp_term shp x) else Nothing))
             (Term_Impl.supteq_list (snd lr)))
    r;

dependency_pairs_tt ::
  forall a b c d.
    (Compare.Compare a, Eq a, Orderings.Linorder a, Shows_Literal.Showl a,
      Collection_Order.Ccompare c, Compare.Compare c, Eq c,
      Mapping_Impl.Mapping_impl c, Orderings.Linorder c,
      Shows_Literal.Showl c) => (a -> a) ->
                                  Termination_Problem_Spec.Tp_ops_ext b a c
                                    () ->
                                    Dependency_Pair_Problem_Spec.Dpp_ops_ext d a
                                      c () ->
                                      b ->
Bool ->
  Bool -> [(Term.Term a c, Term.Term a c)] -> Sum_Type.Sum (String -> String) d;
dependency_pairs_tt shp i j tp nfs m p =
  let {
    r = Termination_Problem_Spec.rules i tp;
    q = Termination_Problem_Spec.q i tp;
    iQ = Termination_Problem_Spec.is_QNF i tp;
    u = filter (Q_Restricted_Rewriting_Impl.applicable_rule_impl iQ) r;
  } in (case Error_Monad.catch_error
               (Error_Monad.bind
                 (if Error_Monad.isOK (Trs_Impl.check_wf_trs u)
                   then Sum_Type.Inr ()
                   else Check_Monad.check
                          (nfs &&
                            Termination_Problem_Spec.nfs i tp &&
                              Termination_Problem_Spec.nFQ_subset_NF_rules i
                                tp &&
                                all (\ l -> not (Term.is_Var l)) (map fst r))
                          (Shows_Literal.showsl_lit
                            "neither is the TRS well-formed, nor is the restriction to innermost with normal form substitutions present"))
                 (\ _ ->
                   Error_Monad.bind
                     (Error_Monad.catch_error
                       (Error_Monad.forallM Term_Impl.check_no_var q)
                       (\ x -> Sum_Type.Inl (snd x)))
                     (\ _ ->
                       let {
                         qr = map (\ (Term.Fun f ss) -> (f, List.size_list ss))
                                q;
                         d = Trs_Impl.defined_list u;
                       } in Error_Monad.bind
                              (Error_Monad.catch_error
                                (Error_Monad.forallM
                                  (\ (f, n) ->
                                    Check_Monad.check
                                      (not (List.member d (shp f, n)))
                                      (((Shows_Literal.showsl_lit "sharping " .
  Shows_Literal.showsl f) .
 Shows_Literal.showsl_lit " yields the defined symbol ") .
Shows_Literal.showsl (shp f)))
                                  d)
                                (\ x -> Sum_Type.Inl (snd x)))
                              (\ _ ->
                                Error_Monad.bind
                                  (Error_Monad.catch_error
                                    (Error_Monad.forallM
                                      (\ (f, n) ->
Check_Monad.check (not (List.member qr (shp f, n)))
  ((((Shows_Literal.showsl_lit "sharping " . Shows_Literal.showsl f) .
      Shows_Literal.showsl_lit " yields the symbol ") .
     Shows_Literal.showsl (shp f)) .
    Shows_Literal.showsl_lit " which is a root of Q"))
                                      d)
                                    (\ x -> Sum_Type.Inl (snd x)))
                                  (\ _ ->
                                    let {
                                      pa = List.set p;
                                    } in Error_Monad.catch_error
   (Error_Monad.catch_error
     (Error_Monad.forallM
       (\ x ->
         (if Set.member x pa || any (Trs.eq_rule_mod_vars x) p
           then Sum_Type.Inr () else Sum_Type.Inl x))
       (dP_list shp u d))
     (\ x -> Sum_Type.Inl (snd x)))
   (\ x ->
     Sum_Type.Inl
       ((Shows_Literal.showsl_lit "the DP " . Trs_Impl.showsl_rule x) .
         Shows_Literal.showsl_lit " does not appear in the DP problem\n")))))))
               (\ x ->
                 Sum_Type.Inl
                   (Shows_Literal.showsl_lit
                      "the DP-transformation is not applied correctly.\n" .
                     x))
         of {
         Sum_Type.Inl a -> Sum_Type.Inl a;
         Sum_Type.Inr _ ->
           Sum_Type.Inr (Dependency_Pair_Problem_Spec.mk j nfs m p [] q [] r);
       });

}
