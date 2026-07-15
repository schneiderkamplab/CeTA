{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  AC_Dependency_Pairs_Impl(Ac_dependency_pairs_proof(..),
                            ac_dependency_pairs_proc,
                            ac_dependency_pairs_proc_simple)
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
import qualified AC_Rewriting_Impl;
import qualified DP_Transformation_Impl;
import qualified Missing_List;
import qualified Trs_Impl;
import qualified Trs;
import qualified Check_Monad;
import qualified List;
import qualified Set;
import qualified Arith;
import qualified Product_Type;
import qualified Sharp_Syntax;
import qualified Error_Monad;
import qualified HOL;
import qualified AC_Dependency_Pair_Problem_Spec;
import qualified AC_Termination_Problem_Spec;
import qualified Sum_Type;
import qualified Mapping_Impl;
import qualified Collection_Order;
import qualified Collection_Enum;
import qualified Shows_Literal;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Term;

data Ac_dependency_pairs_proof a b =
  AC_dependency_pairs_proof [(Term.Term a b, Term.Term a b)]
    [(Term.Term a b, Term.Term a b)] [(Term.Term a b, Term.Term a b)]
    [(Term.Term a b, Term.Term a b)];

ac_dependency_pairs_checks ::
  forall a b c.
    (Collection_Enum.Cenum b, Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Eq b, Set_Impl.Set_impl b, Shows_Literal.Showl b, Collection_Eq.Ceq c,
      Collection_Order.Ccompare c, Eq c, Mapping_Impl.Mapping_impl c,
      Set_Impl.Set_impl c,
      Shows_Literal.Showl c) => AC_Termination_Problem_Spec.Ac_tp_ops_ext a b c
                                  () ->
                                  (b -> b) ->
                                    c -> c ->
   c -> Ac_dependency_pairs_proof b c ->
          a -> Sum_Type.Sum (String -> String) ();
ac_dependency_pairs_checks i shp x y z
  (AC_dependency_pairs_proof e dpr dpe rext) tp =
  Error_Monad.catch_error
    (let {
       a = AC_Termination_Problem_Spec.a i tp;
       c = AC_Termination_Problem_Spec.c i tp;
       r = AC_Termination_Problem_Spec.r i tp;
       oc = Missing_List.list_diff c a;
       d = Trs_Impl.defined_list r;
       _ = List.set d;
       da = Trs_Impl.defined_list (r ++ e);
     } in Error_Monad.bind
            (Error_Monad.catch_error
              (Error_Monad.forallM
                (\ (f, n) ->
                  Check_Monad.check (not (List.member da (shp f, n)))
                    (((Shows_Literal.showsl_lit "sharping " .
                        Shows_Literal.showsl f) .
                       Shows_Literal.showsl_lit " yields the defined symbol ") .
                      Shows_Literal.showsl (shp f)))
                da)
              (\ xa -> Sum_Type.Inl (snd xa)))
            (\ _ ->
              Error_Monad.bind
                (Error_Monad.catch_error (Trs_Impl.check_wf_trs (r ++ e))
                  (\ xa ->
                    Sum_Type.Inl
                      (Shows_Literal.showsl_lit
                         "TRS or equations are not well-formed" .
                        xa)))
                (\ _ ->
                  Error_Monad.bind
                    (Error_Monad.catch_error
                      (AC_Rewriting_Impl.check_symmetric_AC_theory e)
                      (\ xa ->
                        Sum_Type.Inl
                          (Shows_Literal.showsl_lit
                             "equations do not form a symmetric AC-theory\n" .
                            xa)))
                    (\ _ ->
                      Error_Monad.bind
                        (Error_Monad.catch_error
                          (AC_Rewriting_Impl.check_only_C_theory (List.set oc)
                            e)
                          (\ xa ->
                            Sum_Type.Inl
                              (Shows_Literal.showsl_lit
                                 "equations do not form AC_C-theory\n" .
                                xa)))
                        (\ _ ->
                          Error_Monad.bind
                            (Error_Monad.catch_error
                              (Check_Monad.check_subseteq (Trs.funs_trs_list e)
                                (a ++ c))
                              (\ xa ->
                                Sum_Type.Inl
                                  ((Shows_Literal.showsl_lit
                                      "equations contain symbol " .
                                     Shows_Literal.showsl xa) .
                                    Shows_Literal.showsl_lit
                                      " which is not AC-symbol")))
                            (\ _ ->
                              Error_Monad.bind
                                (Error_Monad.catch_error
                                  (AC_Rewriting_Impl.check_AC_same_as_E x y z a
                                    c e)
                                  (\ xa ->
                                    Sum_Type.Inl
                                      (Shows_Literal.showsl_lit
 "could not ensure that equations correspond to AC equivalence\n" .
xa)))
                                (\ _ ->
                                  Error_Monad.bind
                                    (Error_Monad.catch_error
                                      (Check_Monad.check_subseteq
(DP_Transformation_Impl.dP_list shp r d) dpr)
                                      (\ xa ->
Sum_Type.Inl
  (Shows_Literal.showsl_lit "could not find DP for R: " .
    Trs_Impl.showsl_rule xa)))
                                    (\ _ ->
                                      Error_Monad.bind
(Error_Monad.catch_error
  (Check_Monad.check_subseteq (DP_Transformation_Impl.dP_list shp e d) dpe)
  (\ xa ->
    Sum_Type.Inl
      (Shows_Literal.showsl_lit "could not find DP for E: " .
        Trs_Impl.showsl_rule xa)))
(\ _ ->
  Error_Monad.catch_error (AC_Rewriting_Impl.check_ext_trs r a c rext)
    (\ xa ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "could not ensure validity of extended TRS R_ext\n" .
          xa)))))))))))
    (\ xa ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit "problem in applying AC-dependency pairs\n" .
          xa));

ac_dependency_pairs_proc ::
  forall a b c d.
    (Collection_Enum.Cenum b, Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Eq b, Set_Impl.Set_impl b, Shows_Literal.Showl b, Collection_Eq.Ceq c,
      Collection_Order.Ccompare c, Eq c, Mapping_Impl.Mapping_impl c,
      Set_Impl.Set_impl c,
      Shows_Literal.Showl c) => AC_Termination_Problem_Spec.Ac_tp_ops_ext a b c
                                  () ->
                                  AC_Dependency_Pair_Problem_Spec.Ac_dpp_ops_ext
                                    d b c () ->
                                    (b -> b) ->
                                      c ->
c -> c -> Ac_dependency_pairs_proof b c ->
            a -> Sum_Type.Sum (String -> String) (d, d);
ac_dependency_pairs_proc i j shp x y z
  (AC_dependency_pairs_proof e dpr dpe rext) tp =
  Error_Monad.bind
    (ac_dependency_pairs_checks i shp x y z
      (AC_dependency_pairs_proof e dpr dpe rext) tp)
    (\ _ ->
      let {
        r = AC_Termination_Problem_Spec.r i tp;
      } in Sum_Type.Inr
             (AC_Dependency_Pair_Problem_Spec.mk j dpr dpe [] r e,
               AC_Dependency_Pair_Problem_Spec.mk j
                 (map (\ (l, ra) ->
                        (Sharp_Syntax.sharp_term shp l,
                          Sharp_Syntax.sharp_term shp ra))
                   rext)
                 dpe [] r e));

ac_dependency_pairs_proc_simple ::
  forall a b c d.
    (Collection_Enum.Cenum b, Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Eq b, Set_Impl.Set_impl b, Shows_Literal.Showl b, Collection_Eq.Ceq c,
      Collection_Order.Ccompare c, Eq c, Mapping_Impl.Mapping_impl c,
      Set_Impl.Set_impl c,
      Shows_Literal.Showl c) => AC_Termination_Problem_Spec.Ac_tp_ops_ext a b c
                                  () ->
                                  AC_Dependency_Pair_Problem_Spec.Ac_dpp_ops_ext
                                    d b c () ->
                                    (b -> b) ->
                                      c ->
c -> c -> Ac_dependency_pairs_proof b c ->
            a -> Sum_Type.Sum (String -> String) d;
ac_dependency_pairs_proc_simple i j shp x y z
  (AC_dependency_pairs_proof e dpr dpe rext) tp =
  Error_Monad.bind
    (ac_dependency_pairs_checks i shp x y z
      (AC_dependency_pairs_proof e dpr dpe rext) tp)
    (\ _ ->
      let {
        r = AC_Termination_Problem_Spec.r i tp;
      } in Sum_Type.Inr
             (AC_Dependency_Pair_Problem_Spec.mk j
               (dpr ++
                 map (\ (l, ra) ->
                       (Sharp_Syntax.sharp_term shp l,
                         Sharp_Syntax.sharp_term shp ra))
                   rext)
               dpe [] r e));

}
