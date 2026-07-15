{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Rewrite_Relations_Impl(WfTRS, is_mstep, is_par_rstep, mstep_rewrite,
                          parallel_rewrite, is_par_rstep_var_restr)
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
import qualified Cardinality;
import qualified Term_Impl;
import qualified HOL;
import qualified Term_More;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Shows_Literal;
import qualified Option;
import qualified Matching;
import qualified Product_Type;
import qualified Trs_Impl;
import qualified List;
import qualified Set;
import qualified Arith;
import qualified Mapping_Impl;
import qualified Compare;
import qualified Collection_Order;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Container_Setup;
import qualified Term;

newtype WfTRS b a = Abs_wfTRS [(Term.Term b a, Term.Term b a)];

err_wf :: String;
err_wf = "TRS is not well-formed";

rep_wfTRS :: forall b a. WfTRS b a -> [(Term.Term b a, Term.Term b a)];
rep_wfTRS (Abs_wfTRS x) = x;

get_TRS :: forall a b. WfTRS a b -> [(Term.Term a b, Term.Term a b)];
get_TRS x = rep_wfTRS x;

root_steps_substs ::
  forall a b.
    (Eq a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b) => [(Term.Term a b, Term.Term a b)] ->
Term.Term a b -> Term.Term a b -> [([Term.Term a b], [Term.Term a b])];
root_steps_substs r s t =
  concatMap
    (\ (l, ra) ->
      (case Matching.match s l of {
        Nothing -> [];
        Just sigma ->
          (case Matching.match t ra of {
            Nothing -> [];
            Just tau ->
              let {
                var_list =
                  filter (\ x -> Term_Impl.contains_var_term x ra)
                    (((reverse . List.remdups) . reverse)
                      (Term_More.vars_term_list l));
              } in [(map sigma var_list, map tau var_list)];
          });
      }))
    r;

is_mstep ::
  forall a b.
    (Compare.Compare a, Eq a, Collection_Order.Ccompare b, Compare.Compare b,
      Eq b,
      Mapping_Impl.Mapping_impl b) => [(Term.Term a b, Term.Term a b)] ->
Term.Term a b -> Term.Term a b -> Bool;
is_mstep r (Term.Fun f ss) (Term.Fun g ts) =
  Term.equal_term (Term.Fun f ss) (Term.Fun g ts) ||
    (Trs_Impl.is_root_step (List.set r) (Term.Fun f ss) (Term.Fun g ts) ||
      (any (\ (a, b) -> List.list_all2 (is_mstep r) a b)
         (root_steps_substs
           (filter (\ (l, ra) -> not (Term.is_Var l) || not (Term.is_Var ra)) r)
           (Term.Fun f ss) (Term.Fun g ts)) ||
        f == g &&
          Arith.equal_nat (List.size_list ss) (List.size_list ts) &&
            List.list_all2 (is_mstep r) ss ts));
is_mstep r (Term.Var v) t =
  Term.equal_term (Term.Var v) t ||
    (Trs_Impl.is_root_step (List.set r) (Term.Var v) t ||
      any (\ (a, b) -> List.list_all2 (is_mstep r) a b)
        (root_steps_substs
          (filter (\ (l, ra) -> not (Term.is_Var l) || not (Term.is_Var ra)) r)
          (Term.Var v) t));
is_mstep r s (Term.Var v) =
  Term.equal_term s (Term.Var v) ||
    (Trs_Impl.is_root_step (List.set r) s (Term.Var v) ||
      any (\ (a, b) -> List.list_all2 (is_mstep r) a b)
        (root_steps_substs
          (filter (\ (l, ra) -> not (Term.is_Var l) || not (Term.is_Var ra)) r)
          s (Term.Var v)));

is_par_rstep ::
  forall a b.
    (Compare.Compare a, Eq a, Collection_Order.Ccompare b, Compare.Compare b,
      Eq b,
      Mapping_Impl.Mapping_impl b) => [(Term.Term a b, Term.Term a b)] ->
Term.Term a b -> Term.Term a b -> Bool;
is_par_rstep r (Term.Fun f ss) (Term.Fun g ts) =
  Term.equal_term (Term.Fun f ss) (Term.Fun g ts) ||
    (Trs_Impl.is_root_step (List.set r) (Term.Fun f ss) (Term.Fun g ts) ||
      f == g &&
        Arith.equal_nat (List.size_list ss) (List.size_list ts) &&
          List.list_all2 (is_par_rstep r) ss ts);
is_par_rstep r (Term.Var v) t =
  Term.equal_term (Term.Var v) t ||
    Trs_Impl.is_root_step (List.set r) (Term.Var v) t;
is_par_rstep r s (Term.Var v) =
  Term.equal_term s (Term.Var v) ||
    Trs_Impl.is_root_step (List.set r) s (Term.Var v);

root_rewrite ::
  forall a b.
    (Eq a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b) => [(Term.Term a b, Term.Term a b)] ->
Term.Term a b -> [Term.Term a b];
root_rewrite r s =
  concatMap (\ (l, ra) -> (case Matching.match s l of {
                            Nothing -> [];
                            Just sigma -> [Term.eval_term Term.Fun ra sigma];
                          }))
    r;

get_wfTRS_sub ::
  forall a b.
    (Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => [(Term.Term a b, Term.Term a b)] -> WfTRS a b;
get_wfTRS_sub xa =
  Abs_wfTRS
    (if Error_Monad.isOK (Trs_Impl.check_wf_trs xa) then xa
      else (error :: forall a. String -> (() -> a) -> a) err_wf (\ _ -> []));

root_subst_with_rhs ::
  forall a b.
    (Eq a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b) => [(Term.Term a b, Term.Term a b)] ->
Term.Term a b -> [(Term.Term a b, [Term.Term a b])];
root_subst_with_rhs r s =
  concatMap
    (\ (l, ra) ->
      (case Matching.match s l of {
        Nothing -> [];
        Just sigma ->
          [(ra, map sigma
                  (((reverse . List.remdups) . reverse)
                    (Term_More.vars_term_list ra)))];
      }))
    r;

mstep_rewrite_wf ::
  forall a b.
    (Eq a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b) => WfTRS a b ->
Term.Term a b -> [Term.Term a b];
mstep_rewrite_wf r (Term.Var x) = [Term.Var x];
mstep_rewrite_wf r (Term.Fun f ss) =
  List.remdups
    (concatMap
       (\ (ra, ts) ->
         map (\ args ->
               Term.eval_term Term.Fun ra
                 (Term_More.mk_subst Term.Var
                   (zip (((reverse . List.remdups) . reverse)
                          (Term_More.vars_term_list ra))
                     args)))
           (List.product_lists (map (mstep_rewrite_wf r) ts)))
       (root_subst_with_rhs (get_TRS r) (Term.Fun f ss)) ++
      map (Term.Fun f) (List.product_lists (map (mstep_rewrite_wf r) ss)));

mstep_rewrite ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b,
      Shows_Literal.Showl b) => [(Term.Term a b, Term.Term a b)] ->
                                  Term.Term a b -> [Term.Term a b];
mstep_rewrite r = mstep_rewrite_wf (get_wfTRS_sub r);

parallel_rewrite ::
  forall a b.
    (Eq a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b) => [(Term.Term a b, Term.Term a b)] ->
Term.Term a b -> [Term.Term a b];
parallel_rewrite r (Term.Var x) = [Term.Var x];
parallel_rewrite r (Term.Fun f ss) =
  List.remdups
    (root_rewrite r (Term.Fun f ss) ++
      map (Term.Fun f) (List.product_lists (map (parallel_rewrite r) ss)));

is_par_rstep_var_restr ::
  forall a b.
    (Compare.Compare a, Eq a, Cardinality.Card_UNIV b, Collection_Eq.Ceq b,
      Collection_Order.Cproper_interval b, Compare.Compare b, Eq b,
      Mapping_Impl.Mapping_impl b,
      Set_Impl.Set_impl b) => [(Term.Term a b, Term.Term a b)] ->
                                Set.Set b ->
                                  Term.Term a b -> Term.Term a b -> Bool;
is_par_rstep_var_restr r v (Term.Fun f ss) (Term.Fun g ts) =
  Term.equal_term (Term.Fun f ss) (Term.Fun g ts) ||
    (Set.is_empty (Set.inf_set (Term.vars_term (Term.Fun g ts)) v) &&
       Trs_Impl.is_root_step (List.set r) (Term.Fun f ss) (Term.Fun g ts) ||
      f == g &&
        Arith.equal_nat (List.size_list ss) (List.size_list ts) &&
          List.list_all2 (is_par_rstep_var_restr r v) ss ts);
is_par_rstep_var_restr r va (Term.Var v) t =
  Term.equal_term (Term.Var v) t ||
    Set.is_empty (Set.inf_set (Term.vars_term t) va) &&
      Trs_Impl.is_root_step (List.set r) (Term.Var v) t;
is_par_rstep_var_restr r va s (Term.Var v) =
  Term.equal_term s (Term.Var v) ||
    Set.is_empty
      (Set.inf_set ((Term.vars_term :: Term.Term a b -> Set.Set b) (Term.Var v))
        va) &&
      Trs_Impl.is_root_step (List.set r) s (Term.Var v);

}
