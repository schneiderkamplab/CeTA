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
import qualified HOL;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Mapping;
import qualified Compare;
import qualified Arith;
import qualified Term_Rewriting;

newtype WfTRS b a = Abs_wfTRS
  [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)];

err_wf :: String;
err_wf = "TRS is not well-formed";

rep_wfTRS ::
  forall b a. WfTRS b a -> [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)];
rep_wfTRS (Abs_wfTRS x) = x;

get_TRS ::
  forall a b. WfTRS a b -> [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
get_TRS x = rep_wfTRS x;

root_steps_substs ::
  forall a b.
    (Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => [(Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b)] ->
                                   Term_Rewriting.Term a b ->
                                     Term_Rewriting.Term a b ->
                                       [([Term_Rewriting.Term a b],
  [Term_Rewriting.Term a b])];
root_steps_substs r s t =
  concatMap
    (\ (l, ra) ->
      (case Term_Rewriting.match s l of {
        Nothing -> [];
        Just sigma ->
          (case Term_Rewriting.match t ra of {
            Nothing -> [];
            Just tau ->
              let {
                var_list =
                  filter (\ x -> Term_Rewriting.contains_var_term x ra)
                    (((reverse . Arith.remdups) . reverse)
                      (Term_Rewriting.vars_term_list l));
              } in [(map sigma var_list, map tau var_list)];
          });
      }))
    r;

is_mstep ::
  forall a b.
    (Compare.Compare a, Eq a, Arith.Ccompare b, Compare.Compare b, Eq b,
      Mapping.Mapping_impl b) => [(Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b)] ->
                                   Term_Rewriting.Term a b ->
                                     Term_Rewriting.Term a b -> Bool;
is_mstep r (Term_Rewriting.Fun f ss) (Term_Rewriting.Fun g ts) =
  Term_Rewriting.equal_term (Term_Rewriting.Fun f ss)
    (Term_Rewriting.Fun g ts) ||
    (Term_Rewriting.is_root_step (Arith.set r) (Term_Rewriting.Fun f ss)
       (Term_Rewriting.Fun g ts) ||
      (any (\ (a, b) -> Arith.list_all2 (is_mstep r) a b)
         (root_steps_substs
           (filter
             (\ (l, ra) ->
               not (Term_Rewriting.is_Var l) || not (Term_Rewriting.is_Var ra))
             r)
           (Term_Rewriting.Fun f ss) (Term_Rewriting.Fun g ts)) ||
        f == g &&
          Arith.equal_nat (Arith.size_list ss) (Arith.size_list ts) &&
            Arith.list_all2 (is_mstep r) ss ts));
is_mstep r (Term_Rewriting.Var v) t =
  Term_Rewriting.equal_term (Term_Rewriting.Var v) t ||
    (Term_Rewriting.is_root_step (Arith.set r) (Term_Rewriting.Var v) t ||
      any (\ (a, b) -> Arith.list_all2 (is_mstep r) a b)
        (root_steps_substs
          (filter
            (\ (l, ra) ->
              not (Term_Rewriting.is_Var l) || not (Term_Rewriting.is_Var ra))
            r)
          (Term_Rewriting.Var v) t));
is_mstep r s (Term_Rewriting.Var v) =
  Term_Rewriting.equal_term s (Term_Rewriting.Var v) ||
    (Term_Rewriting.is_root_step (Arith.set r) s (Term_Rewriting.Var v) ||
      any (\ (a, b) -> Arith.list_all2 (is_mstep r) a b)
        (root_steps_substs
          (filter
            (\ (l, ra) ->
              not (Term_Rewriting.is_Var l) || not (Term_Rewriting.is_Var ra))
            r)
          s (Term_Rewriting.Var v)));

is_par_rstep ::
  forall a b.
    (Compare.Compare a, Eq a, Arith.Ccompare b, Compare.Compare b, Eq b,
      Mapping.Mapping_impl b) => [(Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b)] ->
                                   Term_Rewriting.Term a b ->
                                     Term_Rewriting.Term a b -> Bool;
is_par_rstep r (Term_Rewriting.Fun f ss) (Term_Rewriting.Fun g ts) =
  Term_Rewriting.equal_term (Term_Rewriting.Fun f ss)
    (Term_Rewriting.Fun g ts) ||
    (Term_Rewriting.is_root_step (Arith.set r) (Term_Rewriting.Fun f ss)
       (Term_Rewriting.Fun g ts) ||
      f == g &&
        Arith.equal_nat (Arith.size_list ss) (Arith.size_list ts) &&
          Arith.list_all2 (is_par_rstep r) ss ts);
is_par_rstep r (Term_Rewriting.Var v) t =
  Term_Rewriting.equal_term (Term_Rewriting.Var v) t ||
    Term_Rewriting.is_root_step (Arith.set r) (Term_Rewriting.Var v) t;
is_par_rstep r s (Term_Rewriting.Var v) =
  Term_Rewriting.equal_term s (Term_Rewriting.Var v) ||
    Term_Rewriting.is_root_step (Arith.set r) s (Term_Rewriting.Var v);

root_rewrite ::
  forall a b.
    (Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => [(Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b)] ->
                                   Term_Rewriting.Term a b ->
                                     [Term_Rewriting.Term a b];
root_rewrite r s =
  concatMap
    (\ (l, ra) ->
      (case Term_Rewriting.match s l of {
        Nothing -> [];
        Just sigma -> [Term_Rewriting.eval_term Term_Rewriting.Fun ra sigma];
      }))
    r;

get_wfTRS_sub ::
  forall a b.
    (Term_Rewriting.Showl a, Eq b,
      Term_Rewriting.Showl b) => [(Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b)] ->
                                   WfTRS a b;
get_wfTRS_sub xa =
  Abs_wfTRS
    (if Error_Monad.isOK (Term_Rewriting.check_wf_trs xa) then xa
      else (error :: forall a. String -> (() -> a) -> a) err_wf (\ _ -> []));

root_subst_with_rhs ::
  forall a b.
    (Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => [(Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b)] ->
                                   Term_Rewriting.Term a b ->
                                     [(Term_Rewriting.Term a b,
[Term_Rewriting.Term a b])];
root_subst_with_rhs r s =
  concatMap
    (\ (l, ra) ->
      (case Term_Rewriting.match s l of {
        Nothing -> [];
        Just sigma ->
          [(ra, map sigma
                  (((reverse . Arith.remdups) . reverse)
                    (Term_Rewriting.vars_term_list ra)))];
      }))
    r;

mstep_rewrite_wf ::
  forall a b.
    (Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => WfTRS a b ->
                                   Term_Rewriting.Term a b ->
                                     [Term_Rewriting.Term a b];
mstep_rewrite_wf r (Term_Rewriting.Var x) = [Term_Rewriting.Var x];
mstep_rewrite_wf r (Term_Rewriting.Fun f ss) =
  Arith.remdups
    (concatMap
       (\ (ra, ts) ->
         map (\ args ->
               Term_Rewriting.eval_term Term_Rewriting.Fun ra
                 (Term_Rewriting.mk_subst Term_Rewriting.Var
                   (zip (((reverse . Arith.remdups) . reverse)
                          (Term_Rewriting.vars_term_list ra))
                     args)))
           (Arith.product_lists (map (mstep_rewrite_wf r) ts)))
       (root_subst_with_rhs (get_TRS r) (Term_Rewriting.Fun f ss)) ++
      map (Term_Rewriting.Fun f)
        (Arith.product_lists (map (mstep_rewrite_wf r) ss)));

mstep_rewrite ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Term_Rewriting.Showl b) => [(Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b)] ->
                                   Term_Rewriting.Term a b ->
                                     [Term_Rewriting.Term a b];
mstep_rewrite r = mstep_rewrite_wf (get_wfTRS_sub r);

parallel_rewrite ::
  forall a b.
    (Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => [(Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b)] ->
                                   Term_Rewriting.Term a b ->
                                     [Term_Rewriting.Term a b];
parallel_rewrite r (Term_Rewriting.Var x) = [Term_Rewriting.Var x];
parallel_rewrite r (Term_Rewriting.Fun f ss) =
  Arith.remdups
    (root_rewrite r (Term_Rewriting.Fun f ss) ++
      map (Term_Rewriting.Fun f)
        (Arith.product_lists (map (parallel_rewrite r) ss)));

is_par_rstep_var_restr ::
  forall a b.
    (Compare.Compare a, Eq a, Arith.Card_UNIV b, Arith.Ceq b,
      Arith.Cproper_interval b, Compare.Compare b, Eq b, Mapping.Mapping_impl b,
      Arith.Set_impl b) => [(Term_Rewriting.Term a b,
                              Term_Rewriting.Term a b)] ->
                             Arith.Set b ->
                               Term_Rewriting.Term a b ->
                                 Term_Rewriting.Term a b -> Bool;
is_par_rstep_var_restr r v (Term_Rewriting.Fun f ss) (Term_Rewriting.Fun g ts) =
  Term_Rewriting.equal_term (Term_Rewriting.Fun f ss)
    (Term_Rewriting.Fun g ts) ||
    (Arith.is_empty
       (Arith.inf_set (Term_Rewriting.vars_term (Term_Rewriting.Fun g ts)) v) &&
       Term_Rewriting.is_root_step (Arith.set r) (Term_Rewriting.Fun f ss)
         (Term_Rewriting.Fun g ts) ||
      f == g &&
        Arith.equal_nat (Arith.size_list ss) (Arith.size_list ts) &&
          Arith.list_all2 (is_par_rstep_var_restr r v) ss ts);
is_par_rstep_var_restr r va (Term_Rewriting.Var v) t =
  Term_Rewriting.equal_term (Term_Rewriting.Var v) t ||
    Arith.is_empty (Arith.inf_set (Term_Rewriting.vars_term t) va) &&
      Term_Rewriting.is_root_step (Arith.set r) (Term_Rewriting.Var v) t;
is_par_rstep_var_restr r va s (Term_Rewriting.Var v) =
  Term_Rewriting.equal_term s (Term_Rewriting.Var v) ||
    Arith.is_empty
      (Arith.inf_set
        ((Term_Rewriting.vars_term :: Term_Rewriting.Term a b -> Arith.Set b)
          (Term_Rewriting.Var v))
        va) &&
      Term_Rewriting.is_root_step (Arith.set r) s (Term_Rewriting.Var v);

}
