{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Complexity_Framework_Impl(check_DP_complexity, split_proc_complexity)
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
import qualified Check_Monad;
import qualified Error_Monad;
import qualified HOL;
import qualified Complexity;
import qualified Sum_Type;
import qualified Shows_Literal;
import qualified Term_Rewriting;
import qualified Arith;

split_DP ::
  forall a b.
    (Arith.Ceq a,
      Arith.Ccompare a) => Arith.Set (a, Arith.Nat) ->
                             (Term_Rewriting.Term a b,
                               Term_Rewriting.Term a b) ->
                               (Term_Rewriting.Mctxt a b,
                                 [Term_Rewriting.Term a b]);
split_DP fs =
  (\ r ->
    Term_Rewriting.split_term
      (\ t ->
        not (Term_Rewriting.is_Var t) &&
          Arith.member (Arith.the (Term_Rewriting.root t)) fs)
      (snd r));

is_Fsharp_term ::
  forall a b.
    (Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a,
      Arith.Set_impl a) => Arith.Set (a, Arith.Nat) ->
                             Arith.Set (a, Arith.Nat) ->
                               Term_Rewriting.Term a b -> Bool;
is_Fsharp_term uu uv (Term_Rewriting.Var uw) = False;
is_Fsharp_term fs fa (Term_Rewriting.Fun f ts) =
  Arith.member (f, Arith.size_list ts) fs &&
    Arith.less_eq_set (Arith.set (concatMap Term_Rewriting.funas_term_list ts))
      fa;

check_DP_complexity ::
  forall a b.
    (Arith.Card_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Eq a, Arith.Set_impl a, Shows_Literal.Showl a,
      Shows_Literal.Showl b) => [(Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b)] ->
                                  Complexity.Complexity_measure a b ->
                                    Sum_Type.Sum (String -> String)
                                      ([(Term_Rewriting.Term a b,
  Term_Rewriting.Term a b)],
([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
  ([(a, Arith.Nat)], ([(a, Arith.Nat)], [(a, Arith.Nat)]))));
check_DP_complexity p (Complexity.Derivational_Complexity uu) =
  Sum_Type.Inl (Shows_Literal.showsl_lit "require runtime complexity");
check_DP_complexity p (Complexity.Runtime_Complexity c fs) =
  let {
    fsa = Arith.set fs;
  } in (case Arith.partition
               (\ lr ->
                 Arith.member (Arith.the (Term_Rewriting.root (fst lr))) fsa)
               p
         of {
         (rs, r) ->
           let {
             cs_ts = map (split_DP fsa) rs;
             cp = Arith.remdups
                    (concatMap (Term_Rewriting.funas_mctxt_list . fst) cs_ts);
             cpa = Arith.set cp;
             f = Arith.remdups
                   (c ++ Term_Rewriting.funas_trs_list r ++
                           concat
                             (concatMap
                               (\ (fsb, _) ->
                                 map Term_Rewriting.funas_term_list
                                   (Term_Rewriting.args fsb))
                               rs) ++
                             concat
                               (concatMap
                                 (\ (_, a) ->
                                   concatMap
                                     (\ t ->
                                       map Term_Rewriting.funas_term_list
 (Term_Rewriting.args t))
                                     a)
                                 cs_ts));
             fa = Arith.set f;
           } in Error_Monad.bind
                  (Check_Monad.check
                    (Arith.is_empty (Arith.inf_set fa fsa) &&
                      Arith.is_empty (Arith.inf_set fa cpa) &&
                        Arith.is_empty (Arith.inf_set fsa cpa))
                    (Shows_Literal.showsl_lit "symbols are not disjoint"))
                  (\ _ ->
                    Error_Monad.bind
                      (Check_Monad.check
                        (all (\ lr -> is_Fsharp_term fsa fa (fst lr)) rs)
                        (Shows_Literal.showsl_lit
                          "lhss of RS are not sharp terms"))
                      (\ _ -> Sum_Type.Inr (rs, (r, (cp, (fs, f))))));
       });

split_proc_complexity ::
  forall a b c.
    (Eq b, Shows_Literal.Showl b, Eq c,
      Shows_Literal.Showl c) => Termination_Problem_Spec.Tp_ops_ext a b c () ->
                                  [(Term_Rewriting.Term b c,
                                     Term_Rewriting.Term b c)] ->
                                    a -> Sum_Type.Sum (String -> String) (a, a);
split_proc_complexity i s1 cp =
  Error_Monad.catch_error
    (let {
       s = Termination_Problem_Spec.r i cp;
       w = Termination_Problem_Spec.rw i cp;
       nfs = Termination_Problem_Spec.nfs i cp;
       q = Termination_Problem_Spec.q i cp;
     } in Error_Monad.bind
            (Error_Monad.catch_error (Check_Monad.check_subseteq s1 s)
              (\ x ->
                Sum_Type.Inl
                  ((Shows_Literal.showsl_lit "rule " .
                     Term_Rewriting.showsl_rule x) .
                    Shows_Literal.showsl_lit " is not a strict rule")))
            (\ _ ->
              let {
                s2 = Missing_List.list_diff s s1;
              } in Sum_Type.Inr
                     (Termination_Problem_Spec.mk i nfs q s1 (s2 ++ w),
                       Termination_Problem_Spec.mk i nfs q s2 (s1 ++ w))))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit "error when splitting complexity problem\n" .
          x));

}
