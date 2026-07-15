{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Nontermination_Impl(Q_increase_nonterm_dp_prf(..),
                       Q_increase_nonterm_trs_prf(..),
                       Rule_removal_nonterm_dp_prf(..),
                       Rule_removal_nonterm_trs_prf(..),
                       Dp_trans_nontermination_tt_prf(..),
                       Rule_removal_nonterm_reltrs_prf(..), reltrs_as_trs,
                       check_not_wwf_qtrs, check_not_wf_reltrs,
                       q_increase_nonterm_dp, q_increase_nonterm_trs,
                       rule_removal_nonterm_dp, rule_removal_nonterm_trs,
                       dp_trans_nontermination_tt, rule_removal_nonterm_reltrs)
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
import qualified Labelings_Impl;
import qualified Missing_List;
import qualified Dependency_Pair_Problem_Spec;
import qualified Q_Restricted_Rewriting_Impl;
import qualified Check_Monad;
import qualified Compare;
import qualified Termination_Problem_Spec;
import qualified Sharp_Syntax;
import qualified Error_Monad;
import qualified HOL;
import qualified Sum_Type;
import qualified Shows_Literal;
import qualified Arith;
import qualified Labelings;
import qualified Term_Rewriting;

newtype Q_increase_nonterm_dp_prf a b = Q_increase_nonterm_dp_prf
  [Term_Rewriting.Term a b];

newtype Q_increase_nonterm_trs_prf a b = Q_increase_nonterm_trs_prf
  [Term_Rewriting.Term a b];

data Rule_removal_nonterm_dp_prf a b =
  Rule_removal_nonterm_dp_prf
    [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]
    [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];

newtype Rule_removal_nonterm_trs_prf a b = Rule_removal_nonterm_trs_prf
  [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];

newtype Dp_trans_nontermination_tt_prf a b c = DP_trans_nontermination_tt_prf
  [(Term_Rewriting.Term (Labelings.Lab a b) c,
     Term_Rewriting.Term (Labelings.Lab a b) c)];

data Rule_removal_nonterm_reltrs_prf a b =
  Rule_removal_nonterm_reltrs_prf
    [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]
    [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];

unsharp :: forall a b. Labelings.Lab a b -> Labelings.Lab a b;
unsharp (Labelings.Sharp f) = f;
unsharp (Labelings.Lab v va) = Labelings.Lab v va;
unsharp (Labelings.FunLab v va) = Labelings.FunLab v va;
unsharp (Labelings.UnLab v) = Labelings.UnLab v;

check_dps ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => (a -> a) ->
                                  [(Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b)] ->
                                    [(Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b)] ->
                                      Sum_Type.Sum
(Term_Rewriting.Term a b, Term_Rewriting.Term a b) ();
check_dps unshp r p =
  let {
    d = Term_Rewriting.defined_list r;
  } in Error_Monad.catch_error
         (Error_Monad.forallM
           (\ x ->
             (if (case x of {
                   (ll, rr) ->
                     not (Term_Rewriting.is_Var rr) &&
                       not (Arith.membera d
                             (Arith.the (Term_Rewriting.root rr))) &&
                         any (\ (l, ra) ->
                               Term_Rewriting.equal_term l
                                 (Sharp_Syntax.sharp_term unshp ll) &&
                                 (Term_Rewriting.equal_term ra
                                    (Sharp_Syntax.sharp_term unshp rr) ||
                                   Term_Rewriting.supt_impl ra
                                     (Sharp_Syntax.sharp_term unshp rr)))
                           r;
                 })
               then Sum_Type.Inr () else Sum_Type.Inl x))
           p)
         (\ x -> Sum_Type.Inl (snd x));

reltrs_as_trs ::
  forall a b c.
    Termination_Problem_Spec.Tp_ops_ext a b c () ->
      a -> Sum_Type.Sum (String -> String) a;
reltrs_as_trs i tp = let {
                       q = Termination_Problem_Spec.q i tp;
                       r = Termination_Problem_Spec.r i tp;
                       nfs = Termination_Problem_Spec.nfs i tp;
                       a = Termination_Problem_Spec.mk i nfs q r [];
                     } in Sum_Type.Inr a;

check_not_wwf_qtrs ::
  forall a b c.
    (Compare.Compare_order b, Shows_Literal.Showl b, Compare.Compare_order c,
      Eq c,
      Shows_Literal.Showl c) => Termination_Problem_Spec.Tp_ops_ext a b c () ->
                                  a -> Sum_Type.Sum (String -> String) ();
check_not_wwf_qtrs i tp =
  Error_Monad.bind
    (Check_Monad.check
      (null (Termination_Problem_Spec.q i tp) ||
        not (Termination_Problem_Spec.nfs i tp))
      (Shows_Literal.showsl_lit
        "strategies and normal form substitutions problem"))
    (\ _ ->
      Check_Monad.check
        (not (Error_Monad.isOK
               (Q_Restricted_Rewriting_Impl.check_wwf_qtrs
                 (Termination_Problem_Spec.is_QNF i tp)
                 (Termination_Problem_Spec.rules i tp))))
        (Shows_Literal.showsl_lit "The Q-TRS is well formed" .
          Shows_Literal.showsl_literal "\n"));

check_not_wf_reltrs ::
  forall a b c.
    (Compare.Compare_order b, Shows_Literal.Showl b, Compare.Compare_order c,
      Eq c,
      Shows_Literal.Showl c) => Termination_Problem_Spec.Tp_ops_ext a b c () ->
                                  a -> Sum_Type.Sum (String -> String) ();
check_not_wf_reltrs i tp =
  Error_Monad.bind
    (Check_Monad.check (Termination_Problem_Spec.q_empty i tp)
      (Shows_Literal.showsl_lit "currently only empty Q is supported"))
    (\ _ ->
      Check_Monad.check
        (not (Error_Monad.isOK
               (Term_Rewriting.check_wf_reltrs
                 (Termination_Problem_Spec.r i tp,
                   Termination_Problem_Spec.rw i tp))))
        (Shows_Literal.showsl_lit "The TRSs R and S are well formed" .
          Shows_Literal.showsl_literal "\n"));

q_increase_nonterm_dp ::
  forall a b c.
    (Eq b,
      Eq c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b c () ->
                 a -> Q_increase_nonterm_dp_prf b c ->
                        Sum_Type.Sum (String -> String) a;
q_increase_nonterm_dp i dpp (Q_increase_nonterm_dp_prf q) =
  let {
    p = Dependency_Pair_Problem_Spec.pairs i dpp;
    r = Dependency_Pair_Problem_Spec.rules i dpp;
    qa = Dependency_Pair_Problem_Spec.q i dpp;
    nfs = Dependency_Pair_Problem_Spec.nfs i dpp;
  } in Sum_Type.Inr
         (Dependency_Pair_Problem_Spec.mk i nfs False p []
           (Missing_List.list_union qa q) [] r);

q_increase_nonterm_trs ::
  forall a b c.
    (Compare.Compare_order b, Eq b, Shows_Literal.Showl b,
      Compare.Compare_order c, Eq c,
      Shows_Literal.Showl c) => Termination_Problem_Spec.Tp_ops_ext a b c () ->
                                  a -> Q_increase_nonterm_trs_prf b c ->
 Sum_Type.Sum (String -> String) a;
q_increase_nonterm_trs i dpp (Q_increase_nonterm_trs_prf q) =
  let {
    r = Termination_Problem_Spec.rules i dpp;
    qa = Termination_Problem_Spec.q i dpp;
    nfs = Termination_Problem_Spec.nfs i dpp;
  } in Sum_Type.Inr
         (Termination_Problem_Spec.mk i nfs (Missing_List.list_union qa q) r
           []);

rule_removal_nonterm_dp ::
  forall a b c.
    (Compare.Compare_order b, Shows_Literal.Showl b, Compare.Compare_order c,
      Shows_Literal.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b c
                                  () ->
                                  a -> Rule_removal_nonterm_dp_prf b c ->
 Sum_Type.Sum (String -> String) a;
rule_removal_nonterm_dp i dpp (Rule_removal_nonterm_dp_prf prm rrm) =
  Sum_Type.Inr
    (Dependency_Pair_Problem_Spec.delete_R_Rw i
      (Dependency_Pair_Problem_Spec.delete_P_Pw i dpp prm prm) rrm rrm);

rule_removal_nonterm_trs ::
  forall a b c.
    (Compare.Compare_order b, Shows_Literal.Showl b, Compare.Compare_order c,
      Shows_Literal.Showl c) => Termination_Problem_Spec.Tp_ops_ext a b c () ->
                                  a -> Rule_removal_nonterm_trs_prf b c ->
 Sum_Type.Sum (String -> String) a;
rule_removal_nonterm_trs i tp (Rule_removal_nonterm_trs_prf rrm) =
  Sum_Type.Inr (Termination_Problem_Spec.delete_R_Rw i tp rrm rrm);

dp_trans_nontermination_tt ::
  forall a b c d e f g.
    (Eq b, Shows_Literal.Showl b, Eq c, Shows_Literal.Showl c, Eq d,
      Shows_Literal.Showl d) => Termination_Problem_Spec.Tp_ops_ext a
                                  (Labelings.Lab b c) d e ->
                                  Dependency_Pair_Problem_Spec.Dpp_ops_ext f
                                    (Labelings.Lab b c) d g ->
                                    a -> Dp_trans_nontermination_tt_prf b c d ->
   Sum_Type.Sum (String -> String) f;
dp_trans_nontermination_tt i j tp (DP_trans_nontermination_tt_prf p) =
  let {
    r = Termination_Problem_Spec.rules i tp;
    q = Termination_Problem_Spec.q i tp;
  } in Error_Monad.bind
         (Check_Monad.check (null q || not (Termination_Problem_Spec.nfs i tp))
           (Shows_Literal.showsl_lit
             "strategies and normal form substitutions problem"))
         (\ _ ->
           Error_Monad.bind
             (Error_Monad.catch_error (check_dps unsharp r p)
               (\ x ->
                 Sum_Type.Inl
                   (Shows_Literal.showsl_lit "problematic rule: " .
                     Term_Rewriting.showsl_rule x)))
             (\ _ ->
               Sum_Type.Inr
                 (Dependency_Pair_Problem_Spec.mk j False False p [] q [] r)));

rule_removal_nonterm_reltrs ::
  forall a b c.
    (Compare.Compare_order b, Shows_Literal.Showl b, Compare.Compare_order c,
      Shows_Literal.Showl c) => Termination_Problem_Spec.Tp_ops_ext a b c () ->
                                  a -> Rule_removal_nonterm_reltrs_prf b c ->
 Sum_Type.Sum (String -> String) a;
rule_removal_nonterm_reltrs i tp (Rule_removal_nonterm_reltrs_prf rrm srm) =
  Sum_Type.Inr (Termination_Problem_Spec.delete_R_Rw i tp rrm srm);

}
