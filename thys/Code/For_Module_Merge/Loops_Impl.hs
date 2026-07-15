{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Loops_Impl(Dp_loop_prf(..), Trs_loop_prf(..), Rel_trs_loop_prf(..),
              check_dp_loop, check_trs_loop, check_rel_trs_loop)
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
import qualified Termination_Problem_Spec;
import qualified Product_Type;
import qualified HOL;
import qualified Dependency_Pair_Problem_Spec;
import qualified Q_Restricted_Rewriting_Impl;
import qualified Innermost_Loops_Impl;
import qualified Term_More;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Mapping_Impl;
import qualified Collection_Order;
import qualified Shows_Literal;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Compare;
import qualified Subterm_and_Context;
import qualified Term;
import qualified Arith;

data Dp_loop_prf a b =
  DP_loop_prf (Term.Term a b)
    [([Arith.Nat], ((Term.Term a b, Term.Term a b), (Bool, Term.Term a b)))]
    [(b, Term.Term a b)] (Subterm_and_Context.Actxt a (Term.Term a b));

data Trs_loop_prf a b =
  TRS_loop_prf (Term.Term a b)
    [([Arith.Nat], ((Term.Term a b, Term.Term a b), Term.Term a b))]
    [(b, Term.Term a b)] (Subterm_and_Context.Actxt a (Term.Term a b));

data Rel_trs_loop_prf a b =
  Rel_trs_loop_prf (Term.Term a b)
    [([Arith.Nat], ((Term.Term a b, Term.Term a b), (Bool, Term.Term a b)))]
    [(b, Term.Term a b)] (Subterm_and_Context.Actxt a (Term.Term a b));

check_loop ::
  forall a b.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a, Collection_Eq.Ceq b,
      Collection_Order.Ccompare b, Compare.Compare b, Eq b,
      Mapping_Impl.Mapping_impl b, Set_Impl.Set_impl b,
      Shows_Literal.Showl b) => [Term.Term a b] ->
                                  Bool ->
                                    Term.Term a b ->
                                      [([Arith.Nat],
 ((Term.Term a b, Term.Term a b), Term.Term a b))] ->
[(b, Term.Term a b)] ->
  Subterm_and_Context.Actxt a (Term.Term a b) ->
    [(Term.Term a b, Term.Term a b)] -> Sum_Type.Sum (String -> String) ();
check_loop q nfs s rseq sigma c r =
  Error_Monad.bind
    (Check_Monad.check (not (null rseq))
      (Shows_Literal.showsl_lit "rewrite sequence must be non-empty"))
    (\ _ ->
      (if null q
        then Q_Restricted_Rewriting_Impl.check_qrsteps (\ _ -> True) nfs r rseq
               s (Subterm_and_Context.intp_actxt Term.Fun c
                   (Term.eval_term Term.Fun s
                     (Term_More.mk_subst Term.Var sigma)))
        else Innermost_Loops_Impl.check_qrsteps_subst
               (Innermost_Loops_Impl.check_NF_iteration sigma q) nfs r rseq s
               (Subterm_and_Context.intp_actxt Term.Fun c
                 (Term.eval_term Term.Fun s
                   (Term_More.mk_subst Term.Var sigma)))));

check_dp_loop ::
  forall a b c.
    (Compare.Compare b, Eq b, Shows_Literal.Showl b, Collection_Eq.Ceq c,
      Collection_Order.Ccompare c, Compare.Compare c, Eq c,
      Mapping_Impl.Mapping_impl c, Set_Impl.Set_impl c,
      Shows_Literal.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b c
                                  () ->
                                  a -> Dp_loop_prf b c ->
 Sum_Type.Sum (String -> String) ();
check_dp_loop i dpp (DP_loop_prf s prseq sigma c) =
  let {
    p = Dependency_Pair_Problem_Spec.pairs i dpp;
    r = Dependency_Pair_Problem_Spec.rules i dpp;
    nfs = Dependency_Pair_Problem_Spec.nfs i dpp;
    q = Dependency_Pair_Problem_Spec.q i dpp;
  } in (if Subterm_and_Context.equal_actxt c Subterm_and_Context.Hole
         then Error_Monad.bind
                (Check_Monad.check (not (null prseq))
                  (Shows_Literal.showsl_lit
                    "rewrite sequence must be non-empty"))
                (\ _ ->
                  (if null q
                    then Q_Restricted_Rewriting_Impl.check_qsteps (\ _ -> True)
                           nfs p r prseq s
                           (Term.eval_term Term.Fun s
                             (Term_More.mk_subst Term.Var sigma))
                    else Innermost_Loops_Impl.check_qsteps_subst
                           (Innermost_Loops_Impl.check_NF_iteration sigma q) nfs
                           p r prseq s
                           (Term.eval_term Term.Fun s
                             (Term_More.mk_subst Term.Var sigma))))
         else check_loop q nfs s (map (\ (x, (y, (_, z))) -> (x, (y, z))) prseq)
                sigma c r);

check_rel_seq ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b,
      Shows_Literal.Showl b) => [(Term.Term a b, Term.Term a b)] ->
                                  [(Term.Term a b, Term.Term a b)] ->
                                    [([Arith.Nat],
                                       ((Term.Term a b, Term.Term a b),
 (Bool, Term.Term a b)))] ->
                                      Term.Term a b ->
Term.Term a b -> Bool -> Sum_Type.Sum (String -> String) ();
check_rel_seq r sa [] s u True =
  Check_Monad.check (Term.equal_term s u)
    ((((Shows_Literal.showsl_lit "the last term of the rewrite sequence\n" .
         Term_More.showsl_terma s) .
        Shows_Literal.showsl_lit "\ndoes not correspond to the goal term\n") .
       Term_More.showsl_terma u) .
      Shows_Literal.showsl_literal "\n");
check_rel_seq r sa [] s u False =
  Sum_Type.Inl
    (Shows_Literal.showsl_lit "did not find strict step in rewrite sequence");
check_rel_seq ra sa ((p, (r, (True, t))) : prts) s u b =
  Error_Monad.bind
    (Q_Restricted_Rewriting_Impl.check_qrstep (\ _ -> True) False ra p r s t)
    (\ _ -> check_rel_seq ra sa prts t u True);
check_rel_seq ra sa ((p, (r, (False, t))) : prts) s u b =
  Error_Monad.bind
    (Q_Restricted_Rewriting_Impl.check_qrstep (\ _ -> True) False sa p r s t)
    (\ _ -> check_rel_seq ra sa prts t u b);

check_rel_loop ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b,
      Shows_Literal.Showl b) => Term.Term a b ->
                                  [([Arith.Nat],
                                     ((Term.Term a b, Term.Term a b),
                                       (Bool, Term.Term a b)))] ->
                                    [(b, Term.Term a b)] ->
                                      Subterm_and_Context.Actxt a
(Term.Term a b) ->
[(Term.Term a b, Term.Term a b)] ->
  [(Term.Term a b, Term.Term a b)] -> Sum_Type.Sum (String -> String) ();
check_rel_loop sa rseq sigma c r s =
  check_rel_seq r s rseq sa
    (Subterm_and_Context.intp_actxt Term.Fun c
      (Term.eval_term Term.Fun sa (Term_More.mk_subst Term.Var sigma)))
    False;

check_trs_loop ::
  forall a b c.
    (Compare.Compare b, Eq b, Shows_Literal.Showl b, Collection_Eq.Ceq c,
      Collection_Order.Ccompare c, Compare.Compare c, Eq c,
      Mapping_Impl.Mapping_impl c, Set_Impl.Set_impl c,
      Shows_Literal.Showl c) => Termination_Problem_Spec.Tp_ops_ext a b c () ->
                                  a -> Trs_loop_prf b c ->
 Sum_Type.Sum (String -> String) ();
check_trs_loop i tp (TRS_loop_prf s rseq sigma c) =
  check_loop (Termination_Problem_Spec.q i tp)
    (Termination_Problem_Spec.nfs i tp) s rseq sigma c
    (Termination_Problem_Spec.rules i tp);

check_rel_trs_loop ::
  forall a b c.
    (Eq b, Shows_Literal.Showl b, Collection_Order.Ccompare c, Eq c,
      Mapping_Impl.Mapping_impl c,
      Shows_Literal.Showl c) => Termination_Problem_Spec.Tp_ops_ext a b c () ->
                                  a -> Rel_trs_loop_prf b c ->
 Sum_Type.Sum (String -> String) ();
check_rel_trs_loop i tp (Rel_trs_loop_prf s rseq sigma c) =
  Error_Monad.bind
    (Check_Monad.check (Termination_Problem_Spec.q_empty i tp)
      (Shows_Literal.showsl_lit "Q is not empty"))
    (\ _ ->
      check_rel_loop s rseq sigma c (Termination_Problem_Spec.r i tp)
        (Termination_Problem_Spec.rw i tp));

}
