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
import qualified HOL;
import qualified Dependency_Pair_Problem_Spec;
import qualified Q_Restricted_Rewriting_Impl;
import qualified Innermost_Loops_Impl;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Mapping;
import qualified Compare;
import qualified Term_Rewriting;
import qualified Arith;

data Dp_loop_prf a b =
  DP_loop_prf (Term_Rewriting.Term a b)
    [([Arith.Nat],
       ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
         (Bool, Term_Rewriting.Term a b)))]
    [(b, Term_Rewriting.Term a b)]
    (Term_Rewriting.Actxt a (Term_Rewriting.Term a b));

data Trs_loop_prf a b =
  TRS_loop_prf (Term_Rewriting.Term a b)
    [([Arith.Nat],
       ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
         Term_Rewriting.Term a b))]
    [(b, Term_Rewriting.Term a b)]
    (Term_Rewriting.Actxt a (Term_Rewriting.Term a b));

data Rel_trs_loop_prf a b =
  Rel_trs_loop_prf (Term_Rewriting.Term a b)
    [([Arith.Nat],
       ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
         (Bool, Term_Rewriting.Term a b)))]
    [(b, Term_Rewriting.Term a b)]
    (Term_Rewriting.Actxt a (Term_Rewriting.Term a b));

check_loop ::
  forall a b.
    (Compare.Compare a, Eq a, Term_Rewriting.Showl a, Arith.Ceq b,
      Arith.Ccompare b, Compare.Compare b, Eq b, Mapping.Mapping_impl b,
      Arith.Set_impl b,
      Term_Rewriting.Showl b) => [Term_Rewriting.Term a b] ->
                                   Bool ->
                                     Term_Rewriting.Term a b ->
                                       [([Arith.Nat],
  ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
    Term_Rewriting.Term a b))] ->
 [(b, Term_Rewriting.Term a b)] ->
   Term_Rewriting.Actxt a (Term_Rewriting.Term a b) ->
     [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
       Sum_Type.Sum (String -> String) ();
check_loop q nfs s rseq sigma c r =
  Error_Monad.bind
    (Check_Monad.check (not (null rseq))
      (Term_Rewriting.showsl_lit "rewrite sequence must be non-empty"))
    (\ _ ->
      (if null q
        then Q_Restricted_Rewriting_Impl.check_qrsteps (\ _ -> True) nfs r rseq
               s (Term_Rewriting.intp_actxt Term_Rewriting.Fun c
                   (Term_Rewriting.eval_term Term_Rewriting.Fun s
                     (Term_Rewriting.mk_subst Term_Rewriting.Var sigma)))
        else Innermost_Loops_Impl.check_qrsteps_subst
               (Innermost_Loops_Impl.check_NF_iteration sigma q) nfs r rseq s
               (Term_Rewriting.intp_actxt Term_Rewriting.Fun c
                 (Term_Rewriting.eval_term Term_Rewriting.Fun s
                   (Term_Rewriting.mk_subst Term_Rewriting.Var sigma)))));

check_dp_loop ::
  forall a b c.
    (Compare.Compare b, Eq b, Term_Rewriting.Showl b, Arith.Ceq c,
      Arith.Ccompare c, Compare.Compare c, Eq c, Mapping.Mapping_impl c,
      Arith.Set_impl c,
      Term_Rewriting.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b c
                                   () ->
                                   a -> Dp_loop_prf b c ->
  Sum_Type.Sum (String -> String) ();
check_dp_loop i dpp (DP_loop_prf s prseq sigma c) =
  let {
    p = Dependency_Pair_Problem_Spec.pairs i dpp;
    r = Dependency_Pair_Problem_Spec.rules i dpp;
    nfs = Dependency_Pair_Problem_Spec.nfs i dpp;
    q = Dependency_Pair_Problem_Spec.q i dpp;
  } in (if Term_Rewriting.equal_actxt c Term_Rewriting.Hole
         then Error_Monad.bind
                (Check_Monad.check (not (null prseq))
                  (Term_Rewriting.showsl_lit
                    "rewrite sequence must be non-empty"))
                (\ _ ->
                  (if null q
                    then Q_Restricted_Rewriting_Impl.check_qsteps (\ _ -> True)
                           nfs p r prseq s
                           (Term_Rewriting.eval_term Term_Rewriting.Fun s
                             (Term_Rewriting.mk_subst Term_Rewriting.Var sigma))
                    else Innermost_Loops_Impl.check_qsteps_subst
                           (Innermost_Loops_Impl.check_NF_iteration sigma q) nfs
                           p r prseq s
                           (Term_Rewriting.eval_term Term_Rewriting.Fun s
                             (Term_Rewriting.mk_subst Term_Rewriting.Var
                               sigma))))
         else check_loop q nfs s (map (\ (x, (y, (_, z))) -> (x, (y, z))) prseq)
                sigma c r);

check_rel_seq ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Term_Rewriting.Showl b) => [(Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b)] ->
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)] ->
                                     [([Arith.Nat],
((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
  (Bool, Term_Rewriting.Term a b)))] ->
                                       Term_Rewriting.Term a b ->
 Term_Rewriting.Term a b -> Bool -> Sum_Type.Sum (String -> String) ();
check_rel_seq r sa [] s u True =
  Check_Monad.check (Term_Rewriting.equal_term s u)
    ((((Term_Rewriting.showsl_lit "the last term of the rewrite sequence\n" .
         Term_Rewriting.showsl_terma s) .
        Term_Rewriting.showsl_lit "\ndoes not correspond to the goal term\n") .
       Term_Rewriting.showsl_terma u) .
      Term_Rewriting.showsl_literal "\n");
check_rel_seq r sa [] s u False =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit "did not find strict step in rewrite sequence");
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
    (Eq a, Term_Rewriting.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Term_Rewriting.Showl b) => Term_Rewriting.Term a b ->
                                   [([Arith.Nat],
                                      ((Term_Rewriting.Term a b,
 Term_Rewriting.Term a b),
(Bool, Term_Rewriting.Term a b)))] ->
                                     [(b, Term_Rewriting.Term a b)] ->
                                       Term_Rewriting.Actxt a
 (Term_Rewriting.Term a b) ->
 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
   [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
     Sum_Type.Sum (String -> String) ();
check_rel_loop sa rseq sigma c r s =
  check_rel_seq r s rseq sa
    (Term_Rewriting.intp_actxt Term_Rewriting.Fun c
      (Term_Rewriting.eval_term Term_Rewriting.Fun sa
        (Term_Rewriting.mk_subst Term_Rewriting.Var sigma)))
    False;

check_trs_loop ::
  forall a b c.
    (Compare.Compare b, Eq b, Term_Rewriting.Showl b, Arith.Ceq c,
      Arith.Ccompare c, Compare.Compare c, Eq c, Mapping.Mapping_impl c,
      Arith.Set_impl c,
      Term_Rewriting.Showl c) => Termination_Problem_Spec.Tp_ops_ext a b c () ->
                                   a -> Trs_loop_prf b c ->
  Sum_Type.Sum (String -> String) ();
check_trs_loop i tp (TRS_loop_prf s rseq sigma c) =
  check_loop (Termination_Problem_Spec.q i tp)
    (Termination_Problem_Spec.nfs i tp) s rseq sigma c
    (Termination_Problem_Spec.rules i tp);

check_rel_trs_loop ::
  forall a b c.
    (Eq b, Term_Rewriting.Showl b, Arith.Ccompare c, Eq c,
      Mapping.Mapping_impl c,
      Term_Rewriting.Showl c) => Termination_Problem_Spec.Tp_ops_ext a b c () ->
                                   a -> Rel_trs_loop_prf b c ->
  Sum_Type.Sum (String -> String) ();
check_rel_trs_loop i tp (Rel_trs_loop_prf s rseq sigma c) =
  Error_Monad.bind
    (Check_Monad.check (Termination_Problem_Spec.q_empty i tp)
      (Term_Rewriting.showsl_lit "Q is not empty"))
    (\ _ ->
      check_rel_loop s rseq sigma c (Termination_Problem_Spec.r i tp)
        (Termination_Problem_Spec.rw i tp));

}
