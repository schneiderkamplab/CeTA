{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  String_Reversal_Impl(string_reversal_tt, string_reversal_complete_tt,
                        string_reversal_complete_rel_tt)
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
import qualified Check_Monad;
import qualified Arith;
import qualified Error_Monad;
import qualified String_Reversal;
import qualified Defaults;
import qualified HOL;
import qualified Termination_Problem_Spec;
import qualified Sum_Type;
import qualified Term_Rewriting;

check_unary_signature ::
  forall a b.
    (Term_Rewriting.Showl a,
      Term_Rewriting.Showl b) => [(Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b)] ->
                                   Sum_Type.Sum (String -> String) ();
check_unary_signature r =
  Error_Monad.catch_error
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ x ->
          (if (case x of {
                (l, ra) ->
                  String_Reversal.unary_term l && String_Reversal.unary_term ra;
              })
            then Sum_Type.Inr () else Sum_Type.Inl x))
        r)
      (\ x -> Sum_Type.Inl (snd x)))
    (\ x ->
      Sum_Type.Inl
        ((Term_Rewriting.showsl_lit "the rule\n" .
           Term_Rewriting.showsl_rule x) .
          Term_Rewriting.showsl_lit
            "\nviolates the condition that all function symbols\nhave to be unary"));

string_reversal_tt ::
  forall a b c.
    (Term_Rewriting.Showl b,
      Term_Rewriting.Showl c) => Termination_Problem_Spec.Tp_ops_ext a b c () ->
                                   a -> Sum_Type.Sum (String -> String) a;
string_reversal_tt i trs =
  let {
    rs = Termination_Problem_Spec.rules i trs;
    r = Termination_Problem_Spec.r i trs;
    s = Termination_Problem_Spec.rw i trs;
  } in (case check_unary_signature rs of {
         Sum_Type.Inl a -> Sum_Type.Inl a;
         Sum_Type.Inr _ ->
           Sum_Type.Inr
             (Termination_Problem_Spec.mk i Defaults.default_nfs_trs []
               (map String_Reversal.rev_rule r)
               (map String_Reversal.rev_rule s));
       });

string_reversal_complete_tt ::
  forall a b c d.
    (Term_Rewriting.Showl b,
      Term_Rewriting.Showl c) => Termination_Problem_Spec.Tp_ops_ext a b c d ->
                                   a -> Sum_Type.Sum (String -> String) a;
string_reversal_complete_tt i tp =
  let {
    r = Termination_Problem_Spec.rules i tp;
  } in Error_Monad.bind
         (Check_Monad.check (Termination_Problem_Spec.q_empty i tp)
           (Term_Rewriting.showsl_lit "Q is not empty"))
         (\ _ ->
           Error_Monad.bind (check_unary_signature r)
             (\ _ ->
               Sum_Type.Inr
                 (Termination_Problem_Spec.mk i Defaults.default_nfs_nt_trs []
                   (map String_Reversal.rev_rule r) [])));

string_reversal_complete_rel_tt ::
  forall a b c d.
    (Term_Rewriting.Showl b,
      Term_Rewriting.Showl c) => Termination_Problem_Spec.Tp_ops_ext a b c d ->
                                   a -> Sum_Type.Sum (String -> String) a;
string_reversal_complete_rel_tt i tp =
  Error_Monad.bind
    (Check_Monad.check (Termination_Problem_Spec.q_empty i tp)
      (Term_Rewriting.showsl_lit "Q is not empty"))
    (\ _ ->
      Error_Monad.bind
        (check_unary_signature (Termination_Problem_Spec.rules i tp))
        (\ _ ->
          Sum_Type.Inr
            (Termination_Problem_Spec.mk i Defaults.default_nfs_nt_trs []
              (map String_Reversal.rev_rule (Termination_Problem_Spec.r i tp))
              (map String_Reversal.rev_rule
                (Termination_Problem_Spec.rw i tp)))));

}
