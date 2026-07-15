{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Right_Ground_Termination_Impl(right_ground_tt, right_ground_nonterm)
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
import qualified Right_Ground_Termination;
import qualified Q_Restricted_Rewriting_Impl;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified HOL;
import qualified Termination_Problem_Spec;
import qualified Sum_Type;
import qualified Term_Rewriting;
import qualified Mapping;
import qualified Arith;
import qualified Shows_Literal;

check_right_ground ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => [(Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b)] ->
                                  Sum_Type.Sum (String -> String) ();
check_right_ground =
  (\ xs ->
    Error_Monad.catch_error
      (Error_Monad.forallM
        (\ (l, r) ->
          Check_Monad.check (Term_Rewriting.ground r)
            (Term_Rewriting.showsl_rule (l, r) .
              Shows_Literal.showsl_literal " is not right ground"))
        xs)
      (\ x -> Sum_Type.Inl (snd x)));

right_ground_tt ::
  forall a b c.
    (Eq b, Shows_Literal.Showl b, Arith.Ccompare c, Eq c,
      Mapping.Mapping_impl c,
      Shows_Literal.Showl c) => Termination_Problem_Spec.Tp_ops_ext a b c () ->
                                  a -> Sum_Type.Sum (String -> String) ();
right_ground_tt i tp =
  let {
    r = Termination_Problem_Spec.rules i tp;
    nfs = Termination_Problem_Spec.nfs i tp;
    qnf = Termination_Problem_Spec.is_QNF i tp;
  } in Error_Monad.bind (check_right_ground r)
         (\ _ ->
           Check_Monad.check
             (Right_Ground_Termination.right_ground_termination
               (Q_Restricted_Rewriting_Impl.qrewrite nfs qnf r) r)
             (Shows_Literal.showsl_literal "TRS is not terminating"));

right_ground_nonterm ::
  forall a b c.
    (Eq b, Shows_Literal.Showl b, Arith.Ccompare c, Eq c,
      Mapping.Mapping_impl c,
      Shows_Literal.Showl c) => Termination_Problem_Spec.Tp_ops_ext a b c () ->
                                  a -> Sum_Type.Sum (String -> String) ();
right_ground_nonterm i tp =
  let {
    r = Termination_Problem_Spec.rules i tp;
    nfs = Termination_Problem_Spec.nfs i tp;
    qnf = Termination_Problem_Spec.is_QNF i tp;
  } in Error_Monad.bind (check_right_ground r)
         (\ _ ->
           Check_Monad.check
             (not (Right_Ground_Termination.right_ground_termination
                    (Q_Restricted_Rewriting_Impl.qrewrite nfs qnf r) r))
             (Shows_Literal.showsl_literal "TRS is terminating"));

}
