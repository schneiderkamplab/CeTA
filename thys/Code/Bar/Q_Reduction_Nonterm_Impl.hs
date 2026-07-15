{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Q_Reduction_Nonterm_Impl(Dp_q_reduction_nonterm_prf(..),
                            dp_q_reduction_nonterm)
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
import qualified Q_Restricted_Rewriting_Impl;
import qualified Error_Monad;
import qualified HOL;
import qualified Dependency_Pair_Problem_Spec;
import qualified Sum_Type;
import qualified Mapping;
import qualified Compare;
import qualified Shows_Literal;
import qualified Arith;
import qualified Term_Rewriting;

newtype Dp_q_reduction_nonterm_prf a b = DP_q_reduction_nonterm_prf
  [Term_Rewriting.Term a b];

dp_q_reduction_nonterm ::
  forall a b c d.
    (Arith.Cenum b, Arith.Ceq b, Arith.Ccompare b, Compare.Compare_order b,
      Eq b, Arith.Set_impl b, Shows_Literal.Showl b, Arith.Ccompare c, Eq c,
      Mapping.Mapping_impl c,
      Shows_Literal.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b c
                                  d ->
                                  a -> Dp_q_reduction_nonterm_prf b c ->
 Sum_Type.Sum (String -> String) a;
dp_q_reduction_nonterm i dpp (DP_q_reduction_nonterm_prf q) =
  let {
    p = Dependency_Pair_Problem_Spec.pairs i dpp;
    r = Dependency_Pair_Problem_Spec.rules i dpp;
    qa = Dependency_Pair_Problem_Spec.q i dpp;
    nfs = Dependency_Pair_Problem_Spec.nfs i dpp;
    f = Arith.set (Term_Rewriting.funas_trs_list (p ++ r));
    rQ = filter (\ qb -> Arith.less_eq_set (Term_Rewriting.funas_term qb) f) qa;
  } in Error_Monad.bind
         (Error_Monad.catch_error
           (Q_Restricted_Rewriting_Impl.check_NF_terms_subset
             (Term_Rewriting.is_NF_terms q) rQ)
           (\ x ->
             Sum_Type.Inl
               ((Shows_Literal.showsl_lit "the term " .
                  Term_Rewriting.showsl_terma x) .
                 Shows_Literal.showsl_lit " is missing in Q\' ")))
         (\ _ ->
           Sum_Type.Inr
             (Dependency_Pair_Problem_Spec.mk i nfs False p [] q [] r));

}
