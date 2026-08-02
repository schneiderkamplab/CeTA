{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module CSR_Check_Loops(check_csr_loop) where {

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
import qualified Context_Sensitive_Impl;
import qualified Error_Monad;
import qualified HOL;
import qualified Forbidden_Pattern_Loops_Impl;
import qualified Loops_Impl;
import qualified Sum_Type;
import qualified Compare;
import qualified Mapping;
import qualified Term_Rewriting;
import qualified Arith;

check_funas_term ::
  forall a b.
    (Eq a) => [(a, Arith.Nat)] ->
                Term_Rewriting.Term a b -> Sum_Type.Sum (String -> String) ();
check_funas_term f t =
  Check_Monad.check (all (Arith.membera f) (Term_Rewriting.funas_term_list t))
    (Term_Rewriting.showsl_lit
      "loop term contains a symbol outside the input signature");

check_csr_loop ::
  forall a.
    (Compare.Compare a, Eq a,
      Term_Rewriting.Showl a) => [((a, Arith.Nat), [Arith.Nat])] ->
                                   [(Term_Rewriting.Term a [Arith.Char],
                                      Term_Rewriting.Term a [Arith.Char])] ->
                                     Loops_Impl.Trs_loop_prf a [Arith.Char] ->
                                       Sum_Type.Sum (String -> String) ();
check_csr_loop mu r prf =
  (case prf of {
    Loops_Impl.TRS_loop_prf s rseq sigma c ->
      Error_Monad.bind
        (Forbidden_Pattern_Loops_Impl.check_fploop r
          (Context_Sensitive_Impl.mu_to_fp_impl mu)
          (Forbidden_Pattern_Loops_Impl.FP_loop_prf c sigma s rseq))
        (\ _ ->
          let {
            f = Term_Rewriting.funas_trs_list r;
          } in Error_Monad.bind
                 (Error_Monad.catch_error
                   (Error_Monad.forallM (check_funas_term f)
                     (s : map (\ (_, (_, t)) -> t) rseq))
                   (\ x -> Sum_Type.Inl (snd x)))
                 (\ _ ->
                   Error_Monad.catch_error
                     (Error_Monad.forallM (\ (_, a) -> check_funas_term f a)
                       sigma)
                     (\ x -> Sum_Type.Inl (snd x))));
  });

}
