{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module CSR_Standalone_DP_Checker(check_standalone_improved_csr_dp) where {

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
import qualified CSR_Conservative_Checker;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Dependency_Pair_Problem_Spec;
import qualified Termination_Problem_Spec;
import qualified CSR_Checker_Base;
import qualified Labelings;
import qualified Sum_Type;
import qualified Compare;
import qualified Countable;
import qualified Term_Rewriting;
import qualified Arith;

check_standalone_improved_csr_dp ::
  forall a b c.
    (Compare.Compare_order b, Countable.Countable b, Eq b,
      Term_Rewriting.Showl b) => Termination_Problem_Spec.Tp_ops_ext a
                                   (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                   () ->
                                   Dependency_Pair_Problem_Spec.Dpp_ops_ext c
                                     (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                     () ->
                                     (String -> String) ->
                                       Bool ->
 Labelings.Lab b [Arith.Nat] ->
   [((Labelings.Lab b [Arith.Nat], Arith.Nat), [Arith.Nat])] ->
     [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
        Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
       [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
          Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
         CSR_Checker_Base.Csr_dp_termination_proof b [Arith.Nat] [Arith.Char] ->
           Sum_Type.Sum (String -> String) ();
check_standalone_improved_csr_dp ia j i m u mu p r prf =
  Error_Monad.bind
    (Check_Monad.check m
      (Term_Rewriting.showsl_lit
        "standalone improved CSR-DPs require CSR minimality"))
    (\ _ ->
      Error_Monad.bind (Term_Rewriting.check_wf_trs r)
        (\ _ ->
          Error_Monad.bind
            (Error_Monad.catch_error
              (Error_Monad.forallM
                (\ (f, _) ->
                  Check_Monad.check
                    (not (CSR_Checker_Base.is_sharp_lab f) &&
                      not (Labelings.equal_lab f u))
                    (Term_Rewriting.showsl_lit
                      "standalone CSR rules define a marked or unhiding symbol"))
                (Term_Rewriting.defined_list r))
              (\ x -> Sum_Type.Inl (snd x)))
            (\ _ ->
              Error_Monad.bind
                (Check_Monad.check (not (CSR_Checker_Base.is_sharp_lab u))
                  (Term_Rewriting.showsl_lit
                    "unhiding symbol must not be sharp"))
                (\ _ ->
                  CSR_Conservative_Checker.check_improved_csr_dp_termination_proof
                    ia j u mu False i
                    (Dependency_Pair_Problem_Spec.mk j False False p [] [] [] r)
                    prf))));

}
