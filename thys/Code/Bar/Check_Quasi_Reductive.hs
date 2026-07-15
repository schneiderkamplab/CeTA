{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Check_Quasi_Reductive(Quasi_reductive_proof(..), check_quasi_reductive_proof)
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
import qualified Unraveling_Impl;
import qualified FOR_Preliminaries;
import qualified Error_Monad;
import qualified HOL;
import qualified Dependency_Pair_Problem_Spec;
import qualified Termination_Problem_Spec;
import qualified Sum_Type;
import qualified Compare;
import qualified Countable;
import qualified Labelings_Impl;
import qualified Shows_Literal;
import qualified Arith;
import qualified Check_Termination;
import qualified Labelings;
import qualified Term_Rewriting;

data Quasi_reductive_proof a b c =
  Unravel
    [(((Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c),
        [(Term_Rewriting.Term (Labelings.Lab a b) c,
           Term_Rewriting.Term (Labelings.Lab a b) c)]),
       [(Term_Rewriting.Term (Labelings.Lab a b) c,
          Term_Rewriting.Term (Labelings.Lab a b) c)])]
    (Check_Termination.Trs_termination_proof a b c);

check_quasi_reductive_proof ::
  forall a b c.
    (Compare.Compare_order b, Countable.Countable b, Eq b,
      Shows_Literal.Showl b) => Bool ->
                                  (String -> String) ->
                                    Termination_Problem_Spec.Tp_ops_ext a
                                      (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                      () ->
                                      Dependency_Pair_Problem_Spec.Dpp_ops_ext c
(Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
[((Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
    Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char]),
   [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
      Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])])] ->
  Quasi_reductive_proof b [Arith.Nat] [Arith.Char] ->
    Sum_Type.Sum (String -> String) ();
check_quasi_reductive_proof a ia i j ctrs (Unravel u_info prf) =
  FOR_Preliminaries.debug ia "Unravel"
    (Error_Monad.bind
      (Error_Monad.catch_error (Unraveling_Impl.check_unraveling u_info ctrs)
        (\ x ->
          Sum_Type.Inl
            ((ia . Shows_Literal.showsl_lit ": error in unraveling\n") . x)))
      (\ r ->
        let {
          tp = Termination_Problem_Spec.mk i False [] r [];
        } in Error_Monad.catch_error
               (Check_Termination.check_trs_termination_proof i j a
                 (ia . Shows_Literal.showsl_lit ".1") tp prf)
               (\ x ->
                 Sum_Type.Inl
                   ((ia . Shows_Literal.showsl_lit
                            ": error below strong normalization + wcr\n") .
                     x))));

}
