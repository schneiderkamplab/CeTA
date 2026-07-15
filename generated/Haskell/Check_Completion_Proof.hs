{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Check_Completion_Proof(Completion_proof(..), Approx_completion_proof(..),
                          check_completion_proof, check_approx_completion_proof)
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
import qualified Equational_Reasoning_Impl;
import qualified Renaming2_String;
import qualified QDP_Framework_Impl;
import qualified FOR_Preliminaries;
import qualified Error_Monad;
import qualified HOL;
import qualified Dependency_Pair_Problem_Spec;
import qualified Termination_Problem_Spec;
import qualified Renaming2;
import qualified Sum_Type;
import qualified Countable;
import qualified Compare;
import qualified Mapping;
import qualified Lists_are_Infinite;
import qualified Arith;
import qualified Check_Termination;
import qualified Critical_Pairs_Impl;
import qualified Labelings;
import qualified Term_Rewriting;

data Completion_proof a b c =
  SN_WCR_Eq (Critical_Pairs_Impl.Join_info (Labelings.Lab a b) c)
    (Check_Termination.Trs_termination_proof a b c)
    [((Term_Rewriting.Term (Labelings.Lab a b) c,
        Term_Rewriting.Term (Labelings.Lab a b) c),
       [Term_Rewriting.Term (Labelings.Lab a b) c])]
    (Maybe [((Term_Rewriting.Term (Labelings.Lab a b) c,
               Term_Rewriting.Term (Labelings.Lab a b) c),
              [Term_Rewriting.Term (Labelings.Lab a b) c])]);

data Approx_completion_proof a b c =
  SN_WCR_Subsumption (Critical_Pairs_Impl.Join_info (Labelings.Lab a b) c)
    (Check_Termination.Trs_termination_proof a b c)
    (Maybe [((Term_Rewriting.Term (Labelings.Lab a b) c,
               Term_Rewriting.Term (Labelings.Lab a b) c),
              [Term_Rewriting.Term (Labelings.Lab a b) c])]);

check_completion_proof ::
  forall a b c.
    (Compare.Compare_order b, Countable.Countable b, Eq b,
      Term_Rewriting.Showl b) => Bool ->
                                   (String -> String) ->
                                     Termination_Problem_Spec.Tp_ops_ext a
                                       (Labelings.Lab b [Arith.Nat])
                                       [Arith.Char] () ->
                                       Dependency_Pair_Problem_Spec.Dpp_ops_ext
 c (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
 [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
    Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
   [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
      Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
     Completion_proof b [Arith.Nat] [Arith.Char] ->
       Sum_Type.Sum (String -> String) ();
check_completion_proof a ia i j e r (SN_WCR_Eq joins_i prf conv1 conv2) =
  FOR_Preliminaries.debug ia "SN_WCR_Eq"
    (let {
       tp = Termination_Problem_Spec.mk i False [] r [];
     } in Error_Monad.bind
            (Error_Monad.catch_error
              (Check_Termination.check_trs_termination_proof i j a
                (Term_Rewriting.add_index ia Arith.one_nat) tp prf)
              (\ x ->
                Sum_Type.Inl
                  ((ia . Term_Rewriting.showsl_lit
                           ": error below strong normalization + wcr\n") .
                    x)))
            (\ _ ->
              Error_Monad.bind
                (Error_Monad.catch_error
                  (Equational_Reasoning_Impl.check_subsumption_guided r e conv1)
                  (\ x ->
                    Sum_Type.Inl
                      ((ia . Term_Rewriting.showsl_lit
                               ": error when showing that rewrite relation can be simulated by equations\n") .
                        x)))
                (\ _ ->
                  Error_Monad.bind
                    (Error_Monad.catch_error
                      (Equational_Reasoning_Impl.check_subsumption e r conv2)
                      (\ x ->
                        Sum_Type.Inl
                          ((ia . Term_Rewriting.showsl_lit
                                   ": error when showing that equations can be simulated by rewrite system\n") .
                            x)))
                    (\ _ ->
                      Error_Monad.catch_error
                        (Critical_Pairs_Impl.check_critical_pairs r
                          (Critical_Pairs_Impl.critical_pairs_impl
                            Renaming2_String.string_rename r r)
                          joins_i)
                        (\ x ->
                          Sum_Type.Inl
                            ((((ia . Term_Rewriting.showsl_lit
                                       ": error when proving local confluence of \n") .
                                QDP_Framework_Impl.showsl_tp i tp) .
                               Term_Rewriting.showsl_literal "\n") .
                              x))))));

check_approx_completion_proof ::
  forall a b c.
    (Compare.Compare_order b, Countable.Countable b, Eq b,
      Term_Rewriting.Showl b) => Bool ->
                                   (String -> String) ->
                                     Termination_Problem_Spec.Tp_ops_ext a
                                       (Labelings.Lab b [Arith.Nat])
                                       [Arith.Char] () ->
                                       Dependency_Pair_Problem_Spec.Dpp_ops_ext
 c (Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
 [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
    Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
   [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
      Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
     Approx_completion_proof b [Arith.Nat] [Arith.Char] ->
       Sum_Type.Sum (String -> String) ();
check_approx_completion_proof a ia i j e r (SN_WCR_Subsumption joins_i prf conv)
  = FOR_Preliminaries.debug ia "SN_WCR_Subsumption"
      (let {
         tp = Termination_Problem_Spec.mk i False [] r [];
       } in Error_Monad.bind
              (Error_Monad.catch_error
                (Check_Termination.check_trs_termination_proof i j a
                  (Term_Rewriting.add_index ia Arith.one_nat) tp prf)
                (\ x ->
                  Sum_Type.Inl
                    ((ia . Term_Rewriting.showsl_lit
                             ": error below strong normalization + wcr\n") .
                      x)))
              (\ _ ->
                Error_Monad.bind
                  (Error_Monad.catch_error
                    (Equational_Reasoning_Impl.check_subsumption e r conv)
                    (\ x ->
                      Sum_Type.Inl
                        ((ia . Term_Rewriting.showsl_lit
                                 ": error when showing that equations can be simulated by rewrite system\n") .
                          x)))
                  (\ _ ->
                    Error_Monad.catch_error
                      (Critical_Pairs_Impl.check_critical_pairs r
                        (Critical_Pairs_Impl.critical_pairs_impl
                          Renaming2_String.string_rename r r)
                        joins_i)
                      (\ x ->
                        Sum_Type.Inl
                          ((((ia . Term_Rewriting.showsl_lit
                                     ": error when proving local confluence of \n") .
                              QDP_Framework_Impl.showsl_tp i tp) .
                             Term_Rewriting.showsl_literal "\n") .
                            x)))));

}
