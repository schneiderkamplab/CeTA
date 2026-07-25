{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  CSR_Conservative_Checker(Extended_csr_termination_proof(..),
                            check_extended_csr_termination_proof)
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
import qualified CSR_Improved_CSDP_Proofs;
import qualified CSR_Minimal_CSDP_Proofs;
import qualified FOR_Preliminaries;
import qualified Error_Monad;
import qualified Dependency_Pair_Problem_Spec;
import qualified Termination_Problem_Spec;
import qualified Sum_Type;
import qualified Arith;
import qualified Compare;
import qualified Countable;
import qualified CSR_Checker;
import qualified Labelings;
import qualified Term_Rewriting;

data Extended_csr_termination_proof a b c =
  Direct_CSR_Proof (CSR_Checker.Csr_termination_proof a b c)
  | Conservative_CSR_Dependency_Pairs (Labelings.Lab a b)
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (CSR_Checker.Csr_dp_termination_proof a b c);

check_extended_csr_termination_proof ::
  forall a b c.
    (Compare.Compare_order b, Countable.Countable b, Eq b,
      Term_Rewriting.Showl b) => Termination_Problem_Spec.Tp_ops_ext a
                                   (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                   () ->
                                   Dependency_Pair_Problem_Spec.Dpp_ops_ext c
                                     (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                     () ->
                                     Bool ->
                                       (String -> String) ->
 [((Labelings.Lab b [Arith.Nat], Arith.Nat), [Arith.Nat])] ->
   [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
      Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
     Extended_csr_termination_proof b [Arith.Nat] [Arith.Char] ->
       Sum_Type.Sum (String -> String) ();
check_extended_csr_termination_proof ia j a i mu r (Direct_CSR_Proof prf) =
  CSR_Minimal_CSDP_Proofs.check_csr_termination_proof_min ia j a i mu r prf;
check_extended_csr_termination_proof ia j a i mu r
  (Conservative_CSR_Dependency_Pairs u p s prf) =
  FOR_Preliminaries.debug i "conservative CSR dependency pairs"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (CSR_Improved_CSDP_Proofs.conservative_csr_dependency_pairs_tt j u mu r
          p s)
        (\ x ->
          Sum_Type.Inl
            ((i . Term_Rewriting.showsl_lit
                    ": invalid conservative CSR-DP transformation\n") .
              x)))
      (\ dpp ->
        Error_Monad.catch_error
          (CSR_Checker.check_csr_dp_termination_proof ia j False
            (Term_Rewriting.add_index i Arith.one_nat) dpp prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below conservative CSR dependency pairs\n") .
                x))));

}
