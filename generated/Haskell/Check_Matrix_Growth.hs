{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Check_Matrix_Growth(check_matrix_complexity) where {

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
import qualified Sturm_Theorem;
import qualified Matrix_Kernel;
import qualified HOL;
import qualified Polynomial;
import qualified Matrix;
import qualified Arith;
import qualified Term_Rewriting;

check_matrix_complexity ::
  Matrix.Mat Term_Rewriting.Real ->
    Polynomial.Poly Term_Rewriting.Real -> Arith.Nat -> Bool;
check_matrix_complexity a cp d =
  Arith.equal_nat (Sturm_Theorem.count_roots_above cp Term_Rewriting.one_real)
    Arith.zero_nat &&
    (if Term_Rewriting.equal_real (Polynomial.poly cp Term_Rewriting.one_real)
          Term_Rewriting.zero_real
      then let {
             ord = Polynomial.order Term_Rewriting.one_real cp;
           } in (if Arith.less_nat (Arith.plus_nat d Arith.one_nat) ord
                  then Arith.equal_nat
                         (Matrix_Kernel.kernel_dim
                           (Matrix.pow_mat
                             (Matrix.minus_mat a
                               (Matrix.one_mat (Matrix.dim_row a)))
                             (Arith.plus_nat d Arith.one_nat)))
                         ord
                  else True)
      else True);

}
