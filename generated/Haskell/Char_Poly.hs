{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Char_Poly(char_poly) where {

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
import qualified Determinant;
import qualified Matrix;
import qualified Arith;
import qualified Polynomial;

char_poly_matrix ::
  forall a.
    (Eq a, Arith.Comm_ring_1 a,
      Arith.Semiring_no_zero_divisors a) => Matrix.Mat a ->
      Matrix.Mat (Polynomial.Poly a);
char_poly_matrix a =
  Matrix.plus_mat
    (Matrix.smult_mat
      (Polynomial.pCons Arith.zero
        (Polynomial.pCons Arith.one Polynomial.zero_poly))
      (Matrix.one_mat (Matrix.dim_row a)))
    (Matrix.map_mat
      (\ aa -> Polynomial.pCons (Arith.uminus aa) Polynomial.zero_poly) a);

char_poly ::
  forall a. (Eq a, Arith.Idom_divide a) => Matrix.Mat a -> Polynomial.Poly a;
char_poly a = Determinant.det (char_poly_matrix a);

}
