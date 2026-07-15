{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Jordan_Normal_Form_Complexity_Approximation(mat_estimate_complexity_jb)
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
import qualified Check_Matrix_Growth;
import qualified Perron_Frobenius_Aux;
import qualified Char_Poly;
import qualified Polynomial;
import qualified Shows_Literal_Matrix;
import qualified Ring_Hom_Matrix;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Matrix;
import qualified Complexity_Carrier;
import qualified Show_Real;
import qualified HOL;
import qualified Term_Rewriting;
import qualified Arith;

count_ones_check :: [Term_Rewriting.Real] -> Arith.Nat -> Bool;
count_ones_check diag d =
  all (\ a ->
        let {
          aa = Term_Rewriting.abs_real a;
        } in Term_Rewriting.less_eq_real aa Term_Rewriting.one_real &&
               (if Term_Rewriting.equal_real aa Term_Rewriting.one_real
                 then Arith.less_eq_nat
                        (Arith.size_list
                          (filter (Term_Rewriting.equal_real a) diag))
                        d
                 else True))
    diag;

complexity_via_perron_frobenius ::
  Arith.Nat ->
    Polynomial.Poly Term_Rewriting.Real ->
      Matrix.Mat Term_Rewriting.Real -> Bool;
complexity_via_perron_frobenius d cp a =
  Perron_Frobenius_Aux.nonneg_mat a &&
    Check_Matrix_Growth.check_matrix_complexity a cp
      (Arith.minus_nat d Arith.one_nat);

combined_growth_check_real_mat ::
  Arith.Nat ->
    Matrix.Mat Term_Rewriting.Real -> Sum_Type.Sum (String -> String) ();
combined_growth_check_real_mat d a =
  Error_Monad.catch_error
    (if Matrix.upper_triangular a && count_ones_check (Matrix.diag_mat a) d
      then Sum_Type.Inr ()
      else (if complexity_via_perron_frobenius d (Char_Poly.char_poly a) a
             then Sum_Type.Inr ()
             else Sum_Type.Inl
                    (if Perron_Frobenius_Aux.nonneg_mat a
                      then Term_Rewriting.showsl_lit
                             "matrix does not have intended growth rate"
                      else Term_Rewriting.showsl_lit
                             "only non-negative matrices supported")))
    (\ x ->
      Sum_Type.Inl
        (((((Term_Rewriting.showsl_lit "could not deduce that " .
              Shows_Literal_Matrix.showsl_mat a) .
             Term_Rewriting.showsl_literal " in O(n^") .
            Term_Rewriting.showsl_nat (Arith.minus_nat d Arith.one_nat)) .
           Term_Rewriting.showsl_lit ")\n") .
          x));

mat_estimate_complexity_jb ::
  forall a.
    (Complexity_Carrier.Large_real_ordered_semiring_1 a) => Arith.Nat ->
                      Matrix.Mat a -> Sum_Type.Sum (String -> String) ();
mat_estimate_complexity_jb d a =
  let {
    b = Matrix.map_mat Ring_Hom_Matrix.real_of a;
  } in Error_Monad.bind
         (Check_Monad.check
           (Arith.equal_nat (Matrix.dim_row a) (Matrix.dim_col a))
           (Term_Rewriting.showsl_lit "expected square matrix but got \n" .
             Shows_Literal_Matrix.showsl_mat b))
         (\ _ -> combined_growth_check_real_mat d b);

}
