{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Polynomial_Factorial(gcd_poly) where {

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
import qualified HOL;
import qualified Polynomial;
import qualified Factorial_Ring;
import qualified Arith;

gcd_poly_code_aux ::
  forall a.
    (Factorial_Ring.Factorial_ring_gcd a,
      Eq a) => Polynomial.Poly a -> Polynomial.Poly a -> Polynomial.Poly a;
gcd_poly_code_aux p q =
  (if (case Polynomial.coeffs q of {
        [] -> True;
        _ : _ -> False;
      })
    then Polynomial.normalize_poly p
    else gcd_poly_code_aux q
           (Polynomial.primitive_part (Polynomial.pseudo_mod p q)));

gcd_poly_code ::
  forall a.
    (Factorial_Ring.Factorial_ring_gcd a,
      Eq a) => Polynomial.Poly a -> Polynomial.Poly a -> Polynomial.Poly a;
gcd_poly_code p q =
  (if (case Polynomial.coeffs p of {
        [] -> True;
        _ : _ -> False;
      })
    then Polynomial.normalize_poly q
    else (if (case Polynomial.coeffs q of {
               [] -> True;
               _ : _ -> False;
             })
           then Polynomial.normalize_poly p
           else let {
                  c1 = Polynomial.content p;
                  c2 = Polynomial.content q;
                  pa = Polynomial.map_poly (\ x -> Arith.divide x c1) p;
                  qa = Polynomial.map_poly (\ x -> Arith.divide x c2) q;
                } in Polynomial.smult (Arith.gcda c1 c2)
                       (gcd_poly_code_aux pa qa)));

gcd_poly ::
  forall a.
    (Factorial_Ring.Factorial_ring_gcd a, Arith.Semiring_gcd_mult_normalize a,
      Eq a) => Polynomial.Poly a -> Polynomial.Poly a -> Polynomial.Poly a;
gcd_poly p q = gcd_poly_code p q;

}
