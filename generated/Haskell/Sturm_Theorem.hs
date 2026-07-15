{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Sturm_Theorem(count_roots_above) where {

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
import qualified Polynomial_Factorial;
import qualified Field_as_Ring;
import qualified Misc_Polynomial;
import qualified Transcendental;
import qualified Arith;
import qualified Polynomial;
import qualified Term_Rewriting;

sturm_aux ::
  Polynomial.Poly Term_Rewriting.Real ->
    Polynomial.Poly Term_Rewriting.Real ->
      [Polynomial.Poly Term_Rewriting.Real];
sturm_aux p q =
  (if Arith.equal_nat (Polynomial.degree q) Arith.zero_nat then [p, q]
    else p : sturm_aux q (Polynomial.uminus_poly (Polynomial.modulo_poly p q)));

sturm ::
  Polynomial.Poly Term_Rewriting.Real -> [Polynomial.Poly Term_Rewriting.Real];
sturm p = sturm_aux p (Polynomial.pderiv p);

sign_changes ::
  [Polynomial.Poly Term_Rewriting.Real] -> Term_Rewriting.Real -> Arith.Nat;
sign_changes ps x =
  Arith.minus_nat
    (Arith.size_list
      (Arith.remdups_adj
        (filter
          (\ xa -> not (Term_Rewriting.equal_real xa Term_Rewriting.zero_real))
          (map (\ p -> Term_Rewriting.sgn_real (Polynomial.poly p x)) ps))))
    Arith.one_nat;

sign_changes_inf ::
  forall a.
    (Eq a,
      Transcendental.Real_normed_vector a) => [Polynomial.Poly a] -> Arith.Nat;
sign_changes_inf ps =
  Arith.minus_nat
    (Arith.size_list
      (Arith.remdups_adj
        (filter (\ x -> not (x == Arith.zero))
          (map Misc_Polynomial.poly_inf ps))))
    Arith.one_nat;

sturm_squarefree ::
  Polynomial.Poly Term_Rewriting.Real -> [Polynomial.Poly Term_Rewriting.Real];
sturm_squarefree p =
  sturm (Polynomial.div_field_poly_impl p
          (Polynomial_Factorial.gcd_poly p (Polynomial.pderiv p)));

count_roots_above ::
  Polynomial.Poly Term_Rewriting.Real -> Term_Rewriting.Real -> Arith.Nat;
count_roots_above p a =
  let {
    q = Polynomial.pderiv p;
  } in (if Polynomial.equal_poly p Polynomial.zero_poly then Arith.zero_nat
         else (if not (Term_Rewriting.equal_real (Polynomial.poly p a)
                        Term_Rewriting.zero_real) ||
                    not (Term_Rewriting.equal_real (Polynomial.poly q a)
                          Term_Rewriting.zero_real)
                then let {
                       ps = sturm p;
                     } in Arith.minus_nat (sign_changes ps a)
                            (sign_changes_inf ps)
                else let {
                       ps = sturm_squarefree p;
                     } in Arith.minus_nat (sign_changes ps a)
                            (sign_changes_inf ps)));

}
