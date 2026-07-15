{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Show_Literal_Polynomial(showsl_monom, showsl_poly) where {

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
import qualified Shows_Literal;
import qualified Quasi_Order;
import qualified Arith;
import qualified Polynomials;

showsl_monom_list ::
  forall a.
    (Quasi_Order.Linorder a,
      Shows_Literal.Showl a) => [(a, Arith.Nat)] -> String -> String;
showsl_monom_list [(x, p)] =
  (if Arith.equal_nat p Arith.one_nat
    then Shows_Literal.showsl_lit "x" . Shows_Literal.showsl x
    else ((Shows_Literal.showsl_lit "x" . Shows_Literal.showsl x) .
           Shows_Literal.showsl_lit "^") .
           Shows_Literal.showsl_nat p);
showsl_monom_list ((x, p) : v : va) =
  ((if Arith.equal_nat p Arith.one_nat
     then Shows_Literal.showsl_lit "x" . Shows_Literal.showsl x
     else ((Shows_Literal.showsl_lit "x" . Shows_Literal.showsl x) .
            Shows_Literal.showsl_literal "^") .
            Shows_Literal.showsl_nat p) .
    Shows_Literal.showsl_literal "*") .
    showsl_monom_list (v : va);
showsl_monom_list [] = Shows_Literal.showsl_literal "1";

showsl_monom ::
  forall a.
    (Quasi_Order.Linorder a,
      Shows_Literal.Showl a) => Polynomials.Monom a -> String -> String;
showsl_monom xa = showsl_monom_list (Polynomials.rep_monom xa);

showsl_poly ::
  forall a b.
    (Eq a, Quasi_Order.Linorder a, Shows_Literal.Showl a, Arith.One b, Eq b,
      Shows_Literal.Showl b) => [(Polynomials.Monom a, b)] -> String -> String;
showsl_poly [] = Shows_Literal.showsl_lit "0";
showsl_poly ((m, c) : p) =
  (if c == Arith.one then showsl_monom m
    else (if m == Polynomials.one_monom then Shows_Literal.showsl c
           else (Shows_Literal.showsl c . Shows_Literal.showsl_lit "*") .
                  showsl_monom m)) .
    (if null p then id else Shows_Literal.showsl_lit " + " . showsl_poly p);

}
