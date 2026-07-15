{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Complexity(Complexity_class(..), Complexity_measure(..), get_signature_of_cm,
              less_eq_complexity_class, showsl_complexity_class)
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
import qualified Shows_Literal;
import qualified Arith;

newtype Complexity_class = Comp_Poly Arith.Nat;

data Complexity_measure a b = Derivational_Complexity [(a, Arith.Nat)]
  | Runtime_Complexity [(a, Arith.Nat)] [(a, Arith.Nat)];

degree :: Complexity_class -> Arith.Nat;
degree (Comp_Poly d) = d;

get_signature_of_cm :: forall a b. Complexity_measure a b -> [(a, Arith.Nat)];
get_signature_of_cm (Derivational_Complexity f) = f;
get_signature_of_cm (Runtime_Complexity c d) = c ++ d;

less_eq_complexity_class :: Complexity_class -> Complexity_class -> Bool;
less_eq_complexity_class x y = Arith.less_eq_nat (degree x) (degree y);

showsl_complexity_class :: Complexity_class -> String -> String;
showsl_complexity_class c =
  (if Arith.equal_nat (degree c) Arith.zero_nat
    then Shows_Literal.showsl_lit "O(1)"
    else (if Arith.equal_nat (degree c) Arith.one_nat
           then Shows_Literal.showsl_lit "O(n)"
           else (Shows_Literal.showsl_lit "O(n^" .
                  Shows_Literal.showsl_nat (degree c)) .
                  Shows_Literal.showsl_lit ")"));

}
