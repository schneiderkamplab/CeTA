{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Extended_Nat(Enat(..), one_enat, zero_enat, equal_enat, minus_enat)
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
import qualified Arith;

data Enat = Enat Arith.Nat | Infinity_enat;

one_enat :: Enat;
one_enat = Enat Arith.one_nat;

zero_enat :: Enat;
zero_enat = Enat Arith.zero_nat;

equal_enat :: Enat -> Enat -> Bool;
equal_enat (Enat nat) Infinity_enat = False;
equal_enat Infinity_enat (Enat nat) = False;
equal_enat (Enat nata) (Enat nat) = Arith.equal_nat nata nat;
equal_enat Infinity_enat Infinity_enat = True;

minus_enat :: Enat -> Enat -> Enat;
minus_enat (Enat a) (Enat b) = Enat (Arith.minus_nat a b);
minus_enat Infinity_enat n = Infinity_enat;
minus_enat (Enat a) Infinity_enat = zero_enat;

}
