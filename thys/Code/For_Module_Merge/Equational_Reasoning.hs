{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Equational_Reasoning(Eq_proof(..)) where {

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
import qualified Term;

data Eq_proof a b = Refl (Term.Term a b) | Sym (Eq_proof a b)
  | Trans (Eq_proof a b) (Eq_proof a b)
  | Assm (Term.Term a b, Term.Term a b) (b -> Term.Term a b)
  | Cong a [Eq_proof a b];

}
