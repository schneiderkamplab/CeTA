{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Cardinality(Finite_UNIV(..), Card_UNIV(..)) where {

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
import qualified Set;
import qualified Phantom_Type;
import qualified Arith;

finite_UNIV_nat :: Phantom_Type.Phantom Arith.Nat Bool;
finite_UNIV_nat = Phantom_Type.Phantom False;

card_UNIV_nat :: Phantom_Type.Phantom Arith.Nat Arith.Nat;
card_UNIV_nat = Phantom_Type.Phantom Arith.zero_nat;

class Finite_UNIV a where {
  finite_UNIV :: Phantom_Type.Phantom a Bool;
};

class (Finite_UNIV a) => Card_UNIV a where {
  card_UNIV :: Phantom_Type.Phantom a Arith.Nat;
};

instance Finite_UNIV Arith.Nat where {
  finite_UNIV = finite_UNIV_nat;
};

instance Card_UNIV Arith.Nat where {
  card_UNIV = card_UNIV_nat;
};

finite_UNIV_set ::
  forall a. (Finite_UNIV a) => Phantom_Type.Phantom (Set.Set a) Bool;
finite_UNIV_set =
  Phantom_Type.Phantom
    (Phantom_Type.of_phantom (finite_UNIV :: Phantom_Type.Phantom a Bool));

instance (Finite_UNIV a) => Finite_UNIV (Set.Set a) where {
  finite_UNIV = finite_UNIV_set;
};

finite_UNIV_list :: forall a. Phantom_Type.Phantom [a] Bool;
finite_UNIV_list = Phantom_Type.Phantom False;

card_UNIV_list :: forall a. Phantom_Type.Phantom [a] Arith.Nat;
card_UNIV_list = Phantom_Type.Phantom Arith.zero_nat;

instance Finite_UNIV [a] where {
  finite_UNIV = finite_UNIV_list;
};

instance Card_UNIV [a] where {
  card_UNIV = card_UNIV_list;
};

finite_UNIV_option ::
  forall a. (Finite_UNIV a) => Phantom_Type.Phantom (Maybe a) Bool;
finite_UNIV_option =
  Phantom_Type.Phantom
    (Phantom_Type.of_phantom (finite_UNIV :: Phantom_Type.Phantom a Bool));

instance (Finite_UNIV a) => Finite_UNIV (Maybe a) where {
  finite_UNIV = finite_UNIV_option;
};

finite_UNIV_prod ::
  forall a b.
    (Finite_UNIV a, Finite_UNIV b) => Phantom_Type.Phantom (a, b) Bool;
finite_UNIV_prod =
  Phantom_Type.Phantom
    (Phantom_Type.of_phantom (finite_UNIV :: Phantom_Type.Phantom a Bool) &&
      Phantom_Type.of_phantom (finite_UNIV :: Phantom_Type.Phantom b Bool));

card_UNIV_prod ::
  forall a b.
    (Card_UNIV a, Card_UNIV b) => Phantom_Type.Phantom (a, b) Arith.Nat;
card_UNIV_prod =
  Phantom_Type.Phantom
    (Arith.times_nat
      (Phantom_Type.of_phantom (card_UNIV :: Phantom_Type.Phantom a Arith.Nat))
      (Phantom_Type.of_phantom
        (card_UNIV :: Phantom_Type.Phantom b Arith.Nat)));

instance (Finite_UNIV a, Finite_UNIV b) => Finite_UNIV (a, b) where {
  finite_UNIV = finite_UNIV_prod;
};

instance (Card_UNIV a, Card_UNIV b) => Card_UNIV (a, b) where {
  card_UNIV = card_UNIV_prod;
};

finite_UNIV_integer :: Phantom_Type.Phantom Integer Bool;
finite_UNIV_integer = Phantom_Type.Phantom False;

card_UNIV_integer :: Phantom_Type.Phantom Integer Arith.Nat;
card_UNIV_integer = Phantom_Type.Phantom Arith.zero_nat;

instance Finite_UNIV Integer where {
  finite_UNIV = finite_UNIV_integer;
};

instance Card_UNIV Integer where {
  card_UNIV = card_UNIV_integer;
};

}
