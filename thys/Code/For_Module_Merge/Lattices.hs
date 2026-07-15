{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Lattices(Inf(..), Semilattice_inf, Semilattice_sup, Lattice, Sup(..))
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
import qualified Quasi_Order;
import qualified Orderings;

class Inf a where {
  inf :: a -> a -> a;
};

class (Inf a, Orderings.Order a) => Semilattice_inf a where {
};

class (Orderings.Order a,
        Quasi_Order.Quasi_semilattice_sup a) => Semilattice_sup a where {
};

class (Semilattice_inf a, Semilattice_sup a) => Lattice a where {
};

class Sup a where {
  sup :: a -> a -> a;
};

}
