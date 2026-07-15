{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Quasi_Order(Quasi_order, Weak_order, Quasi_order_sup, Quasi_semilattice_sup)
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
import qualified Lattices;
import qualified Orderings;

class (Orderings.Ord a) => Quasi_order a where {
};

class (Quasi_order a) => Weak_order a where {
};

class (Lattices.Sup a, Quasi_order a) => Quasi_order_sup a where {
};

class (Quasi_order_sup a) => Quasi_semilattice_sup a where {
};

}
