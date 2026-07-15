{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Lattices_Big(max) where {

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
import qualified Set_Impl;
import qualified Set;
import qualified Collection_Order;
import qualified Orderings;
import qualified Collection_Eq;
import qualified Lattices;

max ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Lattices.Lattice a,
      Orderings.Linorder a) => Set.Set a -> a;
max a = Set_Impl.set_fold1 Set_Impl.max_sls a;

}
