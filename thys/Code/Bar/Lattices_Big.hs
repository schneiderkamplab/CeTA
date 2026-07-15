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
import qualified Arith;
import qualified Quasi_Order;

max ::
  forall a.
    (Arith.Ceq a, Arith.Ccompare a, Quasi_Order.Lattice a,
      Quasi_Order.Linorder a) => Arith.Set a -> a;
max a = Arith.set_fold1 Arith.max_sls a;

}
