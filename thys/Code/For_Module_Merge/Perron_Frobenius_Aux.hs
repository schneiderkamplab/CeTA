{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Perron_Frobenius_Aux(nonneg_mat) where {

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
import qualified Orderings;
import qualified Matrix;
import qualified Set;
import qualified Collection_Order;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Arith;

nonneg_mat ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Arith.Linordered_idom a,
      Set_Impl.Set_impl a) => Matrix.Mat a -> Bool;
nonneg_mat a = Set.ball (Matrix.elements_mat a) (Orderings.less_eq Arith.zero);

}
