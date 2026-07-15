{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  RBT(Rbt, impl_of, keys, empty, union, delete, insert, lookup, entries,
       bulkload)
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
import qualified Compare;
import qualified RBT_Impl;
import qualified Orderings;

newtype Rbt b a = RBT (RBT_Impl.Rbt b a);

impl_of :: forall b a. (Orderings.Linorder b) => Rbt b a -> RBT_Impl.Rbt b a;
impl_of (RBT x) = x;

keys :: forall a b. (Orderings.Linorder a) => Rbt a b -> [a];
keys x = RBT_Impl.keys (impl_of x);

empty :: forall a b. (Orderings.Linorder a) => Rbt a b;
empty = RBT RBT_Impl.Empty;

union :: forall a b. (Compare.Compare_order a) => Rbt a b -> Rbt a b -> Rbt a b;
union xb xc = RBT (RBT_Impl.rbt_union (impl_of xb) (impl_of xc));

delete :: forall a b. (Compare.Compare_order a) => a -> Rbt a b -> Rbt a b;
delete xb xc = RBT (RBT_Impl.rbt_delete xb (impl_of xc));

insert :: forall a b. (Compare.Compare_order a) => a -> b -> Rbt a b -> Rbt a b;
insert xc xd xe = RBT (RBT_Impl.rbt_insert xc xd (impl_of xe));

lookup :: forall a b. (Compare.Compare_order a) => Rbt a b -> a -> Maybe b;
lookup x = RBT_Impl.rbt_lookup (impl_of x);

entries :: forall a b. (Orderings.Linorder a) => Rbt a b -> [(a, b)];
entries x = RBT_Impl.entries (impl_of x);

bulkload :: forall a b. (Compare.Compare_order a) => [(a, b)] -> Rbt a b;
bulkload xa = RBT (RBT_Impl.rbt_bulkload xa);

}
