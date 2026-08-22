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
import qualified Arith;
import qualified Quasi_Order;

newtype Rbt b a = RBT (Arith.Rbt b a);

impl_of :: forall b a. (Quasi_Order.Linorder b) => Rbt b a -> Arith.Rbt b a;
impl_of (RBT x) = x;

keys :: forall a b. (Quasi_Order.Linorder a) => Rbt a b -> [a];
keys x = Arith.keys (impl_of x);

empty :: forall a b. (Quasi_Order.Linorder a) => Rbt a b;
empty = RBT Arith.Empty;

union :: forall a b. (Compare.Compare_order a) => Rbt a b -> Rbt a b -> Rbt a b;
union xb xc = RBT (Arith.rbt_union (impl_of xb) (impl_of xc));

delete :: forall a b. (Compare.Compare_order a) => a -> Rbt a b -> Rbt a b;
delete xb xc = RBT (Arith.rbt_delete xb (impl_of xc));

insert :: forall a b. (Compare.Compare_order a) => a -> b -> Rbt a b -> Rbt a b;
insert xc xd xe = RBT (Arith.rbt_inserta xc xd (impl_of xe));

lookup :: forall a b. (Compare.Compare_order a) => Rbt a b -> a -> Maybe b;
lookup x = Arith.rbt_lookupa (impl_of x);

entries :: forall a b. (Quasi_Order.Linorder a) => Rbt a b -> [(a, b)];
entries x = Arith.entries (impl_of x);

bulkload :: forall a b. (Compare.Compare_order a) => [(a, b)] -> Rbt a b;
bulkload xa = RBT (Arith.rbt_bulkload xa);

}
