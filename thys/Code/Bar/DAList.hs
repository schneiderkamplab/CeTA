{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module DAList(Alist(..), empty, impl_of, filtera, lookup, update) where {

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
import qualified AList;
import qualified Map;

newtype Alist b a = Alist [(b, a)];

empty :: forall a b. Alist a b;
empty = Alist [];

impl_of :: forall b a. Alist b a -> [(b, a)];
impl_of (Alist x) = x;

filtera :: forall a b. ((a, b) -> Bool) -> Alist a b -> Alist a b;
filtera xb xc = Alist (filter xb (impl_of xc));

lookup :: forall a b. (Eq a) => Alist a b -> a -> Maybe b;
lookup xa = Map.map_of (impl_of xa);

update :: forall a b. (Eq a) => a -> b -> Alist a b -> Alist a b;
update xc xd xe = Alist (AList.update xc xd (impl_of xe));

}
