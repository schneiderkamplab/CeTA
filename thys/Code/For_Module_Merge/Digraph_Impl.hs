{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Digraph_Impl(Gen_g_impl_ext(..), gi_E, gi_V0) where {

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

data Gen_g_impl_ext a b c d = Gen_g_impl_ext a b c d;

gi_E :: forall a b c d. Gen_g_impl_ext a b c d -> b;
gi_E (Gen_g_impl_ext gi_V gi_E gi_V0 more) = gi_E;

gi_V0 :: forall a b c d. Gen_g_impl_ext a b c d -> c;
gi_V0 (Gen_g_impl_ext gi_V gi_E gi_V0 more) = gi_V0;

}
