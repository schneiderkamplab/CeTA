{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Map_Of(map_of_total, map_of_default) where {

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
import qualified Option;
import qualified HOL;
import qualified Mapping;
import qualified Mapping_Impl;
import qualified Collection_Order;

map_of_total ::
  forall a b.
    (Collection_Order.Ccompare a, Eq a,
      Mapping_Impl.Mapping_impl a) => (a -> String -> String) ->
[(a, b)] -> a -> b;
map_of_total err xys =
  let {
    m = Mapping.of_alist xys;
  } in (\ x ->
         (case Mapping.lookup m x of {
           Nothing ->
             (error :: forall a. String -> (() -> a) -> a) (err x "")
               (\ _ -> Option.the Nothing);
           Just y -> y;
         }));

map_of_default ::
  forall a b.
    (Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b) => a -> [(b, a)] -> b -> a;
map_of_default d xs = Mapping.lookup_default d (Mapping.of_alist xs);

}
