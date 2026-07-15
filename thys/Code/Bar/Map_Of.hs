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
import qualified HOL;
import qualified Mapping;
import qualified Arith;

map_of_total ::
  forall a b.
    (Arith.Ccompare a, Eq a,
      Mapping.Mapping_impl a) => (a -> String -> String) -> [(a, b)] -> a -> b;
map_of_total err xys =
  let {
    m = Mapping.of_alist xys;
  } in (\ x ->
         (case Mapping.lookup m x of {
           Nothing ->
             (error :: forall a. String -> (() -> a) -> a) (err x "")
               (\ _ -> Arith.the Nothing);
           Just y -> y;
         }));

map_of_default ::
  forall a b.
    (Arith.Ccompare b, Eq b, Mapping.Mapping_impl b) => a -> [(b, a)] -> b -> a;
map_of_default d xs = Mapping.lookup_default d (Mapping.of_alist xs);

}
