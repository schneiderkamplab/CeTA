{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module SetIteratorOperations(map_iterator_dom) where {

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

set_iterator_image ::
  forall a b c.
    (a -> b) ->
      ((c -> Bool) -> (a -> c -> c) -> c -> c) ->
        (c -> Bool) -> (b -> c -> c) -> c -> c;
set_iterator_image g it = (\ c f -> it c (\ x -> f (g x)));

map_iterator_dom ::
  forall a b c.
    ((a -> Bool) -> ((b, c) -> a -> a) -> a -> a) ->
      (a -> Bool) -> (b -> a -> a) -> a -> a;
map_iterator_dom it = set_iterator_image fst it;

}
