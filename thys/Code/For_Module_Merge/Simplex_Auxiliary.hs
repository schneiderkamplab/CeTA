{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Simplex_Auxiliary(min_satisfying) where {

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
import qualified List;
import qualified HOL;
import qualified Orderings;

min_satisfying ::
  forall a. (Orderings.Linorder a) => (a -> Bool) -> [a] -> Maybe a;
min_satisfying p l =
  let {
    xs = filter p l;
  } in (if null xs then Nothing
         else Just (List.foldl Orderings.min (List.hd xs) (List.tl xs)));

}
