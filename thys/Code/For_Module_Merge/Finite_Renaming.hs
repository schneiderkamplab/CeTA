{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Finite_Renaming(extend_finite_map) where {

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
import qualified Product_Type;
import qualified Option;
import qualified List;
import qualified Map;
import qualified HOL;

extend_finite_map :: forall a. (Eq a) => [(a, a)] -> (a -> a, a -> a);
extend_finite_map xs =
  let {
    d = map fst xs;
    r = map snd xs;
    only_r = filter (\ y -> not (List.member d y)) r;
    only_d = filter (\ x -> not (List.member r x)) d;
    ys = xs ++ zip only_r only_d;
    ysa = map (\ (x, y) -> (y, x)) ys;
    fg = Map.map_of ys;
    gf = Map.map_of ysa;
  } in ((\ x -> (case fg x of {
                  Nothing -> x;
                  Just y -> y;
                })),
         (\ y -> (case gf y of {
                   Nothing -> y;
                   Just x -> x;
                 })));

}
