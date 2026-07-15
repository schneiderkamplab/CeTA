{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Lexicographic_Order(lexord_fusion, lexord_eq_fusion) where {

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
import qualified HOL;
import qualified List_Fusion;

lexord_fusion ::
  forall a b c.
    (a -> a -> Bool) ->
      List_Fusion.Generator a b -> List_Fusion.Generator a c -> b -> c -> Bool;
lexord_fusion less g1 g2 s1 s2 =
  (if List_Fusion.has_next g1 s1
    then (if List_Fusion.has_next g2 s2
           then (case List_Fusion.next g1 s1 of {
                  (x, s1a) ->
                    (case List_Fusion.next g2 s2 of {
                      (y, s2a) ->
                        less x y ||
                          not (less y x) && lexord_fusion less g1 g2 s1a s2a;
                    });
                })
           else False)
    else List_Fusion.has_next g2 s2);

lexord_eq_fusion ::
  forall a b c.
    (a -> a -> Bool) ->
      List_Fusion.Generator a b -> List_Fusion.Generator a c -> b -> c -> Bool;
lexord_eq_fusion less g1 g2 s1 s2 =
  (if List_Fusion.has_next g1 s1
    then List_Fusion.has_next g2 s2 &&
           (case List_Fusion.next g1 s1 of {
             (x, s1a) ->
               (case List_Fusion.next g2 s2 of {
                 (y, s2a) ->
                   less x y ||
                     not (less y x) && lexord_eq_fusion less g1 g2 s1a s2a;
               });
           })
    else True);

}
