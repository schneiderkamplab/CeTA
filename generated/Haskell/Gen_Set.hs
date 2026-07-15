{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Gen_Set(gen_set, gen_ball, gen_pick, gen_image, gen_filter, gen_isEmpty,
           gen_disjoint)
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
import qualified Arith;

gen_set :: forall a b. a -> (b -> a -> a) -> [b] -> a;
gen_set emp ins l = Arith.fold ins l emp;

gen_ball ::
  forall a b c d e.
    (a -> (b -> b) -> (c -> d -> Bool) -> Bool -> e) -> a -> (c -> Bool) -> e;
gen_ball it s p = it s (\ x -> x) (\ x _ -> p x) True;

gen_pick ::
  forall a b c d e f.
    (a -> (Maybe b -> Bool) -> (c -> d -> Maybe c) -> Maybe e -> Maybe f) ->
      a -> f;
gen_pick it s =
  Arith.the (it s (\ a -> (case a of {
                            Nothing -> True;
                            Just _ -> False;
                          }))
               (\ x _ -> Just x)
              Nothing);

gen_image ::
  forall a b c d e f g h.
    (a -> (b -> Bool) -> (c -> d -> e) -> f -> g) ->
      f -> (h -> d -> e) -> (c -> h) -> a -> g;
gen_image it1 emp2 ins2 f s1 = it1 s1 (\ _ -> True) (\ x -> ins2 (f x)) emp2;

gen_filter ::
  forall a b c d e f.
    (a -> (b -> Bool) -> (c -> d -> d) -> e -> f) ->
      e -> (c -> d -> d) -> (c -> Bool) -> a -> f;
gen_filter it1 emp2 ins2 p s1 =
  it1 s1 (\ _ -> True) (\ x s -> (if p x then ins2 x s else s)) emp2;

gen_isEmpty :: forall a b. (a -> (b -> Bool) -> Bool) -> a -> Bool;
gen_isEmpty ball s = ball s (\ _ -> False);

gen_disjoint ::
  forall a b c d e f.
    (a -> (b -> b) -> (c -> d -> Bool) -> Bool -> e) ->
      (c -> f -> Bool) -> a -> f -> e;
gen_disjoint it1 mem2 s1 s2 = it1 s1 (\ x -> x) (\ x _ -> not (mem2 x s2)) True;

}
