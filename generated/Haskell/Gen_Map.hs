{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Gen_Map(gen_ball, gen_isEmpty) where {

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

gen_ball ::
  forall a b c d e f.
    (a -> (b -> b) -> (c -> d -> e) -> Bool -> f) -> a -> (c -> e) -> f;
gen_ball it m p = it m (\ x -> x) (\ x _ -> p x) True;

gen_isEmpty :: forall a b c. (a -> (b -> Bool) -> c) -> a -> c;
gen_isEmpty ball m = ball m (\ _ -> False);

}
