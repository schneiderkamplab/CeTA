{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Min_Set_Order_Impl(min_set_ext) where {

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

min_set_ext :: forall a. (a -> a -> (Bool, Bool)) -> [a] -> [a] -> (Bool, Bool);
min_set_ext s_ns =
  (\ asa bs ->
    (not (null bs) && all (\ a -> any (\ b -> fst (s_ns a b)) bs) asa,
      all (\ a -> any (\ b -> snd (s_ns a b)) bs) asa));

}
