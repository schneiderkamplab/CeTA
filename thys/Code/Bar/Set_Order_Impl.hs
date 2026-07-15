{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Set_Order_Impl(set_ext) where {

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

set_ext :: forall a. (a -> a -> (Bool, Bool)) -> [a] -> [a] -> (Bool, Bool);
set_ext s_ns =
  (\ asa bs ->
    (not (null asa) && all (\ b -> any (\ a -> fst (s_ns a b)) asa) bs,
      all (\ b -> any (\ a -> snd (s_ns a b)) asa) bs));

}
