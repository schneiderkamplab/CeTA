{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module RBT_add(rm_iterateoi) where {

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
import qualified RBT_Impl;

rm_iterateoi ::
  forall a b c. RBT_Impl.Rbt a b -> (c -> Bool) -> ((a, b) -> c -> c) -> c -> c;
rm_iterateoi RBT_Impl.Empty c f sigma = sigma;
rm_iterateoi (RBT_Impl.Branch col l k v r) c f sigma =
  (if c sigma
    then let {
           sigmaa = rm_iterateoi l c f sigma;
         } in (if c sigmaa then rm_iterateoi r c f (f (k, v) sigmaa)
                else sigmaa)
    else sigma);

}
