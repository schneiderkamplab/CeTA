{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Renaming2(Renaming2(..), rename_1, rename_2) where {

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
import qualified Fresh;

newtype Renaming2 a = Abs_renaming2 (a -> a, a -> a);

rep_renaming2 ::
  forall a. (Fresh.Infinite a) => Renaming2 a -> (a -> a, a -> a);
rep_renaming2 (Abs_renaming2 x) = x;

rename_1 :: forall a. (Fresh.Infinite a) => Renaming2 a -> a -> a;
rename_1 xa = fst (rep_renaming2 xa);

rename_2 :: forall a. (Fresh.Infinite a) => Renaming2 a -> a -> a;
rename_2 xa = snd (rep_renaming2 xa);

}
