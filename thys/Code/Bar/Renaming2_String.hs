{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Renaming2_String(string_rename) where {

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
import qualified Renaming2;
import qualified Arith;
import qualified Lists_are_Infinite;

string_rename :: Renaming2.Renaming2 [Arith.Char];
string_rename =
  Renaming2.Abs_renaming2
    ((\ a -> Arith.char_0x78 : a), (\ a -> Arith.char_0x79 : a));

}
