{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module WPO(Order_tag(..), equal_order_tag) where {

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

data Order_tag = Lex | Mul;

equal_order_tag :: Order_tag -> Order_tag -> Bool;
equal_order_tag Lex Mul = False;
equal_order_tag Mul Lex = False;
equal_order_tag Mul Mul = True;
equal_order_tag Lex Lex = True;

}
