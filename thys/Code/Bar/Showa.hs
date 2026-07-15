{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Showa(shows_string, Showa, shows_quote, shows_prec_list) where {

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

shows_prec_char :: Arith.Nat -> Arith.Char -> [Arith.Char] -> [Arith.Char];
shows_prec_char p c = (\ a -> c : a);

shows_string :: [Arith.Char] -> [Arith.Char] -> [Arith.Char];
shows_string = (\ a b -> a ++ b);

shows_list_char :: [Arith.Char] -> [Arith.Char] -> [Arith.Char];
shows_list_char cs = shows_string cs;

class Showa a where {
  shows_prec :: Arith.Nat -> a -> [Arith.Char] -> [Arith.Char];
  shows_list :: [a] -> [Arith.Char] -> [Arith.Char];
};

instance Showa Arith.Char where {
  shows_prec = shows_prec_char;
  shows_list = shows_list_char;
};

shows_quote :: ([Arith.Char] -> [Arith.Char]) -> [Arith.Char] -> [Arith.Char];
shows_quote s =
  (shows_prec_char Arith.zero_nat Arith.char_0x27 . s) .
    shows_prec_char Arith.zero_nat Arith.char_0x27;

shows_prec_list ::
  forall a. (Showa a) => Arith.Nat -> [a] -> [Arith.Char] -> [Arith.Char];
shows_prec_list p xs = shows_list xs;

}
