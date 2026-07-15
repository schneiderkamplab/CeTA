{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Show_Instances(shows_prec_nat, shows_prec_rat) where {

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
import qualified Rat;
import qualified Showa;
import qualified Str;
import qualified Arith;

string_of_digit :: Arith.Nat -> [Str.Char];
string_of_digit n =
  (if Arith.equal_nat n Arith.zero_nat then [Str.char_0x30]
    else (if Arith.equal_nat n Arith.one_nat then [Str.char_0x31]
           else (if Arith.equal_nat n (Arith.nat_of_integer (2 :: Integer))
                  then [Str.char_0x32]
                  else (if Arith.equal_nat n
                             (Arith.nat_of_integer (3 :: Integer))
                         then [Str.char_0x33]
                         else (if Arith.equal_nat n
                                    (Arith.nat_of_integer (4 :: Integer))
                                then [Str.char_0x34]
                                else (if Arith.equal_nat n
   (Arith.nat_of_integer (5 :: Integer))
                                       then [Str.char_0x35]
                                       else (if Arith.equal_nat n
          (Arith.nat_of_integer (6 :: Integer))
      then [Str.char_0x36]
      else (if Arith.equal_nat n (Arith.nat_of_integer (7 :: Integer))
             then [Str.char_0x37]
             else (if Arith.equal_nat n (Arith.nat_of_integer (8 :: Integer))
                    then [Str.char_0x38] else [Str.char_0x39])))))))));

showsp_nat :: Arith.Nat -> Arith.Nat -> [Str.Char] -> [Str.Char];
showsp_nat p n =
  (if Arith.less_nat n (Arith.nat_of_integer (10 :: Integer))
    then Showa.shows_string (string_of_digit n)
    else showsp_nat p
           (Arith.divide_nat n (Arith.nat_of_integer (10 :: Integer))) .
           Showa.shows_string
             (string_of_digit
               (Arith.modulo_nat n (Arith.nat_of_integer (10 :: Integer)))));

showsp_int :: Arith.Nat -> Arith.Int -> [Str.Char] -> [Str.Char];
showsp_int p i =
  (if Arith.less_int i Arith.zero_int
    then Showa.shows_string [Str.char_0x2D] .
           showsp_nat p (Arith.nat (Arith.uminus_int i))
    else showsp_nat p (Arith.nat i));

showsp_rat :: Arith.Nat -> Rat.Rat -> [Str.Char] -> [Str.Char];
showsp_rat p x =
  (case Rat.quotient_of x of {
    (d, n) ->
      (if Arith.equal_int n Arith.one_int then showsp_int p d
        else (showsp_int p d . Showa.shows_string [Str.char_0x2F]) .
               showsp_int p n);
  });

shows_prec_nat :: Arith.Nat -> Arith.Nat -> [Str.Char] -> [Str.Char];
shows_prec_nat = showsp_nat;

shows_prec_rat :: Arith.Nat -> Rat.Rat -> [Str.Char] -> [Str.Char];
shows_prec_rat = showsp_rat;

}
