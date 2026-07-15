{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Number_Parser(nat_of_string, int_of_string) where {

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
import qualified List;
import qualified Str;
import qualified Arith;
import qualified Sum_Type;
import qualified Option;

obind :: forall a b. Maybe a -> (a -> Maybe b) -> Maybe b;
obind opt f = (case opt of {
                Nothing -> Nothing;
                Just a -> f a;
              });

sbind ::
  forall a b c. Sum_Type.Sum a b -> (b -> Sum_Type.Sum a c) -> Sum_Type.Sum a c;
sbind su f = (case su of {
               Sum_Type.Inl a -> Sum_Type.Inl a;
               Sum_Type.Inr a -> f a;
             });

safe_head :: forall a. [a] -> Maybe a;
safe_head [] = Nothing;
safe_head (x : xs) = Just x;

nat_of_digit :: Str.Char -> Maybe Arith.Nat;
nat_of_digit x =
  (if Str.equal_char x Str.char_0x30 then Just Arith.zero_nat
    else (if Str.equal_char x Str.char_0x31 then Just Arith.one_nat
           else (if Str.equal_char x Str.char_0x32
                  then Just (Arith.nat_of_integer (2 :: Integer))
                  else (if Str.equal_char x Str.char_0x33
                         then Just (Arith.nat_of_integer (3 :: Integer))
                         else (if Str.equal_char x Str.char_0x34
                                then Just (Arith.nat_of_integer (4 :: Integer))
                                else (if Str.equal_char x Str.char_0x35
                                       then Just
      (Arith.nat_of_integer (5 :: Integer))
                                       else (if Str.equal_char x Str.char_0x36
      then Just (Arith.nat_of_integer (6 :: Integer))
      else (if Str.equal_char x Str.char_0x37
             then Just (Arith.nat_of_integer (7 :: Integer))
             else (if Str.equal_char x Str.char_0x38
                    then Just (Arith.nat_of_integer (8 :: Integer))
                    else (if Str.equal_char x Str.char_0x39
                           then Just (Arith.nat_of_integer (9 :: Integer))
                           else Nothing))))))))));

nat_of_string_aux :: Arith.Nat -> [Str.Char] -> Maybe Arith.Nat;
nat_of_string_aux n [] = Just n;
nat_of_string_aux n (d : s) =
  obind (nat_of_digit d)
    (\ m ->
      nat_of_string_aux
        (Arith.plus_nat
          (Arith.times_nat (Arith.nat_of_integer (10 :: Integer)) n) m)
        s);

nat_of_string :: [Str.Char] -> Sum_Type.Sum String Arith.Nat;
nat_of_string s =
  (case (if null s then Nothing else nat_of_string_aux Arith.zero_nat s) of {
    Nothing ->
      Sum_Type.Inl (("cannot convert \"" ++ Str.implode s) ++ "\" to a number");
    Just a -> Sum_Type.Inr a;
  });

int_of_string :: [Str.Char] -> Sum_Type.Sum String Arith.Int;
int_of_string s =
  (if safe_head s == Just Str.char_0x2D
    then sbind (nat_of_string (List.tl s))
           (\ n -> Sum_Type.Inr (Arith.uminus_int (Arith.int_of_nat n)))
    else sbind (nat_of_string s) (\ n -> Sum_Type.Inr (Arith.int_of_nat n)));

}
