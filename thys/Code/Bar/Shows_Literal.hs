{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Shows_Literal(showsl_lit, showsl_nat, showsl_int, showsl_sep, showsl_list_gen,
                 default_showsl_list, Showl(..), showsl_list_nat, showsl_lista,
                 showsl_list_list, showsl_prod, showsl_list_prod,
                 showsl_integer, add_index, showsl_lines, showsl_option,
                 showsl_literal)
  where {

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
import qualified Sum_Type;
import qualified Rat;
import qualified Arith;

lit_of_digit :: Arith.Nat -> String;
lit_of_digit n =
  Arith.implode
    [Arith.char_of_integer ((48 :: Integer) + Arith.integer_of_nat n)];

showsl_lit :: String -> String -> String;
showsl_lit = (\ a b -> a ++ b);

showsl_nat :: Arith.Nat -> String -> String;
showsl_nat n =
  (if Arith.less_nat n (Arith.nat_of_integer (10 :: Integer))
    then showsl_lit (lit_of_digit n)
    else showsl_nat
           (Arith.divide_nat n (Arith.nat_of_integer (10 :: Integer))) .
           showsl_lit
             (lit_of_digit
               (Arith.modulo_nat n (Arith.nat_of_integer (10 :: Integer)))));

showsl_int :: Arith.Int -> String -> String;
showsl_int i =
  (if Arith.less_int i Arith.zero_int
    then showsl_lit "-" . showsl_nat (Arith.nat (Arith.uminus_int i))
    else showsl_nat (Arith.nat i));

showsl_sep ::
  forall a.
    (a -> String -> String) -> (String -> String) -> [a] -> String -> String;
showsl_sep s sep [] = showsl_lit "";
showsl_sep s sep [x] = s x;
showsl_sep s sep (x : v : va) = (s x . sep) . showsl_sep s sep (v : va);

showsl_list_gen ::
  forall a.
    (a -> String -> String) ->
      String -> String -> String -> String -> [a] -> String -> String;
showsl_list_gen showslx e l s r xs =
  (if null xs then showsl_lit e
    else (showsl_lit l . showsl_sep showslx (showsl_lit s) xs) . showsl_lit r);

default_showsl_list ::
  forall a. (a -> String -> String) -> [a] -> String -> String;
default_showsl_list sl = showsl_list_gen sl "[]" "[" ", " "]";

showsl_list_int :: [Arith.Int] -> String -> String;
showsl_list_int xs = default_showsl_list showsl_int xs;

class Showl a where {
  showsl :: a -> String -> String;
  showsl_list :: [a] -> String -> String;
};

instance Showl Arith.Int where {
  showsl = showsl_int;
  showsl_list = showsl_list_int;
};

showsl_list_nat :: [Arith.Nat] -> String -> String;
showsl_list_nat xs = default_showsl_list showsl_nat xs;

instance Showl Arith.Nat where {
  showsl = showsl_nat;
  showsl_list = showsl_list_nat;
};

showsl_rat :: Rat.Rat -> String -> String;
showsl_rat x =
  (case Rat.quotient_of x of {
    (d, n) ->
      (if Arith.equal_int n Arith.one_int then showsl_int d
        else (showsl_int d . showsl_lit "/") . showsl_int n);
  });

showsl_list_rat :: [Rat.Rat] -> String -> String;
showsl_list_rat xs = default_showsl_list showsl_rat xs;

instance Showl Rat.Rat where {
  showsl = showsl_rat;
  showsl_list = showsl_list_rat;
};

showsl_lista :: forall a. (Showl a) => [a] -> String -> String;
showsl_lista xs = showsl_list xs;

showsl_list_list :: forall a. (Showl a) => [[a]] -> String -> String;
showsl_list_list xs = default_showsl_list showsl_lista xs;

instance (Showl a) => Showl [a] where {
  showsl = showsl_lista;
  showsl_list = showsl_list_list;
};

showsl_list_char :: [Arith.Char] -> String -> String;
showsl_list_char cs s = showsl_lit (Arith.implode cs) s;

showsl_char :: Arith.Char -> String -> String;
showsl_char c = showsl_lit (Arith.implode [c]);

instance Showl Arith.Char where {
  showsl = showsl_char;
  showsl_list = showsl_list_char;
};

showsl_sum ::
  forall a b. (Showl a, Showl b) => Sum_Type.Sum a b -> String -> String;
showsl_sum (Sum_Type.Inl x) = (showsl_lit "Inl (" . showsl x) . showsl_lit ")";
showsl_sum (Sum_Type.Inr x) = (showsl_lit "Inr (" . showsl x) . showsl_lit ")";

showsl_list_sum ::
  forall a b. (Showl a, Showl b) => [Sum_Type.Sum a b] -> String -> String;
showsl_list_sum xs = default_showsl_list showsl_sum xs;

instance (Showl a, Showl b) => Showl (Sum_Type.Sum a b) where {
  showsl = showsl_sum;
  showsl_list = showsl_list_sum;
};

showsl_prod :: forall a b. (Showl a, Showl b) => (a, b) -> String -> String;
showsl_prod (x, y) =
  (((showsl_lit "(" . showsl x) . showsl_lit ", ") . showsl y) . showsl_lit ")";

showsl_list_prod ::
  forall a b. (Showl a, Showl b) => [(a, b)] -> String -> String;
showsl_list_prod xs = default_showsl_list showsl_prod xs;

instance (Showl a, Showl b) => Showl (a, b) where {
  showsl = showsl_prod;
  showsl_list = showsl_list_prod;
};

showsl_integer :: Integer -> String -> String;
showsl_integer i = showsl_int (Arith.Int_of_integer i);

showsl_list_integer :: [Integer] -> String -> String;
showsl_list_integer xs = default_showsl_list showsl_integer xs;

instance Showl Integer where {
  showsl = showsl_integer;
  showsl_list = showsl_list_integer;
};

add_index :: (String -> String) -> Arith.Nat -> String -> String;
add_index s i = (s . showsl_lit ".") . showsl_nat i;

showsl_lines :: forall a. (Showl a) => String -> [a] -> String -> String;
showsl_lines desc_empty = showsl_list_gen showsl desc_empty "" "\n" "";

showsl_option :: forall a. (Showl a) => Maybe a -> String -> String;
showsl_option Nothing = showsl_lit "None";
showsl_option (Just x) = (showsl_lit "Some (" . showsl x) . showsl_lit ")";

showsl_literal :: String -> String -> String;
showsl_literal s = showsl_lit s;

}
