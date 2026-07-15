{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Compare_Instances(compare_nat, comparator_list, compare_list, compare_char,
                     comparator_prod, compare_prod, compare_integer,
                     comparator_option, compare_int)
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
import qualified Str;
import qualified Orderings;
import qualified Comparator;
import qualified Arith;
import qualified Compare;

compare_nat :: Arith.Nat -> Arith.Nat -> Comparator.Order;
compare_nat = Comparator.comparator_of;

instance Compare.Compare Arith.Nat where {
  compare = compare_nat;
};

instance Compare.Compare_order Arith.Nat where {
};

comparator_list ::
  forall a. (a -> a -> Comparator.Order) -> [a] -> [a] -> Comparator.Order;
comparator_list comp_a [] [] = Comparator.Eqa;
comparator_list comp_a [] (y : ya) = Comparator.Lt;
comparator_list comp_a (x : xa) [] = Comparator.Gt;
comparator_list comp_a (x : xa) (y : ya) =
  (case comp_a x y of {
    Comparator.Eqa -> comparator_list comp_a xa ya;
    Comparator.Lt -> Comparator.Lt;
    Comparator.Gt -> Comparator.Gt;
  });

compare_list :: forall a. (Compare.Compare a) => [a] -> [a] -> Comparator.Order;
compare_list = comparator_list Compare.compare;

instance (Compare.Compare a) => Compare.Compare [a] where {
  compare = compare_list;
};

compare_char :: Str.Char -> Str.Char -> Comparator.Order;
compare_char = Comparator.comparator_of;

instance Compare.Compare Str.Char where {
  compare = compare_char;
};

instance Compare.Compare_order Str.Char where {
};

comparator_prod ::
  forall a b.
    (a -> a -> Comparator.Order) ->
      (b -> b -> Comparator.Order) -> (a, b) -> (a, b) -> Comparator.Order;
comparator_prod comp_a comp_b (x, xa) (y, ya) =
  (case comp_a x y of {
    Comparator.Eqa -> comp_b xa ya;
    Comparator.Lt -> Comparator.Lt;
    Comparator.Gt -> Comparator.Gt;
  });

compare_prod ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => (a, b) -> (a, b) -> Comparator.Order;
compare_prod = comparator_prod Compare.compare Compare.compare;

instance (Compare.Compare a,
           Compare.Compare b) => Compare.Compare (a, b) where {
  compare = compare_prod;
};

comparator_unit :: () -> () -> Comparator.Order;
comparator_unit x y = Comparator.Eqa;

compare_unit :: () -> () -> Comparator.Order;
compare_unit = comparator_unit;

instance Compare.Compare () where {
  compare = compare_unit;
};

compare_integer :: Integer -> Integer -> Comparator.Order;
compare_integer = Comparator.comparator_of;

instance Compare.Compare Integer where {
  compare = compare_integer;
};

instance Compare.Compare_order Integer where {
};

comparator_option ::
  forall a.
    (a -> a -> Comparator.Order) -> Maybe a -> Maybe a -> Comparator.Order;
comparator_option comp_a Nothing Nothing = Comparator.Eqa;
comparator_option comp_a Nothing (Just y) = Comparator.Lt;
comparator_option comp_a (Just x) Nothing = Comparator.Gt;
comparator_option comp_a (Just x) (Just y) = comp_a x y;

compare_int :: Arith.Int -> Arith.Int -> Comparator.Order;
compare_int = Comparator.comparator_of;

}
