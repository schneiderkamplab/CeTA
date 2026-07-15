{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module List_Lexorder(less_eq_list, less_list) where {

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
import qualified Quasi_Order;
import qualified Orderings;

less_eq_list :: forall a. (Eq a, Orderings.Order a) => [a] -> [a] -> Bool;
less_eq_list (x : xs) [] = False;
less_eq_list [] xs = True;
less_eq_list (x : xs) (y : ys) =
  Orderings.less x y || x == y && less_eq_list xs ys;

less_list :: forall a. (Eq a, Orderings.Order a) => [a] -> [a] -> Bool;
less_list xs [] = False;
less_list [] (x : xs) = True;
less_list (x : xs) (y : ys) = Orderings.less x y || x == y && less_list xs ys;

instance (Eq a, Orderings.Order a) => Orderings.Ord [a] where {
  less_eq = less_eq_list;
  less = less_list;
};

instance (Eq a, Orderings.Order a) => Quasi_Order.Quasi_order [a] where {
};

instance (Eq a, Orderings.Order a) => Quasi_Order.Weak_order [a] where {
};

instance (Eq a, Orderings.Order a) => Orderings.Preorder [a] where {
};

instance (Eq a, Orderings.Order a) => Orderings.Order [a] where {
};

instance (Eq a, Orderings.Linorder a) => Orderings.Linorder [a] where {
};

}
