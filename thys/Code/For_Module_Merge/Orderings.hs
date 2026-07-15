{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Orderings(Ord(..), Preorder, Order, No_bot, No_top, Linorder, Dense_order,
             Dense_linorder, Unbounded_dense_order, Unbounded_dense_linorder,
             max, min)
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
import qualified Quasi_Order;

class Ord a where {
  less_eq :: a -> a -> Bool;
  less :: a -> a -> Bool;
};

class (Ord a) => Preorder a where {
};

class (Preorder a, Quasi_Order.Weak_order a) => Order a where {
};

class (Order a) => No_bot a where {
};

class (Order a) => No_top a where {
};

class (Order a) => Linorder a where {
};

class (Order a) => Dense_order a where {
};

class (Dense_order a, Linorder a) => Dense_linorder a where {
};

class (Dense_order a, No_bot a, No_top a) => Unbounded_dense_order a where {
};

class (Dense_linorder a,
        Unbounded_dense_order a) => Unbounded_dense_linorder a where {
};

max :: forall a. (Ord a) => a -> a -> a;
max a b = (if less_eq a b then b else a);

min :: forall a. (Ord a) => a -> a -> a;
min a b = (if less_eq a b then a else b);

}
