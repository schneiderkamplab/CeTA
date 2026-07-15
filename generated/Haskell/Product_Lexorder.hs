{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Product_Lexorder(less_eq_prod, less_prod) where {

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

less_eq_prod ::
  forall a b.
    (Quasi_Order.Ord a, Quasi_Order.Ord b) => (a, b) -> (a, b) -> Bool;
less_eq_prod (x1, y1) (x2, y2) =
  Quasi_Order.less x1 x2 ||
    Quasi_Order.less_eq x1 x2 && Quasi_Order.less_eq y1 y2;

less_prod ::
  forall a b.
    (Quasi_Order.Ord a, Quasi_Order.Ord b) => (a, b) -> (a, b) -> Bool;
less_prod (x1, y1) (x2, y2) =
  Quasi_Order.less x1 x2 || Quasi_Order.less_eq x1 x2 && Quasi_Order.less y1 y2;

instance (Quasi_Order.Ord a,
           Quasi_Order.Ord b) => Quasi_Order.Ord (a, b) where {
  less_eq = less_eq_prod;
  less = less_prod;
};

instance (Quasi_Order.Order a,
           Quasi_Order.Order b) => Quasi_Order.Quasi_order (a, b) where {
};

instance (Quasi_Order.Order a,
           Quasi_Order.Order b) => Quasi_Order.Weak_order (a, b) where {
};

instance (Quasi_Order.Preorder a,
           Quasi_Order.Preorder b) => Quasi_Order.Preorder (a, b) where {
};

instance (Quasi_Order.Order a,
           Quasi_Order.Order b) => Quasi_Order.Order (a, b) where {
};

instance (Quasi_Order.Linorder a,
           Quasi_Order.Linorder b) => Quasi_Order.Linorder (a, b) where {
};

}
