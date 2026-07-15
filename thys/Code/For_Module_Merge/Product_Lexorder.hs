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
import qualified Orderings;

less_eq_prod ::
  forall a b. (Orderings.Ord a, Orderings.Ord b) => (a, b) -> (a, b) -> Bool;
less_eq_prod (x1, y1) (x2, y2) =
  Orderings.less x1 x2 || Orderings.less_eq x1 x2 && Orderings.less_eq y1 y2;

less_prod ::
  forall a b. (Orderings.Ord a, Orderings.Ord b) => (a, b) -> (a, b) -> Bool;
less_prod (x1, y1) (x2, y2) =
  Orderings.less x1 x2 || Orderings.less_eq x1 x2 && Orderings.less y1 y2;

instance (Orderings.Ord a, Orderings.Ord b) => Orderings.Ord (a, b) where {
  less_eq = less_eq_prod;
  less = less_prod;
};

instance (Orderings.Order a,
           Orderings.Order b) => Quasi_Order.Quasi_order (a, b) where {
};

instance (Orderings.Order a,
           Orderings.Order b) => Quasi_Order.Weak_order (a, b) where {
};

instance (Orderings.Preorder a,
           Orderings.Preorder b) => Orderings.Preorder (a, b) where {
};

instance (Orderings.Order a,
           Orderings.Order b) => Orderings.Order (a, b) where {
};

instance (Orderings.Linorder a,
           Orderings.Linorder b) => Orderings.Linorder (a, b) where {
};

}
