{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  SN_Order_Carrier(Arctic(..), equal_arctic, one_arctic, zero_arctic,
                    less_arctic, Arctic_delta(..), equal_arctic_delta,
                    one_arctic_delta, zero_arctic_delta, delta_gt, int_mono,
                    delta_mono, pos_arctic, pos_arctic_delta,
                    weak_gt_arctic_delta)
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
import qualified Archimedean_Field;
import qualified Orderings;
import qualified SN_Orders;
import qualified Arith;

instance SN_Orders.Non_strict_order Arith.Int where {
};

instance SN_Orders.Ordered_ab_semigroup Arith.Int where {
};

instance SN_Orders.Ordered_semiring_0 Arith.Int where {
};

instance SN_Orders.Ordered_semiring_1 Arith.Int where {
};

instance SN_Orders.Poly_carrier Arith.Int where {
};

instance SN_Orders.Large_ordered_semiring_1 Arith.Int where {
};

data Arctic = MinInfty | Num_arc Arith.Int;

equal_arctic :: Arctic -> Arctic -> Bool;
equal_arctic MinInfty (Num_arc x2) = False;
equal_arctic (Num_arc x2) MinInfty = False;
equal_arctic (Num_arc x2) (Num_arc y2) = Arith.equal_int x2 y2;
equal_arctic MinInfty MinInfty = True;

instance Eq Arctic where {
  a == b = equal_arctic a b;
};

one_arctic :: Arctic;
one_arctic = Num_arc Arith.zero_int;

instance Arith.One Arctic where {
  one = one_arctic;
};

plus_arctic :: Arctic -> Arctic -> Arctic;
plus_arctic MinInfty y = y;
plus_arctic (Num_arc v) MinInfty = Num_arc v;
plus_arctic (Num_arc x) (Num_arc y) = Num_arc (Orderings.max x y);

instance Arith.Plus Arctic where {
  plus = plus_arctic;
};

zero_arctic :: Arctic;
zero_arctic = MinInfty;

instance Arith.Zero Arctic where {
  zero = zero_arctic;
};

instance Arith.Semigroup_add Arctic where {
};

instance Arith.Numeral Arctic where {
};

times_arctic :: Arctic -> Arctic -> Arctic;
times_arctic MinInfty y = MinInfty;
times_arctic (Num_arc v) MinInfty = MinInfty;
times_arctic (Num_arc x) (Num_arc y) = Num_arc (Arith.plus_int x y);

instance Arith.Times Arctic where {
  times = times_arctic;
};

instance Arith.Power Arctic where {
};

less_eq_arctic :: Arctic -> Arctic -> Bool;
less_eq_arctic MinInfty x = True;
less_eq_arctic (Num_arc uu) MinInfty = False;
less_eq_arctic (Num_arc y) (Num_arc x) = Arith.less_eq_int y x;

less_arctic :: Arctic -> Arctic -> Bool;
less_arctic MinInfty x = True;
less_arctic (Num_arc uu) MinInfty = False;
less_arctic (Num_arc y) (Num_arc x) = Arith.less_int y x;

instance Orderings.Ord Arctic where {
  less_eq = less_eq_arctic;
  less = less_arctic;
};

instance Arith.Ab_semigroup_add Arctic where {
};

instance Arith.Semigroup_mult Arctic where {
};

instance Arith.Semiring Arctic where {
};

instance Arith.Mult_zero Arctic where {
};

instance Arith.Monoid_add Arctic where {
};

instance Arith.Comm_monoid_add Arctic where {
};

instance Arith.Semiring_0 Arctic where {
};

instance Arith.Monoid_mult Arctic where {
};

instance Arith.Semiring_numeral Arctic where {
};

instance Arith.Zero_neq_one Arctic where {
};

instance Arith.Semiring_1 Arctic where {
};

instance SN_Orders.Non_strict_order Arctic where {
};

instance SN_Orders.Ordered_ab_semigroup Arctic where {
};

instance SN_Orders.Ordered_semiring_0 Arctic where {
};

instance SN_Orders.Ordered_semiring_1 Arctic where {
};

data Arctic_delta a = MinInfty_delta | Num_arc_delta a;

equal_arctic_delta ::
  forall a. (Eq a) => Arctic_delta a -> Arctic_delta a -> Bool;
equal_arctic_delta MinInfty_delta (Num_arc_delta x2) = False;
equal_arctic_delta (Num_arc_delta x2) MinInfty_delta = False;
equal_arctic_delta (Num_arc_delta x2) (Num_arc_delta y2) = x2 == y2;
equal_arctic_delta MinInfty_delta MinInfty_delta = True;

instance (Eq a) => Eq (Arctic_delta a) where {
  a == b = equal_arctic_delta a b;
};

one_arctic_delta :: forall a. (Arith.Linordered_field a) => Arctic_delta a;
one_arctic_delta = Num_arc_delta Arith.zero;

instance (Arith.Linordered_field a) => Arith.One (Arctic_delta a) where {
  one = one_arctic_delta;
};

plus_arctic_delta ::
  forall a.
    (Arith.Linordered_field a) => Arctic_delta a ->
                                    Arctic_delta a -> Arctic_delta a;
plus_arctic_delta MinInfty_delta y = y;
plus_arctic_delta (Num_arc_delta v) MinInfty_delta = Num_arc_delta v;
plus_arctic_delta (Num_arc_delta x) (Num_arc_delta y) =
  Num_arc_delta (Orderings.max x y);

instance (Arith.Linordered_field a) => Arith.Plus (Arctic_delta a) where {
  plus = plus_arctic_delta;
};

zero_arctic_delta :: forall a. (Arith.Linordered_field a) => Arctic_delta a;
zero_arctic_delta = MinInfty_delta;

instance (Arith.Linordered_field a) => Arith.Zero (Arctic_delta a) where {
  zero = zero_arctic_delta;
};

instance (Arith.Linordered_field a) => Arith.Semigroup_add (Arctic_delta
                     a) where {
};

instance (Arith.Linordered_field a) => Arith.Numeral (Arctic_delta a) where {
};

times_arctic_delta ::
  forall a.
    (Arith.Linordered_field a) => Arctic_delta a ->
                                    Arctic_delta a -> Arctic_delta a;
times_arctic_delta MinInfty_delta y = MinInfty_delta;
times_arctic_delta (Num_arc_delta v) MinInfty_delta = MinInfty_delta;
times_arctic_delta (Num_arc_delta x) (Num_arc_delta y) =
  Num_arc_delta (Arith.plus x y);

instance (Arith.Linordered_field a) => Arith.Times (Arctic_delta a) where {
  times = times_arctic_delta;
};

instance (Arith.Linordered_field a) => Arith.Power (Arctic_delta a) where {
};

less_eq_arctic_delta ::
  forall a. (Orderings.Ord a) => Arctic_delta a -> Arctic_delta a -> Bool;
less_eq_arctic_delta MinInfty_delta x = True;
less_eq_arctic_delta (Num_arc_delta uu) MinInfty_delta = False;
less_eq_arctic_delta (Num_arc_delta y) (Num_arc_delta x) =
  Orderings.less_eq y x;

less_arctic_delta ::
  forall a. (Orderings.Ord a) => Arctic_delta a -> Arctic_delta a -> Bool;
less_arctic_delta MinInfty_delta x = True;
less_arctic_delta (Num_arc_delta uu) MinInfty_delta = False;
less_arctic_delta (Num_arc_delta y) (Num_arc_delta x) = Orderings.less y x;

instance (Orderings.Ord a) => Orderings.Ord (Arctic_delta a) where {
  less_eq = less_eq_arctic_delta;
  less = less_arctic_delta;
};

instance (Arith.Linordered_field a) => Arith.Ab_semigroup_add (Arctic_delta
                        a) where {
};

instance (Arith.Linordered_field a) => Arith.Semigroup_mult (Arctic_delta
                      a) where {
};

instance (Arith.Linordered_field a) => Arith.Semiring (Arctic_delta a) where {
};

instance (Arith.Linordered_field a) => Arith.Mult_zero (Arctic_delta a) where {
};

instance (Arith.Linordered_field a) => Arith.Monoid_add (Arctic_delta a) where {
};

instance (Arith.Linordered_field a) => Arith.Comm_monoid_add (Arctic_delta
                       a) where {
};

instance (Arith.Linordered_field a) => Arith.Semiring_0 (Arctic_delta a) where {
};

instance (Arith.Linordered_field a) => Arith.Monoid_mult (Arctic_delta
                   a) where {
};

instance (Arith.Linordered_field a) => Arith.Semiring_numeral (Arctic_delta
                        a) where {
};

instance (Arith.Linordered_field a) => Arith.Zero_neq_one (Arctic_delta
                    a) where {
};

instance (Arith.Linordered_field a) => Arith.Semiring_1 (Arctic_delta a) where {
};

instance (Arith.Linordered_field a) => SN_Orders.Non_strict_order (Arctic_delta
                            a) where {
};

instance (Arith.Linordered_field a) => SN_Orders.Ordered_ab_semigroup (Arctic_delta
                                a) where {
};

instance (Arith.Linordered_field a) => SN_Orders.Ordered_semiring_0 (Arctic_delta
                              a) where {
};

instance (Arith.Linordered_field a) => SN_Orders.Ordered_semiring_1 (Arctic_delta
                              a) where {
};

delta_gt ::
  forall a. (Archimedean_Field.Floor_ceiling a) => a -> a -> a -> Bool;
delta_gt delta = (\ x y -> Orderings.less_eq delta (Arith.minus x y));

int_mono :: Arith.Int -> Bool;
int_mono x = Arith.less_eq_int Arith.one_int x;

delta_mono :: forall a. (Archimedean_Field.Floor_ceiling a) => a -> Bool;
delta_mono x = Orderings.less_eq Arith.one x;

pos_arctic :: Arctic -> Bool;
pos_arctic MinInfty = False;
pos_arctic (Num_arc n) = Arith.less_eq_int Arith.zero_int n;

pos_arctic_delta ::
  forall a. (Archimedean_Field.Floor_ceiling a) => Arctic_delta a -> Bool;
pos_arctic_delta MinInfty_delta = False;
pos_arctic_delta (Num_arc_delta n) = Orderings.less_eq Arith.zero n;

weak_gt_arctic_delta ::
  forall a.
    (Archimedean_Field.Floor_ceiling a) => Arctic_delta a ->
     Arctic_delta a -> Bool;
weak_gt_arctic_delta uu MinInfty_delta = True;
weak_gt_arctic_delta MinInfty_delta (Num_arc_delta uv) = False;
weak_gt_arctic_delta (Num_arc_delta x) (Num_arc_delta y) = Orderings.less y x;

}
