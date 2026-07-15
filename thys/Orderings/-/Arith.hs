{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Arith(Nat(..), equal_nat, plus_nat, times_nat, Times(..), one_nat, One(..),
         Plus(..), Zero(..), Semigroup_add, Numeral, minus_nat, Minus(..),
         less_eq_nat, less_nat, Ab_semigroup_add, Mult_zero, Monoid_add,
         Comm_monoid_add, Semiring_0, Semiring_numeral, Semiring_1,
         Comm_semiring_1, Semiring_1_cancel, Comm_semiring_0_cancel,
         Comm_semiring_1_cancel, Neg_numeral, Ring_1, Abs_if, Semiring_char_0,
         Ring_char_0, Linordered_ring, Linordered_ring_strict, Linordered_idom)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;
import qualified Orderings;

data Nat = Zero_nat | Suc Nat;

equal_nat :: Nat -> Nat -> Bool;
equal_nat Zero_nat (Suc x2) = False;
equal_nat (Suc x2) Zero_nat = False;
equal_nat (Suc x2) (Suc y2) = equal_nat x2 y2;
equal_nat Zero_nat Zero_nat = True;

instance Eq Nat where {
  a == b = equal_nat a b;
};

plus_nat :: Nat -> Nat -> Nat;
plus_nat Zero_nat n = n;
plus_nat (Suc m) n = plus_nat m (Suc n);

times_nat :: Nat -> Nat -> Nat;
times_nat Zero_nat n = Zero_nat;
times_nat (Suc m) n = plus_nat n (times_nat m n);

class Times a where {
  times :: a -> a -> a;
};

class (Times a) => Dvd a where {
};

instance Times Nat where {
  times = times_nat;
};

instance Dvd Nat where {
};

one_nat :: Nat;
one_nat = Suc Zero_nat;

class One a where {
  one :: a;
};

instance One Nat where {
  one = one_nat;
};

class Plus a where {
  plus :: a -> a -> a;
};

instance Plus Nat where {
  plus = plus_nat;
};

class Zero a where {
  zero :: a;
};

instance Zero Nat where {
  zero = Zero_nat;
};

class (Plus a) => Semigroup_add a where {
};

class (One a, Semigroup_add a) => Numeral a where {
};

instance Semigroup_add Nat where {
};

instance Numeral Nat where {
};

class (One a, Times a) => Power a where {
};

instance Power Nat where {
};

minus_nat :: Nat -> Nat -> Nat;
minus_nat m Zero_nat = m;
minus_nat Zero_nat n = Zero_nat;
minus_nat (Suc m) (Suc n) = minus_nat m n;

class Minus a where {
  minus :: a -> a -> a;
};

instance Minus Nat where {
  minus = minus_nat;
};

less_eq_nat :: Nat -> Nat -> Bool;
less_eq_nat Zero_nat n = True;
less_eq_nat (Suc m) n = less_nat m n;

less_nat :: Nat -> Nat -> Bool;
less_nat n Zero_nat = False;
less_nat m (Suc n) = less_eq_nat m n;

instance Orderings.Ord Nat where {
  less_eq = less_eq_nat;
  less = less_nat;
};

class (Semigroup_add a) => Ab_semigroup_add a where {
};

class (Times a) => Semigroup_mult a where {
};

class (Ab_semigroup_add a, Semigroup_mult a) => Semiring a where {
};

instance Ab_semigroup_add Nat where {
};

instance Semigroup_mult Nat where {
};

instance Semiring Nat where {
};

instance Orderings.Preorder Nat where {
};

instance Orderings.Order Nat where {
};

class (Times a, Zero a) => Mult_zero a where {
};

instance Mult_zero Nat where {
};

class (Semigroup_add a, Zero a) => Monoid_add a where {
};

class (Ab_semigroup_add a, Monoid_add a) => Comm_monoid_add a where {
};

class (Comm_monoid_add a, Mult_zero a, Semiring a) => Semiring_0 a where {
};

instance Monoid_add Nat where {
};

instance Comm_monoid_add Nat where {
};

instance Semiring_0 Nat where {
};

class (Semigroup_mult a, Power a) => Monoid_mult a where {
};

class (Monoid_mult a, Numeral a, Semiring a) => Semiring_numeral a where {
};

class (One a, Zero a) => Zero_neq_one a where {
};

class (Semiring_numeral a, Semiring_0 a, Zero_neq_one a) => Semiring_1 a where {
};

instance Monoid_mult Nat where {
};

instance Semiring_numeral Nat where {
};

instance Zero_neq_one Nat where {
};

instance Semiring_1 Nat where {
};

instance Orderings.Linorder Nat where {
};

class (Semigroup_mult a) => Ab_semigroup_mult a where {
};

class (Ab_semigroup_mult a, Semiring a) => Comm_semiring a where {
};

instance Ab_semigroup_mult Nat where {
};

instance Comm_semiring Nat where {
};

class (Comm_semiring a, Semiring_0 a) => Comm_semiring_0 a where {
};

instance Comm_semiring_0 Nat where {
};

class (Ab_semigroup_mult a, Monoid_mult a, Dvd a) => Comm_monoid_mult a where {
};

class (Comm_monoid_mult a, Comm_semiring_0 a,
        Semiring_1 a) => Comm_semiring_1 a where {
};

instance Comm_monoid_mult Nat where {
};

instance Comm_semiring_1 Nat where {
};

class (Semigroup_add a) => Cancel_semigroup_add a where {
};

class (Ab_semigroup_add a, Cancel_semigroup_add a,
        Minus a) => Cancel_ab_semigroup_add a where {
};

class (Cancel_ab_semigroup_add a,
        Comm_monoid_add a) => Cancel_comm_monoid_add a where {
};

class (Cancel_comm_monoid_add a, Semiring_0 a) => Semiring_0_cancel a where {
};

instance Cancel_semigroup_add Nat where {
};

instance Cancel_ab_semigroup_add Nat where {
};

instance Cancel_comm_monoid_add Nat where {
};

instance Semiring_0_cancel Nat where {
};

class (Semiring_0_cancel a, Semiring_1 a) => Semiring_1_cancel a where {
};

instance Semiring_1_cancel Nat where {
};

class (Comm_semiring_0 a,
        Semiring_0_cancel a) => Comm_semiring_0_cancel a where {
};

instance Comm_semiring_0_cancel Nat where {
};

class (Comm_semiring_0_cancel a, Comm_semiring_1 a,
        Semiring_1_cancel a) => Comm_semiring_1_cancel a where {
};

instance Comm_semiring_1_cancel Nat where {
};

class (Semiring_0 a) => Semiring_no_zero_divisors a where {
};

class (Semiring_1 a,
        Semiring_no_zero_divisors a) => Semiring_1_no_zero_divisors a where {
};

class (Comm_semiring_1_cancel a,
        Semiring_1_no_zero_divisors a) => Semidom a where {
};

class (Comm_semiring_1_cancel a) => Comm_semiring_1_cancel_crossproduct a where {
};

class (Semiring_no_zero_divisors a) => Semiring_no_zero_divisors_cancel a where {
};

class Uminus a where {
  uminus :: a -> a;
};

class (Cancel_semigroup_add a, Minus a, Monoid_add a,
        Uminus a) => Group_add a where {
};

class (Cancel_comm_monoid_add a, Group_add a) => Ab_group_add a where {
};

class (Ab_group_add a, Semiring_0_cancel a) => Ring a where {
};

class (Ring a,
        Semiring_no_zero_divisors_cancel a) => Ring_no_zero_divisors a where {
};

class (Group_add a, Numeral a) => Neg_numeral a where {
};

class (Neg_numeral a, Ring a, Semiring_1_cancel a) => Ring_1 a where {
};

class (Ring_1 a, Ring_no_zero_divisors a,
        Semiring_1_no_zero_divisors a) => Ring_1_no_zero_divisors a where {
};

class (Comm_semiring_0_cancel a, Ring a) => Comm_ring a where {
};

class (Comm_ring a, Comm_semiring_1_cancel a, Ring_1 a) => Comm_ring_1 a where {
};

class (Comm_ring_1 a, Ring_1_no_zero_divisors a, Semidom a,
        Comm_semiring_1_cancel_crossproduct a) => Idom a where {
};

class Abs a where {
  absa :: a -> a;
};

class (Abs a, Minus a, Uminus a, Zero a, Orderings.Ord a) => Abs_if a where {
};

class (Semiring_1 a) => Semiring_char_0 a where {
};

class (Semiring_char_0 a, Ring_1 a) => Ring_char_0 a where {
};

class Sgn a where {
  sgn :: a -> a;
};

class (Abs a, Sgn a, Idom a) => Idom_abs_sgn a where {
};

class (Ab_semigroup_add a,
        Orderings.Order a) => Ordered_ab_semigroup_add a where {
};

class (Ordered_ab_semigroup_add a) => Strict_ordered_ab_semigroup_add a where {
};

class (Cancel_ab_semigroup_add a,
        Strict_ordered_ab_semigroup_add a) => Ordered_cancel_ab_semigroup_add a where {
};

class (Comm_monoid_add a,
        Ordered_ab_semigroup_add a) => Ordered_comm_monoid_add a where {
};

class (Ordered_comm_monoid_add a, Semiring a) => Ordered_semiring a where {
};

class (Ordered_semiring a, Semiring_0 a) => Ordered_semiring_0 a where {
};

class (Ordered_cancel_ab_semigroup_add a, Ordered_semiring_0 a,
        Semiring_0_cancel a) => Ordered_cancel_semiring a where {
};

class (Ordered_cancel_ab_semigroup_add a) => Ordered_ab_semigroup_add_imp_le a where {
};

class (Comm_monoid_add a,
        Strict_ordered_ab_semigroup_add a) => Strict_ordered_comm_monoid_add a where {
};

class (Ordered_cancel_ab_semigroup_add a, Ordered_comm_monoid_add a,
        Strict_ordered_comm_monoid_add a) => Ordered_cancel_comm_monoid_add a where {
};

class (Cancel_comm_monoid_add a, Ordered_ab_semigroup_add_imp_le a,
        Ordered_cancel_comm_monoid_add a) => Ordered_ab_semigroup_monoid_add_imp_le a where {
};

class (Ab_group_add a,
        Ordered_ab_semigroup_monoid_add_imp_le a) => Ordered_ab_group_add a where {
};

class (Ordered_ab_group_add a, Ordered_cancel_semiring a,
        Ring a) => Ordered_ring a where {
};

class (Orderings.Order a, Zero_neq_one a) => Zero_less_one a where {
};

class (Ordered_cancel_ab_semigroup_add a, Ordered_semiring a,
        Semiring_0_cancel a) => Ordered_semiring_strict a where {
};

class (Ordered_ab_semigroup_add a,
        Orderings.Linorder a) => Linordered_ab_semigroup_add a where {
};

class (Linordered_ab_semigroup_add a,
        Ordered_ab_semigroup_add_imp_le a) => Linordered_cancel_ab_semigroup_add a where {
};

class (Linordered_cancel_ab_semigroup_add a,
        Ordered_ab_semigroup_monoid_add_imp_le a,
        Ordered_cancel_semiring a) => Linordered_semiring a where {
};

class (Linordered_semiring a,
        Ordered_semiring_strict a) => Linordered_semiring_strict a where {
};

class (Ordered_semiring_0 a, Semiring_1 a,
        Zero_less_one a) => Ordered_semiring_1 a where {
};

class (Ordered_semiring_1 a,
        Ordered_semiring_strict a) => Ordered_semiring_1_strict a where {
};

class (Linordered_semiring a,
        Ordered_semiring_1 a) => Linordered_semiring_1 a where {
};

class (Linordered_semiring_1 a, Linordered_semiring_strict a,
        Ordered_semiring_1_strict a) => Linordered_semiring_1_strict a where {
};

class (Abs a, Ordered_ab_group_add a) => Ordered_ab_group_add_abs a where {
};

class (Linordered_cancel_ab_semigroup_add a,
        Ordered_ab_group_add a) => Linordered_ab_group_add a where {
};

class (Linordered_ab_group_add a, Ordered_ab_group_add_abs a, Abs_if a,
        Linordered_semiring a, Ordered_ring a) => Linordered_ring a where {
};

class (Linordered_ring a, Linordered_semiring_strict a,
        Ring_no_zero_divisors a) => Linordered_ring_strict a where {
};

class (Comm_semiring_0 a, Ordered_semiring a) => Ordered_comm_semiring a where {
};

class (Comm_semiring_0_cancel a, Ordered_cancel_semiring a,
        Ordered_comm_semiring a) => Ordered_cancel_comm_semiring a where {
};

class (Ordered_cancel_comm_semiring a,
        Ordered_semiring_strict a) => Ordered_comm_semiring_strict a where {
};

class (Linordered_semiring_strict a,
        Ordered_comm_semiring_strict a) => Linordered_comm_semiring_strict a where {
};

class (Semiring_char_0 a, Orderings.Linorder a, Comm_semiring_1 a,
        Ordered_comm_semiring a,
        Ordered_semiring_1 a) => Linordered_nonzero_semiring a where {
};

class (Linordered_comm_semiring_strict a, Linordered_nonzero_semiring a,
        Semidom a) => Linordered_semidom a where {
};

class (Comm_ring a, Ordered_cancel_comm_semiring a,
        Ordered_ring a) => Ordered_comm_ring a where {
};

class (Ordered_ab_group_add_abs a, Ordered_ring a) => Ordered_ring_abs a where {
};

class (Ring_char_0 a, Idom_abs_sgn a, Linordered_ring_strict a,
        Linordered_semidom a, Linordered_semiring_1_strict a,
        Ordered_comm_ring a, Ordered_ring_abs a) => Linordered_idom a where {
};

}
