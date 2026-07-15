{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Arith(Int(..), equal_int, times_int, Times(..), Dvd, uminus_int, zero_int,
         less_int, abs_int, Abs(..), Num(..), one_int, One(..), sgn_int,
         Sgn(..), minus_int, plus_int, Uminus(..), Minus(..), Zero(..),
         Plus(..), Semigroup_add, Cancel_semigroup_add, Ab_semigroup_add,
         Cancel_ab_semigroup_add, Monoid_add, Comm_monoid_add,
         Cancel_comm_monoid_add, Mult_zero, Semigroup_mult, Semiring,
         Semiring_0, Semiring_0_cancel, Ab_semigroup_mult, Comm_semiring,
         Comm_semiring_0, Comm_semiring_0_cancel, Power, Monoid_mult, Numeral,
         Semiring_numeral, Zero_neq_one, Semiring_1, Semiring_1_cancel,
         Comm_monoid_mult, Comm_semiring_1, Comm_semiring_1_cancel,
         Comm_semiring_1_cancel_crossproduct, Semiring_no_zero_divisors,
         Semiring_1_no_zero_divisors, Semiring_no_zero_divisors_cancel,
         Group_add, Ab_group_add, Ring, Ring_no_zero_divisors, Neg_numeral,
         Ring_1, Ring_1_no_zero_divisors, Comm_ring, Comm_ring_1, Semidom, Idom,
         less_eq_int, Abs_if, Semiring_char_0, Ring_char_0, Idom_abs_sgn,
         Ordered_ab_semigroup_add, Strict_ordered_ab_semigroup_add,
         Ordered_cancel_ab_semigroup_add, Ordered_comm_monoid_add,
         Ordered_semiring, Ordered_semiring_0, Ordered_cancel_semiring,
         Ordered_ab_semigroup_add_imp_le, Strict_ordered_comm_monoid_add,
         Ordered_cancel_comm_monoid_add, Ordered_ab_semigroup_monoid_add_imp_le,
         Ordered_ab_group_add, Ordered_ring, Zero_less_one,
         Ordered_semiring_strict, Linordered_ab_semigroup_add,
         Linordered_cancel_ab_semigroup_add, Linordered_semiring,
         Linordered_semiring_strict, Ordered_semiring_1,
         Ordered_semiring_1_strict, Linordered_semiring_1,
         Linordered_semiring_1_strict, Ordered_ab_group_add_abs,
         Linordered_ab_group_add, Linordered_ring, Linordered_ring_strict,
         Ordered_comm_semiring, Ordered_cancel_comm_semiring,
         Ordered_comm_semiring_strict, Linordered_comm_semiring_strict,
         Linordered_nonzero_semiring, Linordered_semidom, Ordered_comm_ring,
         Ordered_ring_abs, Linordered_idom, Nat, integer_of_nat, equal_nat,
         times_nat, one_nat, plus_nat, zero_nat, minus_nat, less_eq_nat,
         less_nat, divide_integer, divide_nat, Divide(..), modulo_integer,
         modulo_nat, Modulo(..), Divide_trivial, Semidom_divide,
         Semiring_modulo, Semiring_modulo_trivial, Algebraic_semidom,
         Semidom_modulo, Idom_divide, Inverse(..), Division_ring, Field,
         Field_char_0, Field_abs_sgn, Linordered_field, Unit_factor(..),
         Semidom_divide_unit_factor, Normalization_semidom(..),
         Euclidean_semiring(..), Normalization_semidom_multiplicative,
         nat_of_integer, nat, suc, funpow, dvd, power, int_of_nat, divmod_nat,
         of_nat, divide_int)
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
import qualified Product_Type;
import qualified HOL;
import qualified Unique_Factorization;
import qualified Lattices;
import qualified Max_Polynomial_Aux;
import qualified Norms;
import qualified Quasi_Order;
import qualified List;
import qualified Orderings;

newtype Int = Int_of_integer Integer;

integer_of_int :: Int -> Integer;
integer_of_int (Int_of_integer k) = k;

equal_int :: Int -> Int -> Bool;
equal_int k l = integer_of_int k == integer_of_int l;

instance Eq Int where {
  a == b = equal_int a b;
};

times_int :: Int -> Int -> Int;
times_int k l = Int_of_integer (integer_of_int k * integer_of_int l);

class Times a where {
  times :: a -> a -> a;
};

class (Times a) => Dvd a where {
};

instance Times Int where {
  times = times_int;
};

instance Dvd Int where {
};

uminus_int :: Int -> Int;
uminus_int k = Int_of_integer (negate (integer_of_int k));

zero_int :: Int;
zero_int = Int_of_integer (0 :: Integer);

less_int :: Int -> Int -> Bool;
less_int k l = integer_of_int k < integer_of_int l;

abs_int :: Int -> Int;
abs_int i = (if less_int i zero_int then uminus_int i else i);

class Abs a where {
  absa :: a -> a;
};

instance Abs Int where {
  absa = abs_int;
};

data Num = One | Bit0 Num | Bit1 Num;

one_int :: Int;
one_int = Int_of_integer (1 :: Integer);

class One a where {
  one :: a;
};

instance One Int where {
  one = one_int;
};

sgn_int :: Int -> Int;
sgn_int i =
  (if equal_int i zero_int then zero_int
    else (if less_int zero_int i then one_int else uminus_int one_int));

class Sgn a where {
  sgn :: a -> a;
};

instance Sgn Int where {
  sgn = sgn_int;
};

minus_int :: Int -> Int -> Int;
minus_int k l = Int_of_integer (integer_of_int k - integer_of_int l);

plus_int :: Int -> Int -> Int;
plus_int k l = Int_of_integer (integer_of_int k + integer_of_int l);

class Uminus a where {
  uminus :: a -> a;
};

class Minus a where {
  minus :: a -> a -> a;
};

class Zero a where {
  zero :: a;
};

class Plus a where {
  plus :: a -> a -> a;
};

class (Plus a) => Semigroup_add a where {
};

class (Semigroup_add a) => Cancel_semigroup_add a where {
};

class (Semigroup_add a) => Ab_semigroup_add a where {
};

class (Ab_semigroup_add a, Cancel_semigroup_add a,
        Minus a) => Cancel_ab_semigroup_add a where {
};

class (Semigroup_add a, Zero a) => Monoid_add a where {
};

class (Ab_semigroup_add a, Monoid_add a) => Comm_monoid_add a where {
};

class (Cancel_ab_semigroup_add a,
        Comm_monoid_add a) => Cancel_comm_monoid_add a where {
};

class (Times a, Zero a) => Mult_zero a where {
};

class (Times a) => Semigroup_mult a where {
};

class (Ab_semigroup_add a, Semigroup_mult a) => Semiring a where {
};

class (Comm_monoid_add a, Mult_zero a, Semiring a) => Semiring_0 a where {
};

class (Cancel_comm_monoid_add a, Semiring_0 a) => Semiring_0_cancel a where {
};

class (Semigroup_mult a) => Ab_semigroup_mult a where {
};

class (Ab_semigroup_mult a, Semiring a) => Comm_semiring a where {
};

class (Comm_semiring a, Semiring_0 a) => Comm_semiring_0 a where {
};

class (Comm_semiring_0 a,
        Semiring_0_cancel a) => Comm_semiring_0_cancel a where {
};

class (One a, Times a) => Power a where {
};

class (Semigroup_mult a, Power a) => Monoid_mult a where {
};

class (One a, Semigroup_add a) => Numeral a where {
};

class (Monoid_mult a, Numeral a, Semiring a) => Semiring_numeral a where {
};

class (One a, Zero a) => Zero_neq_one a where {
};

class (Semiring_numeral a, Semiring_0 a, Zero_neq_one a) => Semiring_1 a where {
};

class (Semiring_0_cancel a, Semiring_1 a) => Semiring_1_cancel a where {
};

class (Ab_semigroup_mult a, Monoid_mult a, Dvd a) => Comm_monoid_mult a where {
};

class (Comm_monoid_mult a, Comm_semiring_0 a,
        Semiring_1 a) => Comm_semiring_1 a where {
};

class (Comm_semiring_0_cancel a, Comm_semiring_1 a,
        Semiring_1_cancel a) => Comm_semiring_1_cancel a where {
};

class (Comm_semiring_1_cancel a) => Comm_semiring_1_cancel_crossproduct a where {
};

class (Semiring_0 a) => Semiring_no_zero_divisors a where {
};

class (Semiring_1 a,
        Semiring_no_zero_divisors a) => Semiring_1_no_zero_divisors a where {
};

class (Semiring_no_zero_divisors a) => Semiring_no_zero_divisors_cancel a where {
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

class (Comm_semiring_1_cancel a,
        Semiring_1_no_zero_divisors a) => Semidom a where {
};

class (Comm_ring_1 a, Ring_1_no_zero_divisors a, Semidom a,
        Comm_semiring_1_cancel_crossproduct a) => Idom a where {
};

instance Plus Int where {
  plus = plus_int;
};

instance Semigroup_add Int where {
};

instance Cancel_semigroup_add Int where {
};

instance Ab_semigroup_add Int where {
};

instance Minus Int where {
  minus = minus_int;
};

instance Cancel_ab_semigroup_add Int where {
};

instance Zero Int where {
  zero = zero_int;
};

instance Monoid_add Int where {
};

instance Comm_monoid_add Int where {
};

instance Cancel_comm_monoid_add Int where {
};

instance Mult_zero Int where {
};

instance Semigroup_mult Int where {
};

instance Semiring Int where {
};

instance Semiring_0 Int where {
};

instance Semiring_0_cancel Int where {
};

instance Ab_semigroup_mult Int where {
};

instance Comm_semiring Int where {
};

instance Comm_semiring_0 Int where {
};

instance Comm_semiring_0_cancel Int where {
};

instance Power Int where {
};

instance Monoid_mult Int where {
};

instance Numeral Int where {
};

instance Semiring_numeral Int where {
};

instance Zero_neq_one Int where {
};

instance Semiring_1 Int where {
};

instance Semiring_1_cancel Int where {
};

instance Comm_monoid_mult Int where {
};

instance Comm_semiring_1 Int where {
};

instance Comm_semiring_1_cancel Int where {
};

instance Comm_semiring_1_cancel_crossproduct Int where {
};

instance Semiring_no_zero_divisors Int where {
};

instance Semiring_1_no_zero_divisors Int where {
};

instance Semiring_no_zero_divisors_cancel Int where {
};

instance Uminus Int where {
  uminus = uminus_int;
};

instance Group_add Int where {
};

instance Ab_group_add Int where {
};

instance Ring Int where {
};

instance Ring_no_zero_divisors Int where {
};

instance Neg_numeral Int where {
};

instance Ring_1 Int where {
};

instance Ring_1_no_zero_divisors Int where {
};

instance Comm_ring Int where {
};

instance Comm_ring_1 Int where {
};

instance Semidom Int where {
};

instance Idom Int where {
};

less_eq_int :: Int -> Int -> Bool;
less_eq_int k l = integer_of_int k <= integer_of_int l;

class (Abs a, Minus a, Uminus a, Zero a, Orderings.Ord a) => Abs_if a where {
};

instance Orderings.Ord Int where {
  less_eq = less_eq_int;
  less = less_int;
};

instance Abs_if Int where {
};

class (Semiring_1 a) => Semiring_char_0 a where {
};

class (Semiring_char_0 a, Ring_1 a) => Ring_char_0 a where {
};

instance Semiring_char_0 Int where {
};

instance Ring_char_0 Int where {
};

instance Orderings.Preorder Int where {
};

instance Orderings.Order Int where {
};

instance Orderings.Linorder Int where {
};

class (Abs a, Sgn a, Idom a) => Idom_abs_sgn a where {
};

instance Idom_abs_sgn Int where {
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

class (Max_Polynomial_Aux.Ordered_semigroup_mult_zero a, Ordered_semiring a,
        Semiring_0 a) => Ordered_semiring_0 a where {
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

instance Ordered_ab_semigroup_add Int where {
};

instance Strict_ordered_ab_semigroup_add Int where {
};

instance Ordered_cancel_ab_semigroup_add Int where {
};

instance Max_Polynomial_Aux.Ordered_semigroup_mult_zero Int where {
};

instance Ordered_comm_monoid_add Int where {
};

instance Ordered_semiring Int where {
};

instance Ordered_semiring_0 Int where {
};

instance Ordered_cancel_semiring Int where {
};

instance Ordered_ab_semigroup_add_imp_le Int where {
};

instance Strict_ordered_comm_monoid_add Int where {
};

instance Ordered_cancel_comm_monoid_add Int where {
};

instance Ordered_ab_semigroup_monoid_add_imp_le Int where {
};

instance Ordered_ab_group_add Int where {
};

instance Ordered_ring Int where {
};

class (Orderings.Order a, Zero_neq_one a) => Zero_less_one a where {
};

instance Zero_less_one Int where {
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

class (Max_Polynomial_Aux.Ordered_semiring_1 a, Linordered_semiring a,
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

class (Ring_char_0 a, Norms.Semiring_1_real_line a, Idom_abs_sgn a,
        Linordered_ring_strict a, Linordered_semidom a,
        Linordered_semiring_1_strict a, Ordered_comm_ring a,
        Ordered_ring_abs a) => Linordered_idom a where {
};

instance Ordered_semiring_strict Int where {
};

instance Linordered_ab_semigroup_add Int where {
};

instance Linordered_cancel_ab_semigroup_add Int where {
};

instance Linordered_semiring Int where {
};

instance Linordered_semiring_strict Int where {
};

instance Ordered_semiring_1 Int where {
};

instance Ordered_semiring_1_strict Int where {
};

instance Max_Polynomial_Aux.Ordered_semiring_1 Int where {
};

instance Linordered_semiring_1 Int where {
};

instance Linordered_semiring_1_strict Int where {
};

instance Ordered_ab_group_add_abs Int where {
};

instance Linordered_ab_group_add Int where {
};

instance Linordered_ring Int where {
};

instance Linordered_ring_strict Int where {
};

instance Norms.Semiring_real_line Int where {
};

instance Norms.Semiring_1_real_line Int where {
};

instance Ordered_comm_semiring Int where {
};

instance Ordered_cancel_comm_semiring Int where {
};

instance Ordered_comm_semiring_strict Int where {
};

instance Linordered_comm_semiring_strict Int where {
};

instance Linordered_nonzero_semiring Int where {
};

instance Linordered_semidom Int where {
};

instance Ordered_comm_ring Int where {
};

instance Ordered_ring_abs Int where {
};

instance Linordered_idom Int where {
};

newtype Nat = Nat Integer;

integer_of_nat :: Nat -> Integer;
integer_of_nat (Nat x) = x;

equal_nat :: Nat -> Nat -> Bool;
equal_nat m n = integer_of_nat m == integer_of_nat n;

instance Eq Nat where {
  a == b = equal_nat a b;
};

times_nat :: Nat -> Nat -> Nat;
times_nat m n = Nat (integer_of_nat m * integer_of_nat n);

instance Times Nat where {
  times = times_nat;
};

instance Dvd Nat where {
};

one_nat :: Nat;
one_nat = Nat (1 :: Integer);

instance One Nat where {
  one = one_nat;
};

plus_nat :: Nat -> Nat -> Nat;
plus_nat m n = Nat (integer_of_nat m + integer_of_nat n);

instance Plus Nat where {
  plus = plus_nat;
};

zero_nat :: Nat;
zero_nat = Nat (0 :: Integer);

instance Zero Nat where {
  zero = zero_nat;
};

instance Semigroup_add Nat where {
};

instance Numeral Nat where {
};

instance Power Nat where {
};

instance Orderings.Ord Integer where {
  less_eq = (\ a b -> a <= b);
  less = (\ a b -> a < b);
};

minus_nat :: Nat -> Nat -> Nat;
minus_nat m n =
  Nat (Orderings.max (0 :: Integer) (integer_of_nat m - integer_of_nat n));

instance Minus Nat where {
  minus = minus_nat;
};

less_eq_nat :: Nat -> Nat -> Bool;
less_eq_nat m n = integer_of_nat m <= integer_of_nat n;

less_nat :: Nat -> Nat -> Bool;
less_nat m n = integer_of_nat m < integer_of_nat n;

instance Orderings.Ord Nat where {
  less_eq = less_eq_nat;
  less = less_nat;
};

inf_nat :: Nat -> Nat -> Nat;
inf_nat = Orderings.min;

instance Lattices.Inf Nat where {
  inf = inf_nat;
};

sup_nat :: Nat -> Nat -> Nat;
sup_nat = Orderings.max;

instance Lattices.Sup Nat where {
  sup = sup_nat;
};

divmod_integer :: Integer -> Integer -> (Integer, Integer);
divmod_integer k l =
  (if k == (0 :: Integer) then ((0 :: Integer), (0 :: Integer))
    else (if (0 :: Integer) < l
           then (if (0 :: Integer) < k then divMod ( k ) ( l )
                  else (case divMod ( (negate k) ) ( l ) of {
                         (r, s) ->
                           (if s == (0 :: Integer)
                             then (negate r, (0 :: Integer))
                             else (negate r - (1 :: Integer), l - s));
                       }))
           else (if l == (0 :: Integer) then ((0 :: Integer), k)
                  else Product_Type.apsnd negate
                         (if k < (0 :: Integer)
                           then divMod ( (negate k) ) ( (negate l) )
                           else (case divMod ( k ) ( (negate l) ) of {
                                  (r, s) ->
                                    (if s == (0 :: Integer)
                                      then (negate r, (0 :: Integer))
                                      else (negate r - (1 :: Integer),
     negate l - s));
                                })))));

divide_integer :: Integer -> Integer -> Integer;
divide_integer k l = fst (divmod_integer k l);

divide_nat :: Nat -> Nat -> Nat;
divide_nat m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));

class Divide a where {
  divide :: a -> a -> a;
};

instance Divide Nat where {
  divide = divide_nat;
};

modulo_integer :: Integer -> Integer -> Integer;
modulo_integer k l = snd (divmod_integer k l);

modulo_nat :: Nat -> Nat -> Nat;
modulo_nat m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));

class (Divide a, Dvd a) => Modulo a where {
  modulo :: a -> a -> a;
};

instance Modulo Nat where {
  modulo = modulo_nat;
};

instance Ab_semigroup_add Nat where {
};

instance Monoid_add Nat where {
};

instance Comm_monoid_add Nat where {
};

instance Mult_zero Nat where {
};

instance Semigroup_mult Nat where {
};

instance Semiring Nat where {
};

instance Semiring_0 Nat where {
};

instance Semiring_no_zero_divisors Nat where {
};

instance Monoid_mult Nat where {
};

instance Semiring_numeral Nat where {
};

instance Zero_neq_one Nat where {
};

instance Semiring_1 Nat where {
};

instance Semiring_1_no_zero_divisors Nat where {
};

instance Cancel_semigroup_add Nat where {
};

instance Cancel_ab_semigroup_add Nat where {
};

instance Cancel_comm_monoid_add Nat where {
};

instance Semiring_0_cancel Nat where {
};

instance Ab_semigroup_mult Nat where {
};

instance Comm_semiring Nat where {
};

instance Comm_semiring_0 Nat where {
};

instance Comm_semiring_0_cancel Nat where {
};

instance Semiring_1_cancel Nat where {
};

instance Comm_monoid_mult Nat where {
};

instance Comm_semiring_1 Nat where {
};

instance Comm_semiring_1_cancel Nat where {
};

instance Semidom Nat where {
};

instance Quasi_Order.Quasi_order Nat where {
};

instance Quasi_Order.Weak_order Nat where {
};

instance Orderings.Preorder Nat where {
};

instance Orderings.Order Nat where {
};

instance Quasi_Order.Quasi_order_sup Nat where {
};

instance Quasi_Order.Quasi_semilattice_sup Nat where {
};

instance Lattices.Semilattice_sup Nat where {
};

instance Lattices.Semilattice_inf Nat where {
};

instance Lattices.Lattice Nat where {
};

instance Orderings.Linorder Nat where {
};

class (One a, Zero a, Divide a) => Divide_trivial a where {
};

instance Divide_trivial Nat where {
};

class (Divide_trivial a, Semidom a,
        Semiring_no_zero_divisors_cancel a) => Semidom_divide a where {
};

instance Semiring_no_zero_divisors_cancel Nat where {
};

instance Semidom_divide Nat where {
};

class (Comm_semiring_1_cancel a, Modulo a) => Semiring_modulo a where {
};

class (Divide_trivial a, Semiring_modulo a) => Semiring_modulo_trivial a where {
};

class (Semidom_divide a) => Algebraic_semidom a where {
};

class (Algebraic_semidom a,
        Semiring_modulo_trivial a) => Semidom_modulo a where {
};

instance Semiring_modulo Nat where {
};

instance Semiring_modulo_trivial Nat where {
};

instance Algebraic_semidom Nat where {
};

instance Semidom_modulo Nat where {
};

instance Quasi_Order.Quasi_order Integer where {
};

instance Quasi_Order.Weak_order Integer where {
};

instance Orderings.Preorder Integer where {
};

instance Orderings.Order Integer where {
};

instance Orderings.Linorder Integer where {
};

class (Idom a, Semidom_divide a) => Idom_divide a where {
};

class (Divide a) => Inverse a where {
  inverse :: a -> a;
};

class (Inverse a, Divide_trivial a,
        Ring_1_no_zero_divisors a) => Division_ring a where {
};

class (Division_ring a, Idom_divide a,
        Unique_Factorization.Ufd a) => Field a where {
};

class (Field a, Ring_char_0 a) => Field_char_0 a where {
};

class (Field a, Idom_abs_sgn a) => Field_abs_sgn a where {
};

class (Field_abs_sgn a, Field_char_0 a, Orderings.Unbounded_dense_linorder a,
        Linordered_idom a) => Linordered_field a where {
};

class Unit_factor a where {
  unit_factor :: a -> a;
};

class (Semidom_divide a, Unit_factor a) => Semidom_divide_unit_factor a where {
};

class (Algebraic_semidom a,
        Semidom_divide_unit_factor a) => Normalization_semidom a where {
  normalize :: a -> a;
};

class (Semidom_modulo a) => Euclidean_semiring a where {
  euclidean_size :: a -> Nat;
};

class (Normalization_semidom a) => Normalization_semidom_multiplicative a where {
};

nat_of_integer :: Integer -> Nat;
nat_of_integer k = Nat (Orderings.max (0 :: Integer) k);

nat :: Int -> Nat;
nat = nat_of_integer . integer_of_int;

suc :: Nat -> Nat;
suc n = plus_nat n one_nat;

funpow :: forall a. Nat -> (a -> a) -> a -> a;
funpow n f =
  (if equal_nat n zero_nat then id else f . funpow (minus_nat n one_nat) f);

dvd :: forall a. (Eq a, Semidom_modulo a) => a -> a -> Bool;
dvd a b = modulo b a == zero;

power :: forall a. (Power a) => a -> Nat -> a;
power a n =
  (if equal_nat n zero_nat then one
    else times a (power a (minus_nat n one_nat)));

numeral :: forall a. (Numeral a) => Num -> a;
numeral One = one;
numeral (Bit0 n) = let {
                     m = numeral n;
                   } in plus m m;
numeral (Bit1 n) = let {
                     m = numeral n;
                   } in plus (plus m m) one;

int_of_nat :: Nat -> Int;
int_of_nat n = Int_of_integer (integer_of_nat n);

divmod_nat :: Nat -> Nat -> (Nat, Nat);
divmod_nat m n =
  let {
    k = integer_of_nat m;
    l = integer_of_nat n;
  } in Product_Type.map_prod nat_of_integer nat_of_integer
         (if k == (0 :: Integer) then ((0 :: Integer), (0 :: Integer))
           else (if l == (0 :: Integer) then ((0 :: Integer), k)
                  else divMod ( k ) ( l )));

of_nat :: forall a. (Semiring_1 a) => Nat -> a;
of_nat n =
  (if equal_nat n zero_nat then zero
    else (case divmod_nat n (nat_of_integer (2 :: Integer)) of {
           (m, q) -> let {
                       ma = times (numeral (Bit0 One)) (of_nat m);
                     } in (if equal_nat q zero_nat then ma else plus ma one);
         }));

divide_int :: Int -> Int -> Int;
divide_int k l =
  Int_of_integer (divide_integer (integer_of_int k) (integer_of_int l));

}
