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
         less_eq_int, Abs_if, Semiring_char_0, Ring_char_0, Ceq(..),
         Set_impla(..), Set_impl(..), Idom_abs_sgn, Ordered_ab_semigroup_add,
         Strict_ordered_ab_semigroup_add, Ordered_cancel_ab_semigroup_add,
         Ordered_semigroup_mult_zero, Ordered_comm_monoid_add, Ordered_semiring,
         Ordered_semiring_0, Ordered_cancel_semiring,
         Ordered_ab_semigroup_add_imp_le, Strict_ordered_comm_monoid_add,
         Ordered_cancel_comm_monoid_add, Ordered_ab_semigroup_monoid_add_imp_le,
         Ordered_ab_group_add, Ordered_ring, Zero_less_one, Cenum(..),
         Ordered_semiring_strict, Linordered_ab_semigroup_add,
         Linordered_cancel_ab_semigroup_add, Linordered_semiring,
         Linordered_semiring_strict, Ordered_semiring_1,
         Ordered_semiring_1_strict, Ordered_semiring_1a, Linordered_semiring_1,
         Linordered_semiring_1_strict, Ordered_ab_group_add_abs,
         Linordered_ab_group_add, Linordered_ring, Linordered_ring_strict,
         Semiring_real_line, Semiring_1_real_line, Ordered_comm_semiring,
         Ordered_cancel_comm_semiring, Ordered_comm_semiring_strict,
         Linordered_comm_semiring_strict, Linordered_nonzero_semiring,
         Linordered_semidom, Ordered_comm_ring, Ordered_ring_abs,
         Linordered_idom, Ccompare(..), Nat, integer_of_nat, equal_nat,
         times_nat, one_nat, plus_nat, zero_nat, minus_nat, less_eq_nat,
         less_nat, apsnd, divide_nat, Divide(..), modulo_nat, Modulo(..),
         Interval, set_impl_nat, Divide_trivial, Semidom_divide,
         Semiring_modulo, Semiring_modulo_trivial, Algebraic_semidom,
         Semidom_modulo, Finite_UNIV(..), Card_UNIV(..), Cproper_interval(..),
         Generator, Color, Rbt(..), Mapping_rbt, Set_dlist, Set(..),
         list_of_dlist, collect, the, rbt_comp_lookup, lookup, member,
         less_eq_set, uminus_set, rbt_comp_insert, insertc, suc, nat_of_integer,
         rbt_comp_union_with_key, fold, foldc, is_none, size_list, map_prod,
         divmod_nat, entries, map_filter, inf_set, sup_set, set_eq,
         set_impl_set, emptya, set_empty, delete, insert, foldl, set, keys,
         keysa, bot_set, top_set, finite, card, comparator_list, compare_list,
         set_impl_list, Char, integer_of_char, equal_char, comparator_prod,
         compare_prod, set_impl_prod, product, Gcda(..), Gcd(..), Idom_divide,
         Ufd, Inverse(..), Division_ring, Field, Comm_monoid_gcd,
         Unit_factor(..), Semidom_divide_unit_factor, Normalization_semidom(..),
         Semiring_gcd, Idom_gcd, Ring_gcd, Semiring_Gcd, Field_char_0,
         Field_abs_sgn, Linordered_field, Normalization_semidom_multiplicative,
         Semiring_gcd_mult_normalize, Euclidean_semiring(..), Comp_fun_idem,
         Semilattice_set, nat, bex, nth, upt, ball, drop, find, last, take,
         foldb, image, foldr, map_option, those, membera, inserta, union,
         funpow, filtera, bind, hda, tla, butlast, extract, productc, set_Cons,
         listset, remdups, remove1, these, mapa, is_empty, distinct, superset,
         enumerate, partition, removeAll, replicate, implode, list_update,
         remdups_adj, max_sls, sup_cfi, rec_list, product_lists, curry,
         set_fold1, inter_list_set, list_all2, dvd, set_fold_cfi, swap,
         char_of_integer, explode, power, rbt_insert, rbt_lookup, gcd_int,
         lcm_int, rel_option, set_option, int_of_nat, of_nat, char_0x20,
         char_0x21, char_0x22, char_0x23, char_0x26, char_0x27, char_0x28,
         char_0x29, char_0x2A, char_0x2B, char_0x2C, char_0x2D, char_0x2F,
         char_0x30, char_0x31, char_0x32, char_0x33, char_0x34, char_0x35,
         char_0x36, char_0x37, char_0x38, char_0x39, char_0x3A, char_0x3B,
         char_0x3C, char_0x3D, char_0x3E, char_0x3F, char_0x41, char_0x42,
         char_0x43, char_0x44, char_0x45, char_0x46, char_0x47, char_0x48,
         char_0x49, char_0x4A, char_0x4B, char_0x4C, char_0x4D, char_0x4E,
         char_0x4F, char_0x50, char_0x51, char_0x52, char_0x53, char_0x54,
         char_0x55, char_0x56, char_0x57, char_0x58, char_0x59, char_0x5A,
         char_0x5B, char_0x5D, char_0x5F, char_0x61, char_0x62, char_0x63,
         char_0x64, char_0x65, char_0x66, char_0x67, char_0x68, char_0x69,
         char_0x6A, char_0x6B, char_0x6C, char_0x6D, char_0x6E, char_0x6F,
         char_0x70, char_0x71, char_0x72, char_0x73, char_0x74, char_0x75,
         char_0x76, char_0x77, char_0x78, char_0x79, char_0x7A, interval,
         sort_key, rbt_union, minus_set, rbt_delete, rbt_inserta, rbt_lookupa,
         rbt_bulkload, all_interval, sorted_list_of_set, divide_int)
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
import qualified Equality_Instances;
import qualified Efficient_Sort;
import qualified HOL;
import qualified Closure_Set;
import qualified Countable;
import qualified Compare;
import qualified Comparator;
import qualified Phantom_Type;
import qualified Quasi_Order;

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
  minusa :: a -> a -> a;
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
  minusa = minus_int;
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

class (Abs a, Minus a, Uminus a, Zero a, Quasi_Order.Ord a) => Abs_if a where {
};

instance Quasi_Order.Ord Int where {
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

instance Quasi_Order.Quasi_order Int where {
};

instance Quasi_Order.Weak_order Int where {
};

instance Quasi_Order.Preorder Int where {
};

instance Quasi_Order.Order Int where {
};

ceq_int :: Maybe (Int -> Int -> Bool);
ceq_int = Just equal_int;

class Ceq a where {
  ceq :: Maybe (a -> a -> Bool);
};

instance Ceq Int where {
  ceq = ceq_int;
};

data Set_impla = Set_Choose | Set_Collect | Set_DList | Set_RBT | Set_Monada;

set_impl_int :: Phantom_Type.Phantom Int Set_impla;
set_impl_int = Phantom_Type.Phantom Set_RBT;

class Set_impl a where {
  set_impl :: Phantom_Type.Phantom a Set_impla;
};

instance Set_impl Int where {
  set_impl = set_impl_int;
};

instance Quasi_Order.Linorder Int where {
};

class (Abs a, Sgn a, Idom a) => Idom_abs_sgn a where {
};

instance Idom_abs_sgn Int where {
};

class (Ab_semigroup_add a,
        Quasi_Order.Order a) => Ordered_ab_semigroup_add a where {
};

class (Ordered_ab_semigroup_add a) => Strict_ordered_ab_semigroup_add a where {
};

class (Cancel_ab_semigroup_add a,
        Strict_ordered_ab_semigroup_add a) => Ordered_cancel_ab_semigroup_add a where {
};

class (Semigroup_mult a, Quasi_Order.Order a,
        Mult_zero a) => Ordered_semigroup_mult_zero a where {
};

class (Comm_monoid_add a,
        Ordered_ab_semigroup_add a) => Ordered_comm_monoid_add a where {
};

class (Ordered_comm_monoid_add a, Semiring a) => Ordered_semiring a where {
};

class (Ordered_semigroup_mult_zero a, Ordered_semiring a,
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

instance Ordered_semigroup_mult_zero Int where {
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

class (Quasi_Order.Order a, Zero_neq_one a) => Zero_less_one a where {
};

instance Zero_less_one Int where {
};

cEnum_int :: Maybe ([Int], ((Int -> Bool) -> Bool, (Int -> Bool) -> Bool));
cEnum_int = Nothing;

class Cenum a where {
  cEnum :: Maybe ([a], ((a -> Bool) -> Bool, (a -> Bool) -> Bool));
};

instance Cenum Int where {
  cEnum = cEnum_int;
};

class (Ordered_cancel_ab_semigroup_add a, Ordered_semiring a,
        Semiring_0_cancel a) => Ordered_semiring_strict a where {
};

class (Ordered_ab_semigroup_add a,
        Quasi_Order.Linorder a) => Linordered_ab_semigroup_add a where {
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

class (Ordered_semiring_0 a, Semiring_1 a,
        Zero_less_one a) => Ordered_semiring_1a a where {
};

class (Ordered_semiring_1a a, Linordered_semiring a,
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

class (Ordered_semiring_0 a,
        Ordered_semiring_strict a) => Semiring_real_line a where {
};

class (Semiring_real_line a,
        Ordered_semiring_1 a) => Semiring_1_real_line a where {
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

class (Semiring_char_0 a, Quasi_Order.Linorder a, Comm_semiring_1 a,
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

class (Ring_char_0 a, Semiring_1_real_line a, Idom_abs_sgn a,
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

instance Ordered_semiring_1a Int where {
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

instance Semiring_real_line Int where {
};

instance Semiring_1_real_line Int where {
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

compare_int :: Int -> Int -> Comparator.Order;
compare_int = Comparator.comparator_of;

ccompare_int :: Maybe (Int -> Int -> Comparator.Order);
ccompare_int = Just compare_int;

class Ccompare a where {
  ccompare :: Maybe (a -> a -> Comparator.Order);
};

instance Ccompare Int where {
  ccompare = ccompare_int;
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

instance Quasi_Order.Ord Integer where {
  less_eq = (\ a b -> a <= b);
  less = (\ a b -> a < b);
};

minus_nat :: Nat -> Nat -> Nat;
minus_nat m n =
  Nat (Quasi_Order.max (0 :: Integer) (integer_of_nat m - integer_of_nat n));

instance Minus Nat where {
  minusa = minus_nat;
};

less_eq_nat :: Nat -> Nat -> Bool;
less_eq_nat m n = integer_of_nat m <= integer_of_nat n;

less_nat :: Nat -> Nat -> Bool;
less_nat m n = integer_of_nat m < integer_of_nat n;

instance Quasi_Order.Ord Nat where {
  less_eq = less_eq_nat;
  less = less_nat;
};

inf_nat :: Nat -> Nat -> Nat;
inf_nat = Quasi_Order.min;

instance Quasi_Order.Inf Nat where {
  inf = inf_nat;
};

sup_nat :: Nat -> Nat -> Nat;
sup_nat = Quasi_Order.max;

instance Quasi_Order.Sup Nat where {
  sup = sup_nat;
};

apsnd :: forall a b c. (a -> b) -> (c, a) -> (c, b);
apsnd f (x, y) = (x, f y);

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
                  else apsnd negate
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

class (Quasi_Order.Linorder a, Comm_semiring_1_cancel a) => Interval a where {
};

instance Cancel_semigroup_add Nat where {
};

instance Ab_semigroup_add Nat where {
};

instance Cancel_ab_semigroup_add Nat where {
};

instance Monoid_add Nat where {
};

instance Comm_monoid_add Nat where {
};

instance Cancel_comm_monoid_add Nat where {
};

instance Mult_zero Nat where {
};

instance Semigroup_mult Nat where {
};

instance Semiring Nat where {
};

instance Semiring_0 Nat where {
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

instance Monoid_mult Nat where {
};

instance Semiring_numeral Nat where {
};

instance Zero_neq_one Nat where {
};

instance Semiring_1 Nat where {
};

instance Semiring_1_cancel Nat where {
};

instance Comm_monoid_mult Nat where {
};

instance Comm_semiring_1 Nat where {
};

instance Comm_semiring_1_cancel Nat where {
};

instance Quasi_Order.Quasi_order Nat where {
};

instance Quasi_Order.Weak_order Nat where {
};

instance Quasi_Order.Preorder Nat where {
};

instance Quasi_Order.Order Nat where {
};

instance Quasi_Order.Linorder Nat where {
};

instance Interval Nat where {
};

instance Semiring_no_zero_divisors Nat where {
};

instance Semiring_1_no_zero_divisors Nat where {
};

instance Semidom Nat where {
};

compare_nat :: Nat -> Nat -> Comparator.Order;
compare_nat = Comparator.comparator_of;

instance Compare.Compare Nat where {
  compare = compare_nat;
};

instance Quasi_Order.Quasi_order_sup Nat where {
};

instance Quasi_Order.Quasi_semilattice_sup Nat where {
};

instance Quasi_Order.Semilattice_sup Nat where {
};

instance Quasi_Order.Semilattice_inf Nat where {
};

instance Quasi_Order.Lattice Nat where {
};

ceq_nat :: Maybe (Nat -> Nat -> Bool);
ceq_nat = Just equal_nat;

instance Ceq Nat where {
  ceq = ceq_nat;
};

set_impl_nat :: Phantom_Type.Phantom Nat Set_impla;
set_impl_nat = Phantom_Type.Phantom Set_RBT;

instance Set_impl Nat where {
  set_impl = set_impl_nat;
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

finite_UNIV_nat :: Phantom_Type.Phantom Nat Bool;
finite_UNIV_nat = Phantom_Type.Phantom False;

card_UNIV_nat :: Phantom_Type.Phantom Nat Nat;
card_UNIV_nat = Phantom_Type.Phantom zero_nat;

class Finite_UNIV a where {
  finite_UNIV :: Phantom_Type.Phantom a Bool;
};

class (Finite_UNIV a) => Card_UNIV a where {
  card_UNIV :: Phantom_Type.Phantom a Nat;
};

instance Finite_UNIV Nat where {
  finite_UNIV = finite_UNIV_nat;
};

instance Card_UNIV Nat where {
  card_UNIV = card_UNIV_nat;
};

cEnum_nat :: Maybe ([Nat], ((Nat -> Bool) -> Bool, (Nat -> Bool) -> Bool));
cEnum_nat = Nothing;

instance Cenum Nat where {
  cEnum = cEnum_nat;
};

instance Compare.Compare_order Nat where {
};

ccompare_nat :: Maybe (Nat -> Nat -> Comparator.Order);
ccompare_nat = Just compare_nat;

instance Ccompare Nat where {
  ccompare = ccompare_nat;
};

proper_interval_nat :: Maybe Nat -> Maybe Nat -> Bool;
proper_interval_nat no Nothing = True;
proper_interval_nat Nothing (Just x) = less_nat zero_nat x;
proper_interval_nat (Just x) (Just y) = less_nat one_nat (minus_nat y x);

cproper_interval_nat :: Maybe Nat -> Maybe Nat -> Bool;
cproper_interval_nat = proper_interval_nat;

class (Ccompare a) => Cproper_interval a where {
  cproper_interval :: Maybe a -> Maybe a -> Bool;
};

instance Cproper_interval Nat where {
  cproper_interval = cproper_interval_nat;
};

newtype Generator a b = Generator (b -> Bool, b -> (a, b));

generator :: forall a b. Generator a b -> (b -> Bool, b -> (a, b));
generator (Generator x) = x;

has_next :: forall a b. Generator a b -> b -> Bool;
has_next g = fst (generator g);

next :: forall a b. Generator a b -> b -> (a, b);
next g = snd (generator g);

sorted_list_subset_fusion ::
  forall a b c.
    (a -> a -> Bool) ->
      (a -> a -> Bool) -> Generator a b -> Generator a c -> b -> c -> Bool;
sorted_list_subset_fusion less eq g1 g2 s1 s2 =
  (if has_next g1 s1
    then (case next g1 s1 of {
           (x, s1a) ->
             has_next g2 s2 &&
               (case next g2 s2 of {
                 (y, s2a) ->
                   (if eq x y
                     then sorted_list_subset_fusion less eq g1 g2 s1a s2a
                     else less y x &&
                            sorted_list_subset_fusion less eq g1 g2 s1 s2a);
               });
         })
    else True);

list_all_fusion :: forall a b. Generator a b -> (a -> Bool) -> b -> Bool;
list_all_fusion g p s =
  (if has_next g s then (case next g s of {
                          (x, sa) -> p x && list_all_fusion g p sa;
                        })
    else True);

data Color = R | B;

data Rbt a b = Empty | Branch Color (Rbt a b) a b (Rbt a b);

rbt_keys_next ::
  forall a b. ([(a, Rbt a b)], Rbt a b) -> (a, ([(a, Rbt a b)], Rbt a b));
rbt_keys_next ((k, t) : kts, Empty) = (k, (kts, t));
rbt_keys_next (kts, Branch c l k v r) = rbt_keys_next ((k, r) : kts, l);

rbt_has_next :: forall a b c. ([(a, Rbt b c)], Rbt b c) -> Bool;
rbt_has_next ([], Empty) = False;
rbt_has_next (vb : vc, va) = True;
rbt_has_next (v, Branch vb vc vd ve vf) = True;

rbt_keys_generator :: forall a b. Generator a ([(a, Rbt a b)], Rbt a b);
rbt_keys_generator = Generator (rbt_has_next, rbt_keys_next);

newtype Mapping_rbt b a = Mapping_RBT (Rbt b a);

newtype Set_dlist a = Abs_dlist [a];

data Set a = Collect_set (a -> Bool) | DList_set (Set_dlist a)
  | RBT_set (Mapping_rbt a ()) | Set_Monad [a] | Complement (Set a);

list_of_dlist :: forall a. (Ceq a) => Set_dlist a -> [a];
list_of_dlist (Abs_dlist x) = x;

dlist_all :: forall a. (Ceq a) => (a -> Bool) -> Set_dlist a -> Bool;
dlist_all x xc = all x (list_of_dlist xc);

impl_of :: forall b a. (Ccompare b) => Mapping_rbt b a -> Rbt b a;
impl_of (Mapping_RBT x) = x;

rbt_init :: forall a b c. Rbt a b -> ([(c, Rbt a b)], Rbt a b);
rbt_init = (\ a -> ([], a));

init ::
  forall a b c. (Ccompare a) => Mapping_rbt a b -> ([(c, Rbt a b)], Rbt a b);
init xa = rbt_init (impl_of xa);

collect :: forall a. (Cenum a) => (a -> Bool) -> Set a;
collect p = (case cEnum of {
              Nothing -> Collect_set p;
              Just (enum, _) -> Set_Monad (filter p enum);
            });

list_member :: forall a. (a -> a -> Bool) -> [a] -> a -> Bool;
list_member equal [] y = False;
list_member equal (x : xs) y = equal x y || list_member equal xs y;

the :: forall a. Maybe a -> a;
the (Just x2) = x2;

memberc :: forall a. (Ceq a) => Set_dlist a -> a -> Bool;
memberc xa = list_member (the ceq) (list_of_dlist xa);

rbt_comp_lookup ::
  forall a b. (a -> a -> Comparator.Order) -> Rbt a b -> a -> Maybe b;
rbt_comp_lookup c Empty k = Nothing;
rbt_comp_lookup c (Branch uu l x y r) k =
  (case c k x of {
    Comparator.Eqa -> Just y;
    Comparator.Lt -> rbt_comp_lookup c l k;
    Comparator.Gt -> rbt_comp_lookup c r k;
  });

lookup :: forall a b. (Ccompare a) => Mapping_rbt a b -> a -> Maybe b;
lookup xa = rbt_comp_lookup (the ccompare) (impl_of xa);

memberb :: forall a. (Ccompare a) => Mapping_rbt a () -> a -> Bool;
memberb t x = lookup t x == Just ();

member :: forall a. (Ceq a, Ccompare a) => a -> Set a -> Bool;
member x (Set_Monad xs) =
  (case ceq of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "member Set_Monad: ceq = None" (\ _ -> member x (Set_Monad xs));
    Just eq -> list_member eq xs x;
  });
member xa (Complement x) = not (member xa x);
member x (RBT_set rbt) = memberb rbt x;
member x (DList_set dxs) = memberc dxs x;
member x (Collect_set a) = a x;

less_eq_set :: forall a. (Cenum a, Ceq a, Ccompare a) => Set a -> Set a -> Bool;
less_eq_set (RBT_set rbt1) (RBT_set rbt2) =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "subset RBT_set RBT_set: ccompare = None"
        (\ _ -> less_eq_set (RBT_set rbt1) (RBT_set rbt2));
    Just c ->
      (case ceq of {
        Nothing ->
          sorted_list_subset_fusion (Comparator.lt_of_comp c)
            (\ x y -> Comparator.equal_order (c x y) Comparator.Eqa)
            rbt_keys_generator rbt_keys_generator (init rbt1) (init rbt2);
        Just eq ->
          sorted_list_subset_fusion (Comparator.lt_of_comp c) eq
            rbt_keys_generator rbt_keys_generator (init rbt1) (init rbt2);
      });
  });
less_eq_set (Complement a1) (Complement a2) = less_eq_set a2 a1;
less_eq_set (Collect_set p) (Complement a) =
  less_eq_set a (collect (\ x -> not (p x)));
less_eq_set (RBT_set rbt) b =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "subset RBT_set1: ccompare = None" (\ _ -> less_eq_set (RBT_set rbt) b);
    Just _ -> list_all_fusion rbt_keys_generator (\ x -> member x b) (init rbt);
  });
less_eq_set (DList_set dxs) c =
  (case (ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "subset DList_set1: ceq = None" (\ _ -> less_eq_set (DList_set dxs) c);
    Just _ -> dlist_all (\ x -> member x c) dxs;
  });
less_eq_set (Set_Monad xs) c = all (\ x -> member x c) xs;

equal_set ::
  forall a. (Cenum a, Ceq a, Ccompare a, Eq a) => Set a -> Set a -> Bool;
equal_set a b = less_eq_set a b && less_eq_set b a;

instance (Cenum a, Ceq a, Ccompare a, Eq a) => Eq (Set a) where {
  a == b = equal_set a b;
};

uminus_set :: forall a. Set a -> Set a;
uminus_set (Complement b) = b;
uminus_set (Collect_set p) = Collect_set (\ x -> not (p x));
uminus_set a = Complement a;

balance :: forall a b. Rbt a b -> a -> b -> Rbt a b -> Rbt a b;
balance (Branch R a w x b) s t (Branch R c y z d) =
  Branch R (Branch B a w x b) s t (Branch B c y z d);
balance (Branch R (Branch R a w x b) s t c) y z Empty =
  Branch R (Branch B a w x b) s t (Branch B c y z Empty);
balance (Branch R (Branch R a w x b) s t c) y z (Branch B va vb vc vd) =
  Branch R (Branch B a w x b) s t (Branch B c y z (Branch B va vb vc vd));
balance (Branch R Empty w x (Branch R b s t c)) y z Empty =
  Branch R (Branch B Empty w x b) s t (Branch B c y z Empty);
balance (Branch R (Branch B va vb vc vd) w x (Branch R b s t c)) y z Empty =
  Branch R (Branch B (Branch B va vb vc vd) w x b) s t (Branch B c y z Empty);
balance (Branch R Empty w x (Branch R b s t c)) y z (Branch B va vb vc vd) =
  Branch R (Branch B Empty w x b) s t (Branch B c y z (Branch B va vb vc vd));
balance (Branch R (Branch B ve vf vg vh) w x (Branch R b s t c)) y z
  (Branch B va vb vc vd) =
  Branch R (Branch B (Branch B ve vf vg vh) w x b) s t
    (Branch B c y z (Branch B va vb vc vd));
balance Empty w x (Branch R b s t (Branch R c y z d)) =
  Branch R (Branch B Empty w x b) s t (Branch B c y z d);
balance (Branch B va vb vc vd) w x (Branch R b s t (Branch R c y z d)) =
  Branch R (Branch B (Branch B va vb vc vd) w x b) s t (Branch B c y z d);
balance Empty w x (Branch R (Branch R b s t c) y z Empty) =
  Branch R (Branch B Empty w x b) s t (Branch B c y z Empty);
balance Empty w x (Branch R (Branch R b s t c) y z (Branch B va vb vc vd)) =
  Branch R (Branch B Empty w x b) s t (Branch B c y z (Branch B va vb vc vd));
balance (Branch B va vb vc vd) w x (Branch R (Branch R b s t c) y z Empty) =
  Branch R (Branch B (Branch B va vb vc vd) w x b) s t (Branch B c y z Empty);
balance (Branch B va vb vc vd) w x
  (Branch R (Branch R b s t c) y z (Branch B ve vf vg vh)) =
  Branch R (Branch B (Branch B va vb vc vd) w x b) s t
    (Branch B c y z (Branch B ve vf vg vh));
balance Empty s t Empty = Branch B Empty s t Empty;
balance Empty s t (Branch B va vb vc vd) =
  Branch B Empty s t (Branch B va vb vc vd);
balance Empty s t (Branch v Empty vb vc Empty) =
  Branch B Empty s t (Branch v Empty vb vc Empty);
balance Empty s t (Branch v (Branch B ve vf vg vh) vb vc Empty) =
  Branch B Empty s t (Branch v (Branch B ve vf vg vh) vb vc Empty);
balance Empty s t (Branch v Empty vb vc (Branch B vf vg vh vi)) =
  Branch B Empty s t (Branch v Empty vb vc (Branch B vf vg vh vi));
balance Empty s t (Branch v (Branch B ve vj vk vl) vb vc (Branch B vf vg vh vi))
  = Branch B Empty s t
      (Branch v (Branch B ve vj vk vl) vb vc (Branch B vf vg vh vi));
balance (Branch B va vb vc vd) s t Empty =
  Branch B (Branch B va vb vc vd) s t Empty;
balance (Branch B va vb vc vd) s t (Branch B ve vf vg vh) =
  Branch B (Branch B va vb vc vd) s t (Branch B ve vf vg vh);
balance (Branch B va vb vc vd) s t (Branch v Empty vf vg Empty) =
  Branch B (Branch B va vb vc vd) s t (Branch v Empty vf vg Empty);
balance (Branch B va vb vc vd) s t (Branch v (Branch B vi vj vk vl) vf vg Empty)
  = Branch B (Branch B va vb vc vd) s t
      (Branch v (Branch B vi vj vk vl) vf vg Empty);
balance (Branch B va vb vc vd) s t (Branch v Empty vf vg (Branch B vj vk vl vm))
  = Branch B (Branch B va vb vc vd) s t
      (Branch v Empty vf vg (Branch B vj vk vl vm));
balance (Branch B va vb vc vd) s t
  (Branch v (Branch B vi vn vo vp) vf vg (Branch B vj vk vl vm)) =
  Branch B (Branch B va vb vc vd) s t
    (Branch v (Branch B vi vn vo vp) vf vg (Branch B vj vk vl vm));
balance (Branch v Empty vb vc Empty) s t Empty =
  Branch B (Branch v Empty vb vc Empty) s t Empty;
balance (Branch v Empty vb vc (Branch B ve vf vg vh)) s t Empty =
  Branch B (Branch v Empty vb vc (Branch B ve vf vg vh)) s t Empty;
balance (Branch v (Branch B vf vg vh vi) vb vc Empty) s t Empty =
  Branch B (Branch v (Branch B vf vg vh vi) vb vc Empty) s t Empty;
balance (Branch v (Branch B vf vg vh vi) vb vc (Branch B ve vj vk vl)) s t Empty
  = Branch B (Branch v (Branch B vf vg vh vi) vb vc (Branch B ve vj vk vl)) s t
      Empty;
balance (Branch v Empty vf vg Empty) s t (Branch B va vb vc vd) =
  Branch B (Branch v Empty vf vg Empty) s t (Branch B va vb vc vd);
balance (Branch v Empty vf vg (Branch B vi vj vk vl)) s t (Branch B va vb vc vd)
  = Branch B (Branch v Empty vf vg (Branch B vi vj vk vl)) s t
      (Branch B va vb vc vd);
balance (Branch v (Branch B vj vk vl vm) vf vg Empty) s t (Branch B va vb vc vd)
  = Branch B (Branch v (Branch B vj vk vl vm) vf vg Empty) s t
      (Branch B va vb vc vd);
balance (Branch v (Branch B vj vk vl vm) vf vg (Branch B vi vn vo vp)) s t
  (Branch B va vb vc vd) =
  Branch B (Branch v (Branch B vj vk vl vm) vf vg (Branch B vi vn vo vp)) s t
    (Branch B va vb vc vd);

rbt_comp_ins ::
  forall a b.
    (a -> a -> Comparator.Order) ->
      (a -> b -> b -> b) -> a -> b -> Rbt a b -> Rbt a b;
rbt_comp_ins c f k v Empty = Branch R Empty k v Empty;
rbt_comp_ins c f k v (Branch B l x y r) =
  (case c k x of {
    Comparator.Eqa -> Branch B l x (f k y v) r;
    Comparator.Lt -> balance (rbt_comp_ins c f k v l) x y r;
    Comparator.Gt -> balance l x y (rbt_comp_ins c f k v r);
  });
rbt_comp_ins c f k v (Branch R l x y r) =
  (case c k x of {
    Comparator.Eqa -> Branch R l x (f k y v) r;
    Comparator.Lt -> Branch R (rbt_comp_ins c f k v l) x y r;
    Comparator.Gt -> Branch R l x y (rbt_comp_ins c f k v r);
  });

paint :: forall a b. Color -> Rbt a b -> Rbt a b;
paint c Empty = Empty;
paint c (Branch uu l k v r) = Branch c l k v r;

rbt_comp_insert_with_key ::
  forall a b.
    (a -> a -> Comparator.Order) ->
      (a -> b -> b -> b) -> a -> b -> Rbt a b -> Rbt a b;
rbt_comp_insert_with_key c f k v t = paint B (rbt_comp_ins c f k v t);

rbt_comp_insert ::
  forall a b. (a -> a -> Comparator.Order) -> a -> b -> Rbt a b -> Rbt a b;
rbt_comp_insert c = rbt_comp_insert_with_key c (\ _ _ nv -> nv);

insertc ::
  forall a b. (Ccompare a) => a -> b -> Mapping_rbt a b -> Mapping_rbt a b;
insertc xc xd xe =
  Mapping_RBT (rbt_comp_insert (the ccompare) xc xd (impl_of xe));

rbt_baliR :: forall a b. Rbt a b -> a -> b -> Rbt a b -> Rbt a b;
rbt_baliR t1 ab bb (Branch R t2 aa ba (Branch R t3 a b t4)) =
  Branch R (Branch B t1 ab bb t2) aa ba (Branch B t3 a b t4);
rbt_baliR t1 ab bb (Branch R (Branch R t2 aa ba t3) a b Empty) =
  Branch R (Branch B t1 ab bb t2) aa ba (Branch B t3 a b Empty);
rbt_baliR t1 ab bb (Branch R (Branch R t2 aa ba t3) a b (Branch B va vb vc vd))
  = Branch R (Branch B t1 ab bb t2) aa ba
      (Branch B t3 a b (Branch B va vb vc vd));
rbt_baliR t1 a b Empty = Branch B t1 a b Empty;
rbt_baliR t1 a b (Branch B va vb vc vd) =
  Branch B t1 a b (Branch B va vb vc vd);
rbt_baliR t1 a b (Branch v Empty vb vc Empty) =
  Branch B t1 a b (Branch v Empty vb vc Empty);
rbt_baliR t1 a b (Branch v (Branch B ve vf vg vh) vb vc Empty) =
  Branch B t1 a b (Branch v (Branch B ve vf vg vh) vb vc Empty);
rbt_baliR t1 a b (Branch v Empty vb vc (Branch B vf vg vh vi)) =
  Branch B t1 a b (Branch v Empty vb vc (Branch B vf vg vh vi));
rbt_baliR t1 a b (Branch v (Branch B ve vj vk vl) vb vc (Branch B vf vg vh vi))
  = Branch B t1 a b
      (Branch v (Branch B ve vj vk vl) vb vc (Branch B vf vg vh vi));

equal_color :: Color -> Color -> Bool;
equal_color R B = False;
equal_color B R = False;
equal_color B B = True;
equal_color R R = True;

suc :: Nat -> Nat;
suc n = plus_nat n one_nat;

bheight :: forall a b. Rbt a b -> Nat;
bheight Empty = zero_nat;
bheight (Branch c lt k v rt) =
  (if equal_color c B then suc (bheight lt) else bheight lt);

rbt_joinR :: forall a b. Rbt a b -> a -> b -> Rbt a b -> Rbt a b;
rbt_joinR l a b r =
  (if less_eq_nat (bheight l) (bheight r) then Branch R l a b r
    else (case l of {
           Branch R la ab ba ra -> Branch R la ab ba (rbt_joinR ra a b r);
           Branch B la ab ba ra -> rbt_baliR la ab ba (rbt_joinR ra a b r);
         }));

rbt_baliL :: forall a b. Rbt a b -> a -> b -> Rbt a b -> Rbt a b;
rbt_baliL (Branch R (Branch R t1 ab bb t2) aa ba t3) a b t4 =
  Branch R (Branch B t1 ab bb t2) aa ba (Branch B t3 a b t4);
rbt_baliL (Branch R Empty ab bb (Branch R t2 aa ba t3)) a b t4 =
  Branch R (Branch B Empty ab bb t2) aa ba (Branch B t3 a b t4);
rbt_baliL (Branch R (Branch B va vb vc vd) ab bb (Branch R t2 aa ba t3)) a b t4
  = Branch R (Branch B (Branch B va vb vc vd) ab bb t2) aa ba
      (Branch B t3 a b t4);
rbt_baliL Empty a b t2 = Branch B Empty a b t2;
rbt_baliL (Branch B va vb vc vd) a b t2 =
  Branch B (Branch B va vb vc vd) a b t2;
rbt_baliL (Branch v Empty vb vc Empty) a b t2 =
  Branch B (Branch v Empty vb vc Empty) a b t2;
rbt_baliL (Branch v Empty vb vc (Branch B ve vf vg vh)) a b t2 =
  Branch B (Branch v Empty vb vc (Branch B ve vf vg vh)) a b t2;
rbt_baliL (Branch v (Branch B vf vg vh vi) vb vc Empty) a b t2 =
  Branch B (Branch v (Branch B vf vg vh vi) vb vc Empty) a b t2;
rbt_baliL (Branch v (Branch B vf vg vh vi) vb vc (Branch B ve vj vk vl)) a b t2
  = Branch B (Branch v (Branch B vf vg vh vi) vb vc (Branch B ve vj vk vl)) a b
      t2;

rbt_joinL :: forall a b. Rbt a b -> a -> b -> Rbt a b -> Rbt a b;
rbt_joinL l a b r =
  (if less_eq_nat (bheight r) (bheight l) then Branch R l a b r
    else (case r of {
           Branch R la ab ba ra -> Branch R (rbt_joinL l a b la) ab ba ra;
           Branch B la ab ba ra -> rbt_baliL (rbt_joinL l a b la) ab ba ra;
         }));

rbt_join :: forall a b. Rbt a b -> a -> b -> Rbt a b -> Rbt a b;
rbt_join l a b r =
  let {
    bhl = bheight l;
    bhr = bheight r;
  } in (if less_nat bhr bhl then paint B (rbt_joinR l a b r)
         else (if less_nat bhl bhr then paint B (rbt_joinL l a b r)
                else Branch B l a b r));

rbt_split_comp ::
  forall a b.
    (a -> a -> Comparator.Order) ->
      Rbt a b -> a -> (Rbt a b, (Maybe b, Rbt a b));
rbt_split_comp c Empty k = (Empty, (Nothing, Empty));
rbt_split_comp c (Branch uu l a b r) x =
  (case c x a of {
    Comparator.Eqa -> (l, (Just b, r));
    Comparator.Lt -> (case rbt_split_comp c l x of {
                       (l1, (beta, l2)) -> (l1, (beta, rbt_join l2 a b r));
                     });
    Comparator.Gt -> (case rbt_split_comp c r x of {
                       (r1, (beta, r2)) -> (rbt_join l a b r1, (beta, r2));
                     });
  });

nat_of_integer :: Integer -> Nat;
nat_of_integer k = Nat (Quasi_Order.max (0 :: Integer) k);

folda :: forall a b c. (a -> b -> c -> c) -> Rbt a b -> c -> c;
folda f Empty x = x;
folda f (Branch c lt k v rt) x = folda f rt (f k v (folda f lt x));

rbt_comp_union_swap_rec ::
  forall a b.
    (a -> a -> Comparator.Order) ->
      (a -> b -> b -> b) -> Bool -> Rbt a b -> Rbt a b -> Rbt a b;
rbt_comp_union_swap_rec c f gamma t1 t2 =
  let {
    bh1 = bheight t1;
    bh2 = bheight t2;
  } in (case (if less_nat bh1 bh2 then (not gamma, (t1, (bh1, (t2, bh2))))
               else (gamma, (t2, (bh2, (t1, bh1)))))
         of {
         (gammaa, (t2a, (bh2a, (t1a, _)))) ->
           let {
             fa = (if gammaa then (\ k v va -> f k va v) else f);
           } in (if less_nat bh2a (nat_of_integer (4 :: Integer))
                  then folda (rbt_comp_insert_with_key c fa) t2a t1a
                  else (case t1a of {
                         Empty -> t2a;
                         Branch _ l1 a b r1 ->
                           (case rbt_split_comp c t2a a of {
                             (l2, (beta, r2)) ->
                               rbt_join
                                 (rbt_comp_union_swap_rec c f gammaa l1 l2) a
                                 (case beta of {
                                   Nothing -> b;
                                   Just ca -> fa a b ca;
                                 })
                                 (rbt_comp_union_swap_rec c f gammaa r1 r2);
                           });
                       }));
       });

rbt_comp_union_with_key ::
  forall a b.
    (a -> a -> Comparator.Order) ->
      (a -> b -> b -> b) -> Rbt a b -> Rbt a b -> Rbt a b;
rbt_comp_union_with_key c f t1 t2 =
  paint B (rbt_comp_union_swap_rec c f False t1 t2);

join ::
  forall a b.
    (Ccompare a) => (a -> b -> b -> b) ->
                      Mapping_rbt a b -> Mapping_rbt a b -> Mapping_rbt a b;
join xc xd xe =
  Mapping_RBT
    (rbt_comp_union_with_key (the ccompare) xc (impl_of xd) (impl_of xe));

list_insert :: forall a. (a -> a -> Bool) -> a -> [a] -> [a];
list_insert equal x xs = (if list_member equal xs x then xs else x : xs);

insertb :: forall a. (Ceq a) => a -> Set_dlist a -> Set_dlist a;
insertb xb xc = Abs_dlist (list_insert (the ceq) xb (list_of_dlist xc));

fold :: forall a b. (a -> b -> b) -> [a] -> b -> b;
fold f [] s = s;
fold f (x : xs) s = fold f xs (f x s);

foldc :: forall a b. (Ceq a) => (a -> b -> b) -> Set_dlist a -> b -> b;
foldc x xc = fold x (list_of_dlist xc);

uniona :: forall a. (Ceq a) => Set_dlist a -> Set_dlist a -> Set_dlist a;
uniona = foldc insertb;

is_none :: forall a. Maybe a -> Bool;
is_none Nothing = True;
is_none (Just x) = False;

inter_list ::
  forall a. (Ccompare a) => Mapping_rbt a () -> [a] -> Mapping_rbt a ();
inter_list xb xc =
  Mapping_RBT
    (fold (\ k -> rbt_comp_insert (the ccompare) k ())
      (filter
        (\ x -> not (is_none (rbt_comp_lookup (the ccompare) (impl_of xb) x)))
        xc)
      Empty);

length_tailrec :: forall a. [a] -> Nat -> Nat;
length_tailrec [] n = n;
length_tailrec (x : xs) n = length_tailrec xs (suc n);

size_list :: forall a. [a] -> Nat;
size_list xs = length_tailrec xs zero_nat;

map_prod :: forall a b c d. (a -> b) -> (c -> d) -> (a, c) -> (b, d);
map_prod f g (a, b) = (f a, g b);

divmod_nat :: Nat -> Nat -> (Nat, Nat);
divmod_nat m n =
  let {
    k = integer_of_nat m;
    l = integer_of_nat n;
  } in map_prod nat_of_integer nat_of_integer
         (if k == (0 :: Integer) then ((0 :: Integer), (0 :: Integer))
           else (if l == (0 :: Integer) then ((0 :: Integer), k)
                  else divMod ( k ) ( l )));

apfst :: forall a b c. (a -> b) -> (a, c) -> (b, c);
apfst f (x, y) = (f x, y);

rbtreeify_g :: forall a b. Nat -> [(a, b)] -> (Rbt a b, [(a, b)]);
rbtreeify_g n kvs =
  (if equal_nat n zero_nat || equal_nat n one_nat then (Empty, kvs)
    else (case divmod_nat n (nat_of_integer (2 :: Integer)) of {
           (na, r) ->
             (if equal_nat r zero_nat
               then (case rbtreeify_g na kvs of {
                      (t1, (k, v) : kvsa) ->
                        apfst (Branch B t1 k v) (rbtreeify_g na kvsa);
                    })
               else (case rbtreeify_f na kvs of {
                      (t1, (k, v) : kvsa) ->
                        apfst (Branch B t1 k v) (rbtreeify_g na kvsa);
                    }));
         }));

rbtreeify_f :: forall a b. Nat -> [(a, b)] -> (Rbt a b, [(a, b)]);
rbtreeify_f n kvs =
  (if equal_nat n zero_nat then (Empty, kvs)
    else (if equal_nat n one_nat
           then (case kvs of {
                  (k, v) : kvsa -> (Branch R Empty k v Empty, kvsa);
                })
           else (case divmod_nat n (nat_of_integer (2 :: Integer)) of {
                  (na, r) ->
                    (if equal_nat r zero_nat
                      then (case rbtreeify_f na kvs of {
                             (t1, (k, v) : kvsa) ->
                               apfst (Branch B t1 k v) (rbtreeify_g na kvsa);
                           })
                      else (case rbtreeify_f na kvs of {
                             (t1, (k, v) : kvsa) ->
                               apfst (Branch B t1 k v) (rbtreeify_f na kvsa);
                           }));
                })));

rbtreeify :: forall a b. [(a, b)] -> Rbt a b;
rbtreeify kvs = fst (rbtreeify_g (suc (size_list kvs)) kvs);

gen_entries :: forall a b. [((a, b), Rbt a b)] -> Rbt a b -> [(a, b)];
gen_entries [] Empty = [];
gen_entries ((kv, t) : kvts) Empty = kv : gen_entries kvts t;
gen_entries kvts (Branch c l k v r) = gen_entries (((k, v), r) : kvts) l;

entries :: forall a b. Rbt a b -> [(a, b)];
entries = gen_entries [];

filterc ::
  forall a b.
    (Ccompare a) => ((a, b) -> Bool) -> Mapping_rbt a b -> Mapping_rbt a b;
filterc xb xc = Mapping_RBT (rbtreeify (filter xb (entries (impl_of xc))));

map_filter :: forall a b. (a -> Maybe b) -> [a] -> [b];
map_filter f [] = [];
map_filter f (x : xs) = (case f x of {
                          Nothing -> map_filter f xs;
                          Just y -> y : map_filter f xs;
                        });

map_filter_comp_inter ::
  forall a b c d.
    (a -> a -> Comparator.Order) ->
      (a -> b -> c -> d) -> Rbt a b -> Rbt a c -> [(a, d)];
map_filter_comp_inter c f t1 t2 =
  map_filter (\ (k, v) -> (case rbt_comp_lookup c t1 k of {
                            Nothing -> Nothing;
                            Just va -> Just (k, f k va v);
                          }))
    (entries t2);

is_rbt_empty :: forall a b. Rbt a b -> Bool;
is_rbt_empty t = (case t of {
                   Empty -> True;
                   Branch _ _ _ _ _ -> False;
                 });

rbt_split_min :: forall a b. Rbt a b -> (a, (b, Rbt a b));
rbt_split_min Empty = error "undefined";
rbt_split_min (Branch uu l a b r) =
  (if is_rbt_empty l then (a, (b, r))
    else (case rbt_split_min l of {
           (aa, (ba, la)) -> (aa, (ba, rbt_join la a b r));
         }));

rbt_join2 :: forall a b. Rbt a b -> Rbt a b -> Rbt a b;
rbt_join2 l r =
  (if is_rbt_empty r then l else (case rbt_split_min r of {
                                   (a, (b, c)) -> rbt_join l a b c;
                                 }));

rbt_comp_inter_swap_rec ::
  forall a b.
    (a -> a -> Comparator.Order) ->
      (a -> b -> b -> b) -> Bool -> Rbt a b -> Rbt a b -> Rbt a b;
rbt_comp_inter_swap_rec c f gamma t1 t2 =
  let {
    bh1 = bheight t1;
    bh2 = bheight t2;
  } in (case (if less_nat bh1 bh2 then (not gamma, (t1, (bh1, (t2, bh2))))
               else (gamma, (t2, (bh2, (t1, bh1)))))
         of {
         (gammaa, (t2a, (bh2a, (t1a, _)))) ->
           let {
             fa = (if gammaa then (\ k v va -> f k va v) else f);
           } in (if less_nat bh2a (nat_of_integer (4 :: Integer))
                  then rbtreeify (map_filter_comp_inter c fa t1a t2a)
                  else (case t1a of {
                         Empty -> Empty;
                         Branch _ l1 a b r1 ->
                           (case rbt_split_comp c t2a a of {
                             (l2, (beta, r2)) ->
                               let {
                                 l = rbt_comp_inter_swap_rec c f gammaa l1 l2;
                                 r = rbt_comp_inter_swap_rec c f gammaa r1 r2;
                               } in (case beta of {
                                      Nothing -> rbt_join2 l r;
                                      Just ba -> rbt_join l a (fa a b ba) r;
                                    });
                           });
                       }));
       });

rbt_comp_inter_with_key ::
  forall a b.
    (a -> a -> Comparator.Order) ->
      (a -> b -> b -> b) -> Rbt a b -> Rbt a b -> Rbt a b;
rbt_comp_inter_with_key c f t1 t2 =
  paint B (rbt_comp_inter_swap_rec c f False t1 t2);

meet ::
  forall a b.
    (Ccompare a) => (a -> b -> b -> b) ->
                      Mapping_rbt a b -> Mapping_rbt a b -> Mapping_rbt a b;
meet xc xd xe =
  Mapping_RBT
    (rbt_comp_inter_with_key (the ccompare) xc (impl_of xd) (impl_of xe));

filterb :: forall a. (Ceq a) => (a -> Bool) -> Set_dlist a -> Set_dlist a;
filterb xb xc = Abs_dlist (filter xb (list_of_dlist xc));

inf_set :: forall a. (Ceq a, Ccompare a) => Set a -> Set a -> Set a;
inf_set (RBT_set rbt1) (Set_Monad xs) =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "inter RBT_set Set_Monad: ccompare = None"
        (\ _ -> inf_set (RBT_set rbt1) (Set_Monad xs));
    Just _ -> RBT_set (inter_list rbt1 xs);
  });
inf_set (Set_Monad xs) (RBT_set rbt1) =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "inter Set_Monad RBT_set: ccompare = None"
        (\ _ -> inf_set (RBT_set rbt1) (Set_Monad xs));
    Just _ -> RBT_set (inter_list rbt1 xs);
  });
inf_set (Set_Monad xs) (DList_set dxs2) =
  (case ceq of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "inter Set_Monad DList_set: ceq = None"
        (\ _ -> inf_set (Set_Monad xs) (DList_set dxs2));
    Just eq -> DList_set (filterb (list_member eq xs) dxs2);
  });
inf_set (Set_Monad xs1) (Set_Monad xs2) =
  (case ceq of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "inter Set_Monad Set_Monad: ceq = None"
        (\ _ -> inf_set (Set_Monad xs1) (Set_Monad xs2));
    Just eq -> Set_Monad (filter (list_member eq xs2) xs1);
  });
inf_set (RBT_set rbt) (DList_set dxs) =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "inter RBT_set DList_set: ccompare = None"
        (\ _ -> inf_set (RBT_set rbt) (DList_set dxs));
    Just _ ->
      (case (ceq :: Maybe (a -> a -> Bool)) of {
        Nothing ->
          (error :: forall a. String -> (() -> a) -> a)
            "inter RBT_set DList_set: ceq = None"
            (\ _ -> inf_set (RBT_set rbt) (DList_set dxs));
        Just _ -> RBT_set (inter_list rbt (list_of_dlist dxs));
      });
  });
inf_set (RBT_set rbt1) (RBT_set rbt2) =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "inter RBT_set RBT_set: ccompare = None"
        (\ _ -> inf_set (RBT_set rbt1) (RBT_set rbt2));
    Just _ -> RBT_set (meet (\ _ _ -> id) rbt1 rbt2);
  });
inf_set (DList_set dxs1) (Set_Monad xs) =
  (case ceq of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "inter DList_set Set_Monad: ceq = None"
        (\ _ -> inf_set (DList_set dxs1) (Set_Monad xs));
    Just eq -> DList_set (filterb (list_member eq xs) dxs1);
  });
inf_set (DList_set dxs1) (DList_set dxs2) =
  (case (ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "inter DList_set DList_set: ceq = None"
        (\ _ -> inf_set (DList_set dxs1) (DList_set dxs2));
    Just _ -> DList_set (filterb (memberc dxs2) dxs1);
  });
inf_set (DList_set dxs) (RBT_set rbt) =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "inter DList_set RBT_set: ccompare = None"
        (\ _ -> inf_set (DList_set dxs) (RBT_set rbt));
    Just _ ->
      (case (ceq :: Maybe (a -> a -> Bool)) of {
        Nothing ->
          (error :: forall a. String -> (() -> a) -> a)
            "inter DList_set RBT_set: ceq = None"
            (\ _ -> inf_set (DList_set dxs) (RBT_set rbt));
        Just _ -> RBT_set (inter_list rbt (list_of_dlist dxs));
      });
  });
inf_set (Complement ba) (Complement b) = Complement (sup_set ba b);
inf_set g (RBT_set rbt2) =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "inter RBT_set2: ccompare = None" (\ _ -> inf_set g (RBT_set rbt2));
    Just _ -> RBT_set (filterc ((\ x -> member x g) . fst) rbt2);
  });
inf_set (RBT_set rbt1) g =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "inter RBT_set1: ccompare = None" (\ _ -> inf_set (RBT_set rbt1) g);
    Just _ -> RBT_set (filterc ((\ x -> member x g) . fst) rbt1);
  });
inf_set h (DList_set dxs2) =
  (case (ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "inter DList_set2: ceq = None" (\ _ -> inf_set h (DList_set dxs2));
    Just _ -> DList_set (filterb (\ x -> member x h) dxs2);
  });
inf_set (DList_set dxs1) h =
  (case (ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "inter DList_set1: ceq = None" (\ _ -> inf_set (DList_set dxs1) h);
    Just _ -> DList_set (filterb (\ x -> member x h) dxs1);
  });
inf_set i (Set_Monad xs) = Set_Monad (filter (\ x -> member x i) xs);
inf_set (Set_Monad xs) i = Set_Monad (filter (\ x -> member x i) xs);
inf_set j (Collect_set a) = Collect_set (\ x -> a x && member x j);
inf_set (Collect_set a) j = Collect_set (\ x -> a x && member x j);

sup_set :: forall a. (Ceq a, Ccompare a) => Set a -> Set a -> Set a;
sup_set ba (Complement b) = Complement (inf_set (uminus_set ba) b);
sup_set (Complement ba) b = Complement (inf_set ba (uminus_set b));
sup_set (RBT_set rbt1) (RBT_set rbt2) =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "union RBT_set RBT_set: ccompare = None"
        (\ _ -> sup_set (RBT_set rbt1) (RBT_set rbt2));
    Just _ -> RBT_set (join (\ _ _ -> id) rbt1 rbt2);
  });
sup_set (RBT_set rbt) (DList_set dxs) =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "union RBT_set DList_set: ccompare = None"
        (\ _ -> sup_set (RBT_set rbt) (DList_set dxs));
    Just _ ->
      (case (ceq :: Maybe (a -> a -> Bool)) of {
        Nothing ->
          (error :: forall a. String -> (() -> a) -> a)
            "union RBT_set DList_set: ceq = None"
            (\ _ -> sup_set (RBT_set rbt) (DList_set dxs));
        Just _ -> RBT_set (foldc (\ k -> insertc k ()) dxs rbt);
      });
  });
sup_set (DList_set dxs) (RBT_set rbt) =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "union DList_set RBT_set: ccompare = None"
        (\ _ -> sup_set (RBT_set rbt) (DList_set dxs));
    Just _ ->
      (case (ceq :: Maybe (a -> a -> Bool)) of {
        Nothing ->
          (error :: forall a. String -> (() -> a) -> a)
            "union DList_set RBT_set: ceq = None"
            (\ _ -> sup_set (RBT_set rbt) (DList_set dxs));
        Just _ -> RBT_set (foldc (\ k -> insertc k ()) dxs rbt);
      });
  });
sup_set (DList_set dxs1) (DList_set dxs2) =
  (case (ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "union DList_set DList_set: ceq = None"
        (\ _ -> sup_set (DList_set dxs1) (DList_set dxs2));
    Just _ -> DList_set (uniona dxs1 dxs2);
  });
sup_set (Set_Monad zs) (RBT_set rbt2) =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "union Set_Monad RBT_set: ccompare = None"
        (\ _ -> sup_set (Set_Monad zs) (RBT_set rbt2));
    Just _ -> RBT_set (fold (\ k -> insertc k ()) zs rbt2);
  });
sup_set (RBT_set rbt1) (Set_Monad zs) =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "union RBT_set Set_Monad: ccompare = None"
        (\ _ -> sup_set (RBT_set rbt1) (Set_Monad zs));
    Just _ -> RBT_set (fold (\ k -> insertc k ()) zs rbt1);
  });
sup_set (Set_Monad ws) (DList_set dxs2) =
  (case (ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "union Set_Monad DList_set: ceq = None"
        (\ _ -> sup_set (Set_Monad ws) (DList_set dxs2));
    Just _ -> DList_set (fold insertb ws dxs2);
  });
sup_set (DList_set dxs1) (Set_Monad ws) =
  (case (ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "union DList_set Set_Monad: ceq = None"
        (\ _ -> sup_set (DList_set dxs1) (Set_Monad ws));
    Just _ -> DList_set (fold insertb ws dxs1);
  });
sup_set (Set_Monad xs) (Set_Monad ys) = Set_Monad (xs ++ ys);
sup_set b (Collect_set a) = Collect_set (\ x -> a x || member x b);
sup_set (Collect_set a) b = Collect_set (\ x -> a x || member x b);

instance (Ceq a, Ccompare a) => Quasi_Order.Inf (Set a) where {
  inf = inf_set;
};

instance (Ceq a, Ccompare a) => Quasi_Order.Sup (Set a) where {
  sup = sup_set;
};

less_set :: forall a. (Cenum a, Ceq a, Ccompare a) => Set a -> Set a -> Bool;
less_set a b = less_eq_set a b && not (less_eq_set b a);

instance (Cenum a, Ceq a, Ccompare a) => Quasi_Order.Ord (Set a) where {
  less_eq = less_eq_set;
  less = less_set;
};

instance (Cenum a, Ceq a, Ccompare a) => Quasi_Order.Quasi_order (Set a) where {
};

instance (Cenum a, Ceq a, Ccompare a) => Quasi_Order.Weak_order (Set a) where {
};

instance (Cenum a, Ceq a, Ccompare a) => Quasi_Order.Preorder (Set a) where {
};

instance (Cenum a, Ceq a, Ccompare a) => Quasi_Order.Order (Set a) where {
};

instance (Cenum a, Ceq a,
           Ccompare a) => Quasi_Order.Quasi_order_sup (Set a) where {
};

instance (Cenum a, Ceq a,
           Ccompare a) => Quasi_Order.Quasi_semilattice_sup (Set a) where {
};

instance (Cenum a, Ceq a,
           Ccompare a) => Quasi_Order.Semilattice_sup (Set a) where {
};

instance (Cenum a, Ceq a,
           Ccompare a) => Quasi_Order.Semilattice_inf (Set a) where {
};

instance (Cenum a, Ceq a, Ccompare a) => Quasi_Order.Lattice (Set a) where {
};

list_all2_fusion ::
  forall a b c d.
    (a -> b -> Bool) -> Generator a c -> Generator b d -> c -> d -> Bool;
list_all2_fusion p g1 g2 s1 s2 =
  (if has_next g1 s1
    then has_next g2 s2 &&
           (case next g1 s1 of {
             (x, s1a) ->
               (case next g2 s2 of {
                 (y, s2a) -> p x y && list_all2_fusion p g1 g2 s1a s2a;
               });
           })
    else not (has_next g2 s2));

set_eq :: forall a. (Cenum a, Ceq a, Ccompare a) => Set a -> Set a -> Bool;
set_eq (RBT_set rbt1) (RBT_set rbt2) =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "set_eq RBT_set RBT_set: ccompare = None"
        (\ _ -> set_eq (RBT_set rbt1) (RBT_set rbt2));
    Just c ->
      (case ceq of {
        Nothing ->
          list_all2_fusion
            (\ x y -> Comparator.equal_order (c x y) Comparator.Eqa)
            rbt_keys_generator rbt_keys_generator (init rbt1) (init rbt2);
        Just eq ->
          list_all2_fusion eq rbt_keys_generator rbt_keys_generator (init rbt1)
            (init rbt2);
      });
  });
set_eq (Complement a) (Complement b) = set_eq a b;
set_eq a b = less_eq_set a b && less_eq_set b a;

ceq_set ::
  forall a. (Cenum a, Ceq a, Ccompare a) => Maybe (Set a -> Set a -> Bool);
ceq_set = (case (ceq :: Maybe (a -> a -> Bool)) of {
            Nothing -> Nothing;
            Just _ -> Just set_eq;
          });

instance (Cenum a, Ceq a, Ccompare a) => Ceq (Set a) where {
  ceq = ceq_set;
};

set_impl_set :: forall a. Phantom_Type.Phantom (Set a) Set_impla;
set_impl_set = Phantom_Type.Phantom Set_Choose;

instance Set_impl (Set a) where {
  set_impl = set_impl_set;
};

emptya :: forall a b. (Ccompare a) => Mapping_rbt a b;
emptya = Mapping_RBT Empty;

empty :: forall a. (Ceq a) => Set_dlist a;
empty = Abs_dlist [];

set_empty_choose :: forall a. (Ceq a, Ccompare a) => Set a;
set_empty_choose = (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
                     Nothing -> (case (ceq :: Maybe (a -> a -> Bool)) of {
                                  Nothing -> Set_Monad [];
                                  Just _ -> DList_set empty;
                                });
                     Just _ -> RBT_set emptya;
                   });

set_empty :: forall a. (Ceq a, Ccompare a) => Set_impla -> Set a;
set_empty Set_Collect = Collect_set (\ _ -> False);
set_empty Set_DList = DList_set empty;
set_empty Set_RBT = RBT_set emptya;
set_empty Set_Monada = Set_Monad [];
set_empty Set_Choose = set_empty_choose;

balance_right :: forall a b. Rbt a b -> a -> b -> Rbt a b -> Rbt a b;
balance_right a k x (Branch R b s y c) = Branch R a k x (Branch B b s y c);
balance_right (Branch B a k x b) s y Empty =
  balance (Branch R a k x b) s y Empty;
balance_right (Branch B a k x b) s y (Branch B va vb vc vd) =
  balance (Branch R a k x b) s y (Branch B va vb vc vd);
balance_right (Branch R a k x (Branch B b s y c)) t z Empty =
  Branch R (balance (paint R a) k x b) s y (Branch B c t z Empty);
balance_right (Branch R a k x (Branch B b s y c)) t z (Branch B va vb vc vd) =
  Branch R (balance (paint R a) k x b) s y
    (Branch B c t z (Branch B va vb vc vd));
balance_right Empty k x Empty = Empty;
balance_right (Branch R va vb vc Empty) k x Empty = Empty;
balance_right (Branch R va vb vc (Branch R ve vf vg vh)) k x Empty = Empty;
balance_right Empty k x (Branch B va vb vc vd) = Empty;
balance_right (Branch R ve vf vg Empty) k x (Branch B va vb vc vd) = Empty;
balance_right (Branch R ve vf vg (Branch R vi vj vk vl)) k x
  (Branch B va vb vc vd) = Empty;

balance_left :: forall a b. Rbt a b -> a -> b -> Rbt a b -> Rbt a b;
balance_left (Branch R a k x b) s y c = Branch R (Branch B a k x b) s y c;
balance_left Empty k x (Branch B a s y b) =
  balance Empty k x (Branch R a s y b);
balance_left (Branch B va vb vc vd) k x (Branch B a s y b) =
  balance (Branch B va vb vc vd) k x (Branch R a s y b);
balance_left Empty k x (Branch R (Branch B a s y b) t z c) =
  Branch R (Branch B Empty k x a) s y (balance b t z (paint R c));
balance_left (Branch B va vb vc vd) k x (Branch R (Branch B a s y b) t z c) =
  Branch R (Branch B (Branch B va vb vc vd) k x a) s y
    (balance b t z (paint R c));
balance_left Empty k x Empty = Empty;
balance_left Empty k x (Branch R Empty vb vc vd) = Empty;
balance_left Empty k x (Branch R (Branch R ve vf vg vh) vb vc vd) = Empty;
balance_left (Branch B va vb vc vd) k x Empty = Empty;
balance_left (Branch B va vb vc vd) k x (Branch R Empty vf vg vh) = Empty;
balance_left (Branch B va vb vc vd) k x
  (Branch R (Branch R vi vj vk vl) vf vg vh) = Empty;

combine :: forall a b. Rbt a b -> Rbt a b -> Rbt a b;
combine Empty x = x;
combine (Branch v va vb vc vd) Empty = Branch v va vb vc vd;
combine (Branch R a k x b) (Branch R c s y d) =
  (case combine b c of {
    Empty -> Branch R a k x (Branch R Empty s y d);
    Branch R b2 t z c2 -> Branch R (Branch R a k x b2) t z (Branch R c2 s y d);
    Branch B b2 t z c2 -> Branch R a k x (Branch R (Branch B b2 t z c2) s y d);
  });
combine (Branch B a k x b) (Branch B c s y d) =
  (case combine b c of {
    Empty -> balance_left a k x (Branch B Empty s y d);
    Branch R b2 t z c2 -> Branch R (Branch B a k x b2) t z (Branch B c2 s y d);
    Branch B b2 t z c2 ->
      balance_left a k x (Branch B (Branch B b2 t z c2) s y d);
  });
combine (Branch B va vb vc vd) (Branch R b k x c) =
  Branch R (combine (Branch B va vb vc vd) b) k x c;
combine (Branch R a k x b) (Branch B va vb vc vd) =
  Branch R a k x (combine b (Branch B va vb vc vd));

rbt_comp_del ::
  forall a b. (a -> a -> Comparator.Order) -> a -> Rbt a b -> Rbt a b;
rbt_comp_del c x Empty = Empty;
rbt_comp_del c x (Branch uu a y s b) =
  (case c x y of {
    Comparator.Eqa -> combine a b;
    Comparator.Lt -> rbt_comp_del_from_left c x a y s b;
    Comparator.Gt -> rbt_comp_del_from_right c x a y s b;
  });

rbt_comp_del_from_left ::
  forall a b.
    (a -> a -> Comparator.Order) ->
      a -> Rbt a b -> a -> b -> Rbt a b -> Rbt a b;
rbt_comp_del_from_left c x (Branch B lt z v rt) y s b =
  balance_left (rbt_comp_del c x (Branch B lt z v rt)) y s b;
rbt_comp_del_from_left c x Empty y s b =
  Branch R (rbt_comp_del c x Empty) y s b;
rbt_comp_del_from_left c x (Branch R va vb vc vd) y s b =
  Branch R (rbt_comp_del c x (Branch R va vb vc vd)) y s b;

rbt_comp_del_from_right ::
  forall a b.
    (a -> a -> Comparator.Order) ->
      a -> Rbt a b -> a -> b -> Rbt a b -> Rbt a b;
rbt_comp_del_from_right c x a y s (Branch B lt z v rt) =
  balance_right a y s (rbt_comp_del c x (Branch B lt z v rt));
rbt_comp_del_from_right c x a y s Empty =
  Branch R a y s (rbt_comp_del c x Empty);
rbt_comp_del_from_right c x a y s (Branch R va vb vc vd) =
  Branch R a y s (rbt_comp_del c x (Branch R va vb vc vd));

rbt_comp_delete ::
  forall a b. (a -> a -> Comparator.Order) -> a -> Rbt a b -> Rbt a b;
rbt_comp_delete c k t = paint B (rbt_comp_del c k t);

delete :: forall a b. (Ccompare a) => a -> Mapping_rbt a b -> Mapping_rbt a b;
delete xb xc = Mapping_RBT (rbt_comp_delete (the ccompare) xb (impl_of xc));

list_remove1 :: forall a. (a -> a -> Bool) -> a -> [a] -> [a];
list_remove1 equal x [] = [];
list_remove1 equal x (y : xs) =
  (if equal x y then xs else y : list_remove1 equal x xs);

removea :: forall a. (Ceq a) => a -> Set_dlist a -> Set_dlist a;
removea xb xc = Abs_dlist (list_remove1 (the ceq) xb (list_of_dlist xc));

insert :: forall a. (Ceq a, Ccompare a) => a -> Set a -> Set a;
insert xa (Complement x) = Complement (remove xa x);
insert x (RBT_set rbt) =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "insert RBT_set: ccompare = None" (\ _ -> insert x (RBT_set rbt));
    Just _ -> RBT_set (insertc x () rbt);
  });
insert x (DList_set dxs) =
  (case (ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "insert DList_set: ceq = None" (\ _ -> insert x (DList_set dxs));
    Just _ -> DList_set (insertb x dxs);
  });
insert x (Set_Monad xs) = Set_Monad (x : xs);
insert x (Collect_set a) =
  (case ceq of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "insert Collect_set: ceq = None" (\ _ -> insert x (Collect_set a));
    Just eq -> Collect_set (Closure_Set.fun_upd eq a x True);
  });

remove :: forall a. (Ceq a, Ccompare a) => a -> Set a -> Set a;
remove x (Complement a) = Complement (insert x a);
remove x (RBT_set rbt) =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "remove RBT_set: ccompare = None" (\ _ -> remove x (RBT_set rbt));
    Just _ -> RBT_set (delete x rbt);
  });
remove x (DList_set dxs) =
  (case (ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "remove DList_set: ceq = None" (\ _ -> remove x (DList_set dxs));
    Just _ -> DList_set (removea x dxs);
  });
remove x (Collect_set a) =
  (case ceq of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a) "remove Collect: ceq = None"
        (\ _ -> remove x (Collect_set a));
    Just eq -> Collect_set (Closure_Set.fun_upd eq a x False);
  });

foldl :: forall a b. (a -> b -> a) -> a -> [b] -> a;
foldl f a [] = a;
foldl f a (x : xs) = foldl f (f a x) xs;

set_aux :: forall a. (Ceq a, Ccompare a) => Set_impla -> [a] -> Set a;
set_aux Set_Monada = Set_Monad;
set_aux Set_Choose =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing -> (case (ceq :: Maybe (a -> a -> Bool)) of {
                 Nothing -> Set_Monad;
                 Just _ -> foldl (\ s x -> insert x s) (DList_set empty);
               });
    Just _ -> foldl (\ s x -> insert x s) (RBT_set emptya);
  });
set_aux impl = foldl (\ s x -> insert x s) (set_empty impl);

set :: forall a. (Ceq a, Ccompare a, Set_impl a) => [a] -> Set a;
set xs =
  set_aux
    (Phantom_Type.of_phantom (set_impl :: Phantom_Type.Phantom a Set_impla)) xs;

subseqs :: forall a. [a] -> [[a]];
subseqs [] = [[]];
subseqs (x : xs) = let {
                     xss = subseqs xs;
                   } in map (\ a -> x : a) xss ++ xss;

cEnum_set ::
  forall a.
    (Cenum a, Ceq a, Ccompare a,
      Set_impl a) => Maybe ([Set a],
                             ((Set a -> Bool) -> Bool,
                               (Set a -> Bool) -> Bool));
cEnum_set =
  (case cEnum of {
    Nothing -> Nothing;
    Just (enum_a, (_, _)) ->
      Just (map set (subseqs enum_a),
             ((\ p -> all p (map set (subseqs enum_a))),
               (\ p -> any p (map set (subseqs enum_a)))));
  });

instance (Cenum a, Ceq a, Ccompare a, Set_impl a) => Cenum (Set a) where {
  cEnum = cEnum_set;
};

finite_UNIV_set ::
  forall a. (Finite_UNIV a) => Phantom_Type.Phantom (Set a) Bool;
finite_UNIV_set =
  Phantom_Type.Phantom
    (Phantom_Type.of_phantom (finite_UNIV :: Phantom_Type.Phantom a Bool));

instance (Finite_UNIV a) => Finite_UNIV (Set a) where {
  finite_UNIV = finite_UNIV_set;
};

set_less_eq_aux_Compl_fusion ::
  forall a b c.
    (a -> a -> Bool) ->
      (Maybe a -> Maybe a -> Bool) ->
        Generator a b -> Generator a c -> Maybe a -> b -> c -> Bool;
set_less_eq_aux_Compl_fusion less proper_interval g1 g2 ao s1 s2 =
  (if has_next g1 s1
    then (if has_next g2 s2
           then (case next g1 s1 of {
                  (x, s1a) ->
                    (case next g2 s2 of {
                      (y, s2a) ->
                        (if less x y
                          then proper_interval ao (Just x) ||
                                 set_less_eq_aux_Compl_fusion less
                                   proper_interval g1 g2 (Just x) s1a s2
                          else (if less y x
                                 then proper_interval ao (Just y) ||
set_less_eq_aux_Compl_fusion less proper_interval g1 g2 (Just y) s1 s2a
                                 else proper_interval ao (Just y)));
                    });
                })
           else True)
    else True);

compl_set_less_eq_aux_fusion ::
  forall a b c.
    (a -> a -> Bool) ->
      (Maybe a -> Maybe a -> Bool) ->
        Generator a b -> Generator a c -> Maybe a -> b -> c -> Bool;
compl_set_less_eq_aux_fusion less proper_interval g1 g2 ao s1 s2 =
  (if has_next g1 s1
    then (case next g1 s1 of {
           (x, s1a) ->
             (if has_next g2 s2
               then (case next g2 s2 of {
                      (y, s2a) ->
                        (if less x y
                          then not (proper_interval ao (Just x)) &&
                                 compl_set_less_eq_aux_fusion less
                                   proper_interval g1 g2 (Just x) s1a s2
                          else (if less y x
                                 then not (proper_interval ao (Just y)) &&
compl_set_less_eq_aux_fusion less proper_interval g1 g2 (Just y) s1 s2a
                                 else not (proper_interval ao (Just y))));
                    })
               else not (proper_interval ao (Just x)) &&
                      compl_set_less_eq_aux_fusion less proper_interval g1 g2
                        (Just x) s1a s2);
         })
    else (if has_next g2 s2
           then (case next g2 s2 of {
                  (y, s2a) ->
                    not (proper_interval ao (Just y)) &&
                      compl_set_less_eq_aux_fusion less proper_interval g1 g2
                        (Just y) s1 s2a;
                })
           else not (proper_interval ao Nothing)));

set_less_eq_aux_Compl ::
  forall a.
    (a -> a -> Bool) ->
      (Maybe a -> Maybe a -> Bool) -> Maybe a -> [a] -> [a] -> Bool;
set_less_eq_aux_Compl less proper_interval ao [] ys = True;
set_less_eq_aux_Compl less proper_interval ao xs [] = True;
set_less_eq_aux_Compl less proper_interval ao (x : xs) (y : ys) =
  (if less x y
    then proper_interval ao (Just x) ||
           set_less_eq_aux_Compl less proper_interval (Just x) xs (y : ys)
    else (if less y x
           then proper_interval ao (Just y) ||
                  set_less_eq_aux_Compl less proper_interval (Just y) (x : xs)
                    ys
           else proper_interval ao (Just y)));

compl_set_less_eq_aux ::
  forall a.
    (a -> a -> Bool) ->
      (Maybe a -> Maybe a -> Bool) -> Maybe a -> [a] -> [a] -> Bool;
compl_set_less_eq_aux less proper_interval ao [] [] =
  not (proper_interval ao Nothing);
compl_set_less_eq_aux less proper_interval ao [] (y : ys) =
  not (proper_interval ao (Just y)) &&
    compl_set_less_eq_aux less proper_interval (Just y) [] ys;
compl_set_less_eq_aux less proper_interval ao (x : xs) [] =
  not (proper_interval ao (Just x)) &&
    compl_set_less_eq_aux less proper_interval (Just x) xs [];
compl_set_less_eq_aux less proper_interval ao (x : xs) (y : ys) =
  (if less x y
    then not (proper_interval ao (Just x)) &&
           compl_set_less_eq_aux less proper_interval (Just x) xs (y : ys)
    else (if less y x
           then not (proper_interval ao (Just y)) &&
                  compl_set_less_eq_aux less proper_interval (Just y) (x : xs)
                    ys
           else not (proper_interval ao (Just y))));

lexord_eq_fusion ::
  forall a b c.
    (a -> a -> Bool) -> Generator a b -> Generator a c -> b -> c -> Bool;
lexord_eq_fusion less g1 g2 s1 s2 =
  (if has_next g1 s1
    then has_next g2 s2 &&
           (case next g1 s1 of {
             (x, s1a) ->
               (case next g2 s2 of {
                 (y, s2a) ->
                   less x y ||
                     not (less y x) && lexord_eq_fusion less g1 g2 s1a s2a;
               });
           })
    else True);

remdups_sorted :: forall a. (a -> a -> Bool) -> [a] -> [a];
remdups_sorted less [] = [];
remdups_sorted less [x] = [x];
remdups_sorted less (x : y : xs) =
  (if less x y then x : remdups_sorted less (y : xs)
    else remdups_sorted less (y : xs));

quicksort_acc :: forall a. (a -> a -> Bool) -> [a] -> [a] -> [a];
quicksort_acc less ac [] = ac;
quicksort_acc less ac [x] = x : ac;
quicksort_acc less ac (x : v : va) = quicksort_part less ac x [] [] [] (v : va);

quicksort_part ::
  forall a. (a -> a -> Bool) -> [a] -> a -> [a] -> [a] -> [a] -> [a] -> [a];
quicksort_part less ac x lts eqs gts [] =
  quicksort_acc less (eqs ++ x : quicksort_acc less ac gts) lts;
quicksort_part less ac x lts eqs gts (z : zs) =
  (if less x z then quicksort_part less ac x lts eqs (z : gts) zs
    else (if less z x then quicksort_part less ac x (z : lts) eqs gts zs
           else quicksort_part less ac x lts (z : eqs) gts zs));

quicksort :: forall a. (a -> a -> Bool) -> [a] -> [a];
quicksort less = quicksort_acc less [];

gen_keys :: forall a b. [(a, Rbt a b)] -> Rbt a b -> [a];
gen_keys [] Empty = [];
gen_keys ((k, t) : kts) Empty = k : gen_keys kts t;
gen_keys kts (Branch c l k v r) = gen_keys ((k, r) : kts) l;

keys :: forall a b. Rbt a b -> [a];
keys = gen_keys [];

keysa :: forall a. (Ccompare a) => Mapping_rbt a () -> [a];
keysa xa = keys (impl_of xa);

csorted_list_of_set :: forall a. (Ceq a, Ccompare a) => Set a -> [a];
csorted_list_of_set (Set_Monad xs) =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "csorted_list_of_set Set_Monad: ccompare = None"
        (\ _ -> csorted_list_of_set (Set_Monad xs));
    Just c ->
      remdups_sorted (Comparator.lt_of_comp c)
        (quicksort (Comparator.lt_of_comp c) xs);
  });
csorted_list_of_set (DList_set dxs) =
  (case (ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "csorted_list_of_set DList_set: ceq = None"
        (\ _ -> csorted_list_of_set (DList_set dxs));
    Just _ ->
      (case ccompare of {
        Nothing ->
          (error :: forall a. String -> (() -> a) -> a)
            "csorted_list_of_set DList_set: ccompare = None"
            (\ _ -> csorted_list_of_set (DList_set dxs));
        Just c -> quicksort (Comparator.lt_of_comp c) (list_of_dlist dxs);
      });
  });
csorted_list_of_set (RBT_set rbt) =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "csorted_list_of_set RBT_set: ccompare = None"
        (\ _ -> csorted_list_of_set (RBT_set rbt));
    Just _ -> keysa rbt;
  });

bot_set :: forall a. (Ceq a, Ccompare a, Set_impl a) => Set a;
bot_set =
  set_empty
    (Phantom_Type.of_phantom (set_impl :: Phantom_Type.Phantom a Set_impla));

top_set :: forall a. (Ceq a, Ccompare a, Set_impl a) => Set a;
top_set = uminus_set bot_set;

lexordp_eq :: forall a. (a -> a -> Bool) -> [a] -> [a] -> Bool;
lexordp_eq less [] ys = True;
lexordp_eq less xs [] = null xs;
lexordp_eq less (x : xs) (y : ys) =
  less x y || not (less y x) && lexordp_eq less xs ys;

finite :: forall a. (Finite_UNIV a, Ceq a, Ccompare a) => Set a -> Bool;
finite (Collect_set p) =
  Phantom_Type.of_phantom (finite_UNIV :: Phantom_Type.Phantom a Bool) ||
    (error :: forall a. String -> (() -> a) -> a) "finite Collect_set"
      (\ _ -> finite (Collect_set p));
finite (Set_Monad xs) = True;
finite (Complement a) =
  (if Phantom_Type.of_phantom (finite_UNIV :: Phantom_Type.Phantom a Bool)
    then True
    else (if finite a then False
           else (error :: forall a. String -> (() -> a) -> a)
                  "finite Complement: infinite set"
                  (\ _ -> finite (Complement a))));
finite (RBT_set rbt) =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "finite RBT_set: ccompare = None" (\ _ -> finite (RBT_set rbt));
    Just _ -> True;
  });
finite (DList_set dxs) =
  (case (ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "finite DList_set: ceq = None" (\ _ -> finite (DList_set dxs));
    Just _ -> True;
  });

set_less_aux_Compl_fusion ::
  forall a b c.
    (a -> a -> Bool) ->
      (Maybe a -> Maybe a -> Bool) ->
        Generator a b -> Generator a c -> Maybe a -> b -> c -> Bool;
set_less_aux_Compl_fusion less proper_interval g1 g2 ao s1 s2 =
  (if has_next g1 s1
    then (case next g1 s1 of {
           (x, s1a) ->
             (if has_next g2 s2
               then (case next g2 s2 of {
                      (y, s2a) ->
                        (if less x y
                          then proper_interval ao (Just x) ||
                                 set_less_aux_Compl_fusion less proper_interval
                                   g1 g2 (Just x) s1a s2
                          else (if less y x
                                 then proper_interval ao (Just y) ||
set_less_aux_Compl_fusion less proper_interval g1 g2 (Just y) s1 s2a
                                 else proper_interval ao (Just y)));
                    })
               else proper_interval ao (Just x) ||
                      set_less_aux_Compl_fusion less proper_interval g1 g2
                        (Just x) s1a s2);
         })
    else (if has_next g2 s2
           then (case next g2 s2 of {
                  (y, s2a) ->
                    proper_interval ao (Just y) ||
                      set_less_aux_Compl_fusion less proper_interval g1 g2
                        (Just y) s1 s2a;
                })
           else proper_interval ao Nothing));

compl_set_less_aux_fusion ::
  forall a b c.
    (a -> a -> Bool) ->
      (Maybe a -> Maybe a -> Bool) ->
        Generator a b -> Generator a c -> Maybe a -> b -> c -> Bool;
compl_set_less_aux_fusion less proper_interval g1 g2 ao s1 s2 =
  has_next g1 s1 &&
    has_next g2 s2 &&
      (case next g1 s1 of {
        (x, s1a) ->
          (case next g2 s2 of {
            (y, s2a) ->
              (if less x y
                then not (proper_interval ao (Just x)) &&
                       compl_set_less_aux_fusion less proper_interval g1 g2
                         (Just x) s1a s2
                else (if less y x
                       then not (proper_interval ao (Just y)) &&
                              compl_set_less_aux_fusion less proper_interval g1
                                g2 (Just y) s1 s2a
                       else not (proper_interval ao (Just y))));
          });
      });

set_less_aux_Compl ::
  forall a.
    (a -> a -> Bool) ->
      (Maybe a -> Maybe a -> Bool) -> Maybe a -> [a] -> [a] -> Bool;
set_less_aux_Compl less proper_interval ao [] [] = proper_interval ao Nothing;
set_less_aux_Compl less proper_interval ao [] (y : ys) =
  proper_interval ao (Just y) ||
    set_less_aux_Compl less proper_interval (Just y) [] ys;
set_less_aux_Compl less proper_interval ao (x : xs) [] =
  proper_interval ao (Just x) ||
    set_less_aux_Compl less proper_interval (Just x) xs [];
set_less_aux_Compl less proper_interval ao (x : xs) (y : ys) =
  (if less x y
    then proper_interval ao (Just x) ||
           set_less_aux_Compl less proper_interval (Just x) xs (y : ys)
    else (if less y x
           then proper_interval ao (Just y) ||
                  set_less_aux_Compl less proper_interval (Just y) (x : xs) ys
           else proper_interval ao (Just y)));

compl_set_less_aux ::
  forall a.
    (a -> a -> Bool) ->
      (Maybe a -> Maybe a -> Bool) -> Maybe a -> [a] -> [a] -> Bool;
compl_set_less_aux less proper_interval ao [] ys = False;
compl_set_less_aux less proper_interval ao xs [] = False;
compl_set_less_aux less proper_interval ao (x : xs) (y : ys) =
  (if less x y
    then not (proper_interval ao (Just x)) &&
           compl_set_less_aux less proper_interval (Just x) xs (y : ys)
    else (if less y x
           then not (proper_interval ao (Just y)) &&
                  compl_set_less_aux less proper_interval (Just y) (x : xs) ys
           else not (proper_interval ao (Just y))));

lexord_fusion ::
  forall a b c.
    (a -> a -> Bool) -> Generator a b -> Generator a c -> b -> c -> Bool;
lexord_fusion less g1 g2 s1 s2 =
  (if has_next g1 s1
    then (if has_next g2 s2
           then (case next g1 s1 of {
                  (x, s1a) ->
                    (case next g2 s2 of {
                      (y, s2a) ->
                        less x y ||
                          not (less y x) && lexord_fusion less g1 g2 s1a s2a;
                    });
                })
           else False)
    else has_next g2 s2);

lexordp :: forall a. (a -> a -> Bool) -> [a] -> [a] -> Bool;
lexordp less [] ys = not (null ys);
lexordp less xs [] = False;
lexordp less (x : xs) (y : ys) =
  less x y || not (less y x) && lexordp less xs ys;

ccompare_set ::
  forall a.
    (Finite_UNIV a, Ceq a, Cproper_interval a,
      Set_impl a) => Maybe (Set a -> Set a -> Comparator.Order);
ccompare_set =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing -> Nothing;
    Just _ -> Just (Comparator.comp_of_ords cless_eq_set cless_set);
  });

cless_set ::
  forall a.
    (Finite_UNIV a, Ceq a, Cproper_interval a,
      Set_impl a) => Set a -> Set a -> Bool;
cless_set (Complement (RBT_set rbt1)) (RBT_set rbt2) =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cless_set (Complement RBT_set) RBT_set: ccompare = None"
        (\ _ -> cless_set (Complement (RBT_set rbt1)) (RBT_set rbt2));
    Just c ->
      (finite :: Set a -> Bool) (top_set :: Set a) &&
        compl_set_less_aux_fusion (Comparator.lt_of_comp c) cproper_interval
          rbt_keys_generator rbt_keys_generator Nothing (init rbt1) (init rbt2);
  });
cless_set (RBT_set rbt1) (Complement (RBT_set rbt2)) =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cless_set RBT_set (Complement RBT_set): ccompare = None"
        (\ _ -> cless_set (RBT_set rbt1) (Complement (RBT_set rbt2)));
    Just c ->
      (if (finite :: Set a -> Bool) (top_set :: Set a)
        then set_less_aux_Compl_fusion (Comparator.lt_of_comp c)
               cproper_interval rbt_keys_generator rbt_keys_generator Nothing
               (init rbt1) (init rbt2)
        else True);
  });
cless_set (RBT_set rbta) (RBT_set rbt) =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cless_set RBT_set RBT_set: ccompare = None"
        (\ _ -> cless_set (RBT_set rbta) (RBT_set rbt));
    Just c ->
      lexord_fusion (\ x y -> Comparator.lt_of_comp c y x) rbt_keys_generator
        rbt_keys_generator (init rbta) (init rbt);
  });
cless_set (Complement a) (Complement b) =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cless_set Complement Complement: ccompare = None"
        (\ _ -> cless_set (Complement a) (Complement b));
    Just _ -> Comparator.lt_of_comp (the ccompare_set) b a;
  });
cless_set (Complement a) b =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cless_set Complement1: ccompare = None"
        (\ _ -> cless_set (Complement a) b);
    Just c ->
      (if finite a && finite b
        then (finite :: Set a -> Bool) (top_set :: Set a) &&
               compl_set_less_aux (Comparator.lt_of_comp c) cproper_interval
                 Nothing (csorted_list_of_set a) (csorted_list_of_set b)
        else (error :: forall a. String -> (() -> a) -> a)
               "cless_set Complement1: infinite set"
               (\ _ -> cless_set (Complement a) b));
  });
cless_set a (Complement b) =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cless_set Complement2: ccompare = None"
        (\ _ -> cless_set a (Complement b));
    Just c ->
      (if finite a && finite b
        then (if (finite :: Set a -> Bool) (top_set :: Set a)
               then set_less_aux_Compl (Comparator.lt_of_comp c)
                      cproper_interval Nothing (csorted_list_of_set a)
                      (csorted_list_of_set b)
               else True)
        else (error :: forall a. String -> (() -> a) -> a)
               "cless_set Complement2: infinite set"
               (\ _ -> cless_set a (Complement b)));
  });
cless_set a b =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a) "cless_set: ccompare = None"
        (\ _ -> cless_set a b);
    Just c ->
      (if finite a && finite b
        then lexordp (\ x y -> Comparator.lt_of_comp c y x)
               (csorted_list_of_set a) (csorted_list_of_set b)
        else (error :: forall a. String -> (() -> a) -> a)
               "cless_set: infinite set" (\ _ -> cless_set a b));
  });

cless_eq_set ::
  forall a.
    (Finite_UNIV a, Ceq a, Cproper_interval a,
      Set_impl a) => Set a -> Set a -> Bool;
cless_eq_set (Complement (RBT_set rbt1)) (RBT_set rbt2) =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cless_eq_set (Complement RBT_set) RBT_set: ccompare = None"
        (\ _ -> cless_eq_set (Complement (RBT_set rbt1)) (RBT_set rbt2));
    Just c ->
      (finite :: Set a -> Bool) (top_set :: Set a) &&
        compl_set_less_eq_aux_fusion (Comparator.lt_of_comp c) cproper_interval
          rbt_keys_generator rbt_keys_generator Nothing (init rbt1) (init rbt2);
  });
cless_eq_set (RBT_set rbt1) (Complement (RBT_set rbt2)) =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cless_eq_set RBT_set (Complement RBT_set): ccompare = None"
        (\ _ -> cless_eq_set (RBT_set rbt1) (Complement (RBT_set rbt2)));
    Just c ->
      (if (finite :: Set a -> Bool) (top_set :: Set a)
        then set_less_eq_aux_Compl_fusion (Comparator.lt_of_comp c)
               cproper_interval rbt_keys_generator rbt_keys_generator Nothing
               (init rbt1) (init rbt2)
        else True);
  });
cless_eq_set (RBT_set rbta) (RBT_set rbt) =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cless_eq_set RBT_set RBT_set: ccompare = None"
        (\ _ -> cless_eq_set (RBT_set rbta) (RBT_set rbt));
    Just c ->
      lexord_eq_fusion (\ x y -> Comparator.lt_of_comp c y x) rbt_keys_generator
        rbt_keys_generator (init rbta) (init rbt);
  });
cless_eq_set (Complement a) (Complement b) =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cless_eq_set Complement Complement: ccompare = None"
        (\ _ ->
          Comparator.le_of_comp (the ccompare_set) (Complement a)
            (Complement b));
    Just _ -> cless_eq_set b a;
  });
cless_eq_set (Complement a) b =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cless_eq_set Complement1: ccompare = None"
        (\ _ -> cless_eq_set (Complement a) b);
    Just c ->
      (if finite a && finite b
        then (finite :: Set a -> Bool) (top_set :: Set a) &&
               compl_set_less_eq_aux (Comparator.lt_of_comp c) cproper_interval
                 Nothing (csorted_list_of_set a) (csorted_list_of_set b)
        else (error :: forall a. String -> (() -> a) -> a)
               "cless_eq_set Complement1: infinite set"
               (\ _ -> cless_eq_set (Complement a) b));
  });
cless_eq_set a (Complement b) =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cless_eq_set Complement2: ccompare = None"
        (\ _ -> cless_eq_set a (Complement b));
    Just c ->
      (if finite a && finite b
        then (if (finite :: Set a -> Bool) (top_set :: Set a)
               then set_less_eq_aux_Compl (Comparator.lt_of_comp c)
                      cproper_interval Nothing (csorted_list_of_set a)
                      (csorted_list_of_set b)
               else True)
        else (error :: forall a. String -> (() -> a) -> a)
               "cless_eq_set Complement2: infinite set"
               (\ _ -> cless_eq_set a (Complement b)));
  });
cless_eq_set a b =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cless_eq_set: ccompare = None" (\ _ -> cless_eq_set a b);
    Just c ->
      (if finite a && finite b
        then lexordp_eq (\ x y -> Comparator.lt_of_comp c y x)
               (csorted_list_of_set a) (csorted_list_of_set b)
        else (error :: forall a. String -> (() -> a) -> a)
               "cless_eq_set: infinite set" (\ _ -> cless_eq_set a b));
  });

instance (Finite_UNIV a, Ceq a, Cproper_interval a,
           Set_impl a) => Ccompare (Set a) where {
  ccompare = ccompare_set;
};

fold_fusion :: forall a b c. Generator a b -> (a -> c -> c) -> b -> c -> c;
fold_fusion g f s b =
  (if has_next g s then (case next g s of {
                          (x, sa) -> fold_fusion g f sa (f x b);
                        })
    else b);

length_last_fusion :: forall a b. Generator a b -> b -> (Nat, a);
length_last_fusion g s =
  (if has_next g s
    then (case next g s of {
           (x, sa) ->
             fold_fusion g (\ xa (n, _) -> (plus_nat n one_nat, xa)) sa
               (one_nat, x);
         })
    else (zero_nat, error "undefined"));

gen_length_fusion :: forall a b. Generator a b -> Nat -> b -> Nat;
gen_length_fusion g n s =
  (if has_next g s then gen_length_fusion g (suc n) (snd (next g s)) else n);

length_fusion :: forall a b. Generator a b -> b -> Nat;
length_fusion g = gen_length_fusion g zero_nat;

list_remdups :: forall a. (a -> a -> Bool) -> [a] -> [a];
list_remdups equal [] = [];
list_remdups equal (x : xs) =
  (if list_member equal xs x then list_remdups equal xs
    else x : list_remdups equal xs);

length :: forall a. (Ceq a) => Set_dlist a -> Nat;
length xa = size_list (list_of_dlist xa);

card :: forall a. (Card_UNIV a, Ceq a, Ccompare a) => Set a -> Nat;
card (Complement a) =
  let {
    aa = card a;
    s = Phantom_Type.of_phantom (card_UNIV :: Phantom_Type.Phantom a Nat);
  } in (if less_nat zero_nat s then minus_nat s aa
         else (if finite a then zero_nat
                else (error :: forall a. String -> (() -> a) -> a)
                       "card Complement: infinite"
                       (\ _ -> card (Complement a))));
card (Set_Monad xs) =
  (case ceq of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a) "card Set_Monad: ceq = None"
        (\ _ -> card (Set_Monad xs));
    Just eq -> size_list (list_remdups eq xs);
  });
card (RBT_set rbt) =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "card RBT_set: ccompare = None" (\ _ -> card (RBT_set rbt));
    Just _ -> size_list (keysa rbt);
  });
card (DList_set dxs) =
  (case (ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a) "card DList_set: ceq = None"
        (\ _ -> card (DList_set dxs));
    Just _ -> length dxs;
  });

proper_interval_set_Compl_aux_fusion ::
  forall a b c.
    (Card_UNIV a, Ceq a, Ccompare a,
      Set_impl a) => (a -> a -> Bool) ->
                       (Maybe a -> Maybe a -> Bool) ->
                         Generator a b ->
                           Generator a c -> Maybe a -> Nat -> b -> c -> Bool;
proper_interval_set_Compl_aux_fusion less proper_interval g1 g2 ao n s1 s2 =
  (if has_next g1 s1
    then (case next g1 s1 of {
           (x, s1a) ->
             (if has_next g2 s2
               then (case next g2 s2 of {
                      (y, s2a) ->
                        (if less x y
                          then proper_interval ao (Just x) ||
                                 proper_interval_set_Compl_aux_fusion less
                                   proper_interval g1 g2 (Just x)
                                   (plus_nat n one_nat) s1a s2
                          else (if less y x
                                 then proper_interval ao (Just y) ||
proper_interval_set_Compl_aux_fusion less proper_interval g1 g2 (Just y)
  (plus_nat n one_nat) s1 s2a
                                 else proper_interval ao (Just x) &&
let {
  m = minus_nat ((card :: Set a -> Nat) (top_set :: Set a)) n;
} in not (equal_nat (minus_nat m (length_fusion g2 s2a))
           (nat_of_integer (2 :: Integer))) ||
       not (equal_nat (minus_nat m (length_fusion g1 s1a))
             (nat_of_integer (2 :: Integer)))));
                    })
               else let {
                      m = minus_nat ((card :: Set a -> Nat) (top_set :: Set a))
                            n;
                    } in (case length_last_fusion g1 s1 of {
                           (len_x, xa) ->
                             not (equal_nat m len_x) &&
                               (if equal_nat m (plus_nat len_x one_nat)
                                 then not (proper_interval (Just xa) Nothing)
                                 else True);
                         }));
         })
    else (if has_next g2 s2
           then (case next g2 s2 of {
                  (_, _) ->
                    let {
                      m = minus_nat ((card :: Set a -> Nat) (top_set :: Set a))
                            n;
                    } in (case length_last_fusion g2 s2 of {
                           (len_y, y) ->
                             not (equal_nat m len_y) &&
                               (if equal_nat m (plus_nat len_y one_nat)
                                 then not (proper_interval (Just y) Nothing)
                                 else True);
                         });
                })
           else less_nat (plus_nat n one_nat)
                  ((card :: Set a -> Nat) (top_set :: Set a))));

proper_interval_Compl_set_aux_fusion ::
  forall a b c.
    (a -> a -> Bool) ->
      (Maybe a -> Maybe a -> Bool) ->
        Generator a b -> Generator a c -> Maybe a -> b -> c -> Bool;
proper_interval_Compl_set_aux_fusion less proper_interval g1 g2 ao s1 s2 =
  has_next g1 s1 &&
    has_next g2 s2 &&
      (case next g1 s1 of {
        (x, s1a) ->
          (case next g2 s2 of {
            (y, s2a) ->
              (if less x y
                then not (proper_interval ao (Just x)) &&
                       proper_interval_Compl_set_aux_fusion less proper_interval
                         g1 g2 (Just x) s1a s2
                else (if less y x
                       then not (proper_interval ao (Just y)) &&
                              proper_interval_Compl_set_aux_fusion less
                                proper_interval g1 g2 (Just y) s1 s2a
                       else not (proper_interval ao (Just x)) &&
                              (has_next g2 s2a || has_next g1 s1a)));
          });
      });

exhaustive_above_fusion ::
  forall a b. (Maybe a -> Maybe a -> Bool) -> Generator a b -> a -> b -> Bool;
exhaustive_above_fusion proper_interval g y s =
  (if has_next g s
    then (case next g s of {
           (x, sa) ->
             not (proper_interval (Just y) (Just x)) &&
               exhaustive_above_fusion proper_interval g x sa;
         })
    else not (proper_interval (Just y) Nothing));

proper_interval_set_aux_fusion ::
  forall a b c.
    (a -> a -> Bool) ->
      (Maybe a -> Maybe a -> Bool) ->
        Generator a b -> Generator a c -> b -> c -> Bool;
proper_interval_set_aux_fusion less proper_interval g1 g2 s1 s2 =
  has_next g2 s2 &&
    (case next g2 s2 of {
      (y, s2a) ->
        (if has_next g1 s1
          then (case next g1 s1 of {
                 (x, s1a) ->
                   (if less x y then False
                     else (if less y x
                            then proper_interval (Just y) (Just x) ||
                                   (has_next g2 s2a ||
                                     not (exhaustive_above_fusion
   proper_interval g1 x s1a))
                            else proper_interval_set_aux_fusion less
                                   proper_interval g1 g2 s1a s2a));
               })
          else has_next g2 s2a || proper_interval (Just y) Nothing);
    });

length_last :: forall a. [a] -> (Nat, a);
length_last [] = (zero_nat, error "undefined");
length_last (x : xs) =
  fold (\ xa (n, _) -> (plus_nat n one_nat, xa)) xs (one_nat, x);

proper_interval_set_Compl_aux ::
  forall a.
    (Card_UNIV a, Ceq a, Ccompare a,
      Set_impl a) => (a -> a -> Bool) ->
                       (Maybe a -> Maybe a -> Bool) ->
                         Maybe a -> Nat -> [a] -> [a] -> Bool;
proper_interval_set_Compl_aux less proper_interval ao n [] [] =
  less_nat (plus_nat n one_nat) ((card :: Set a -> Nat) (top_set :: Set a));
proper_interval_set_Compl_aux less proper_interval ao n [] (y : ys) =
  let {
    m = minus_nat ((card :: Set a -> Nat) (top_set :: Set a)) n;
  } in (case length_last (y : ys) of {
         (len_y, ya) ->
           not (equal_nat m len_y) &&
             (if equal_nat m (plus_nat len_y one_nat)
               then not (proper_interval (Just ya) Nothing) else True);
       });
proper_interval_set_Compl_aux less proper_interval ao n (x : xs) [] =
  let {
    m = minus_nat ((card :: Set a -> Nat) (top_set :: Set a)) n;
  } in (case length_last (x : xs) of {
         (len_x, xa) ->
           not (equal_nat m len_x) &&
             (if equal_nat m (plus_nat len_x one_nat)
               then not (proper_interval (Just xa) Nothing) else True);
       });
proper_interval_set_Compl_aux less proper_interval ao n (x : xs) (y : ys) =
  (if less x y
    then proper_interval ao (Just x) ||
           proper_interval_set_Compl_aux less proper_interval (Just x)
             (plus_nat n one_nat) xs (y : ys)
    else (if less y x
           then proper_interval ao (Just y) ||
                  proper_interval_set_Compl_aux less proper_interval (Just y)
                    (plus_nat n one_nat) (x : xs) ys
           else proper_interval ao (Just x) &&
                  let {
                    m = minus_nat ((card :: Set a -> Nat) (top_set :: Set a)) n;
                  } in not (equal_nat (minus_nat m (size_list ys))
                             (nat_of_integer (2 :: Integer))) ||
                         not (equal_nat (minus_nat m (size_list xs))
                               (nat_of_integer (2 :: Integer)))));

proper_interval_Compl_set_aux ::
  forall a.
    (a -> a -> Bool) ->
      (Maybe a -> Maybe a -> Bool) -> Maybe a -> [a] -> [a] -> Bool;
proper_interval_Compl_set_aux less proper_interval ao (x : xs) (y : ys) =
  (if less x y
    then not (proper_interval ao (Just x)) &&
           proper_interval_Compl_set_aux less proper_interval (Just x) xs
             (y : ys)
    else (if less y x
           then not (proper_interval ao (Just y)) &&
                  proper_interval_Compl_set_aux less proper_interval (Just y)
                    (x : xs) ys
           else not (proper_interval ao (Just x)) &&
                  (if null ys then not (null xs) else True)));
proper_interval_Compl_set_aux less proper_interval ao [] uv = False;
proper_interval_Compl_set_aux less proper_interval ao uu [] = False;

exhaustive_above :: forall a. (Maybe a -> Maybe a -> Bool) -> a -> [a] -> Bool;
exhaustive_above proper_interval x [] = not (proper_interval (Just x) Nothing);
exhaustive_above proper_interval x (y : ys) =
  not (proper_interval (Just x) (Just y)) &&
    exhaustive_above proper_interval y ys;

proper_interval_set_aux ::
  forall a.
    (a -> a -> Bool) -> (Maybe a -> Maybe a -> Bool) -> [a] -> [a] -> Bool;
proper_interval_set_aux less proper_interval xs [] = False;
proper_interval_set_aux less proper_interval [] (y : ys) =
  not (null ys) || proper_interval (Just y) Nothing;
proper_interval_set_aux less proper_interval (x : xs) (y : ys) =
  (if less x y then False
    else (if less y x
           then proper_interval (Just y) (Just x) ||
                  (not (null ys) || not (exhaustive_above proper_interval x xs))
           else proper_interval_set_aux less proper_interval xs ys));

cproper_interval_set ::
  forall a.
    (Card_UNIV a, Ceq a, Cproper_interval a,
      Set_impl a) => Maybe (Set a) -> Maybe (Set a) -> Bool;
cproper_interval_set (Just (Complement (RBT_set rbt1))) (Just (RBT_set rbt2)) =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cproper_interval (Complement RBT_set) RBT_set: ccompare = None"
        (\ _ ->
          cproper_interval_set (Just (Complement (RBT_set rbt1)))
            (Just (RBT_set rbt2)));
    Just c ->
      (finite :: Set a -> Bool) (top_set :: Set a) &&
        proper_interval_Compl_set_aux_fusion (Comparator.lt_of_comp c)
          cproper_interval rbt_keys_generator rbt_keys_generator Nothing
          (init rbt1) (init rbt2);
  });
cproper_interval_set (Just (RBT_set rbt1)) (Just (Complement (RBT_set rbt2))) =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cproper_interval RBT_set (Complement RBT_set): ccompare = None"
        (\ _ ->
          cproper_interval_set (Just (RBT_set rbt1))
            (Just (Complement (RBT_set rbt2))));
    Just c ->
      (finite :: Set a -> Bool) (top_set :: Set a) &&
        proper_interval_set_Compl_aux_fusion (Comparator.lt_of_comp c)
          cproper_interval rbt_keys_generator rbt_keys_generator Nothing
          zero_nat (init rbt1) (init rbt2);
  });
cproper_interval_set (Just (RBT_set rbt1)) (Just (RBT_set rbt2)) =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cproper_interval RBT_set RBT_set: ccompare = None"
        (\ _ ->
          cproper_interval_set (Just (RBT_set rbt1)) (Just (RBT_set rbt2)));
    Just c ->
      (finite :: Set a -> Bool) (top_set :: Set a) &&
        proper_interval_set_aux_fusion (Comparator.lt_of_comp c)
          cproper_interval rbt_keys_generator rbt_keys_generator (init rbt1)
          (init rbt2);
  });
cproper_interval_set (Just (Complement a)) (Just (Complement b)) =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cproper_interval Complement Complement: ccompare = None"
        (\ _ ->
          cproper_interval_set (Just (Complement a)) (Just (Complement b)));
    Just _ -> cproper_interval_set (Just b) (Just a);
  });
cproper_interval_set (Just (Complement a)) (Just b) =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cproper_interval Complement1: ccompare = None"
        (\ _ -> cproper_interval_set (Just (Complement a)) (Just b));
    Just c ->
      (finite :: Set a -> Bool) (top_set :: Set a) &&
        proper_interval_Compl_set_aux (Comparator.lt_of_comp c) cproper_interval
          Nothing (csorted_list_of_set a) (csorted_list_of_set b);
  });
cproper_interval_set (Just a) (Just (Complement b)) =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cproper_interval Complement2: ccompare = None"
        (\ _ -> cproper_interval_set (Just a) (Just (Complement b)));
    Just c ->
      (finite :: Set a -> Bool) (top_set :: Set a) &&
        proper_interval_set_Compl_aux (Comparator.lt_of_comp c) cproper_interval
          Nothing zero_nat (csorted_list_of_set a) (csorted_list_of_set b);
  });
cproper_interval_set (Just a) (Just b) =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cproper_interval: ccompare = None"
        (\ _ -> cproper_interval_set (Just a) (Just b));
    Just c ->
      (finite :: Set a -> Bool) (top_set :: Set a) &&
        proper_interval_set_aux (Comparator.lt_of_comp c) cproper_interval
          (csorted_list_of_set a) (csorted_list_of_set b);
  });

instance (Card_UNIV a, Ceq a, Cproper_interval a,
           Set_impl a) => Cproper_interval (Set a) where {
  cproper_interval = cproper_interval_set;
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

ceq_list :: forall a. (Ceq a) => Maybe ([a] -> [a] -> Bool);
ceq_list = (case ceq of {
             Nothing -> Nothing;
             Just eq_a -> Just (Equality_Instances.equality_list eq_a);
           });

instance (Ceq a) => Ceq [a] where {
  ceq = ceq_list;
};

set_impl_list :: forall a. Phantom_Type.Phantom [a] Set_impla;
set_impl_list = Phantom_Type.Phantom Set_Choose;

instance Set_impl [a] where {
  set_impl = set_impl_list;
};

finite_UNIV_list :: forall a. Phantom_Type.Phantom [a] Bool;
finite_UNIV_list = Phantom_Type.Phantom False;

card_UNIV_list :: forall a. Phantom_Type.Phantom [a] Nat;
card_UNIV_list = Phantom_Type.Phantom zero_nat;

instance Finite_UNIV [a] where {
  finite_UNIV = finite_UNIV_list;
};

instance Card_UNIV [a] where {
  card_UNIV = card_UNIV_list;
};

cEnum_list ::
  forall a. Maybe ([[a]], (([a] -> Bool) -> Bool, ([a] -> Bool) -> Bool));
cEnum_list = Nothing;

instance Cenum [a] where {
  cEnum = cEnum_list;
};

ccompare_list ::
  forall a. (Ccompare a) => Maybe ([a] -> [a] -> Comparator.Order);
ccompare_list = (case ccompare of {
                  Nothing -> Nothing;
                  Just comp_a -> Just (comparator_list comp_a);
                });

instance (Ccompare a) => Ccompare [a] where {
  ccompare = ccompare_list;
};

cproper_interval_list ::
  forall a. (Ccompare a) => Maybe [a] -> Maybe [a] -> Bool;
cproper_interval_list xso yso = error "undefined";

instance (Ccompare a) => Cproper_interval [a] where {
  cproper_interval = cproper_interval_list;
};

newtype Char = Chr Integer;

integer_of_char :: Char -> Integer;
integer_of_char (Chr x) = x;

equal_char :: Char -> Char -> Bool;
equal_char c d = integer_of_char c == integer_of_char d;

instance Eq Char where {
  a == b = equal_char a b;
};

less_eq_char :: Char -> Char -> Bool;
less_eq_char c d = integer_of_char c <= integer_of_char d;

less_char :: Char -> Char -> Bool;
less_char c d = integer_of_char c < integer_of_char d;

instance Quasi_Order.Ord Char where {
  less_eq = less_eq_char;
  less = less_char;
};

instance Quasi_Order.Quasi_order Char where {
};

instance Quasi_Order.Weak_order Char where {
};

instance Quasi_Order.Preorder Char where {
};

instance Quasi_Order.Order Char where {
};

instance Quasi_Order.Linorder Char where {
};

compare_char :: Char -> Char -> Comparator.Order;
compare_char = Comparator.comparator_of;

instance Compare.Compare Char where {
  compare = compare_char;
};

ceq_char :: Maybe (Char -> Char -> Bool);
ceq_char = Just equal_char;

instance Ceq Char where {
  ceq = ceq_char;
};

instance Countable.Countable Char where {
};

instance Compare.Compare_order Char where {
};

ccompare_char :: Maybe (Char -> Char -> Comparator.Order);
ccompare_char = Just compare_char;

instance Ccompare Char where {
  ccompare = ccompare_char;
};

ceq_option :: forall a. (Ceq a) => Maybe (Maybe a -> Maybe a -> Bool);
ceq_option = (case ceq of {
               Nothing -> Nothing;
               Just eq_a -> Just (Equality_Instances.equality_option eq_a);
             });

instance (Ceq a) => Ceq (Maybe a) where {
  ceq = ceq_option;
};

set_impl_option ::
  forall a. (Set_impl a) => Phantom_Type.Phantom (Maybe a) Set_impla;
set_impl_option =
  Phantom_Type.Phantom
    (Phantom_Type.of_phantom (set_impl :: Phantom_Type.Phantom a Set_impla));

instance (Set_impl a) => Set_impl (Maybe a) where {
  set_impl = set_impl_option;
};

cEnum_option ::
  forall a.
    (Cenum a) => Maybe ([Maybe a],
                         ((Maybe a -> Bool) -> Bool,
                           (Maybe a -> Bool) -> Bool));
cEnum_option =
  (case cEnum of {
    Nothing -> Nothing;
    Just (enum_a, (enum_all_a, enum_ex_a)) ->
      Just (Nothing : map Just enum_a,
             ((\ p -> p Nothing && enum_all_a (\ x -> p (Just x))),
               (\ p -> p Nothing || enum_ex_a (\ x -> p (Just x)))));
  });

instance (Cenum a) => Cenum (Maybe a) where {
  cEnum = cEnum_option;
};

finite_UNIV_option ::
  forall a. (Finite_UNIV a) => Phantom_Type.Phantom (Maybe a) Bool;
finite_UNIV_option =
  Phantom_Type.Phantom
    (Phantom_Type.of_phantom (finite_UNIV :: Phantom_Type.Phantom a Bool));

instance (Finite_UNIV a) => Finite_UNIV (Maybe a) where {
  finite_UNIV = finite_UNIV_option;
};

comparator_option ::
  forall a.
    (a -> a -> Comparator.Order) -> Maybe a -> Maybe a -> Comparator.Order;
comparator_option comp_a Nothing Nothing = Comparator.Eqa;
comparator_option comp_a Nothing (Just y) = Comparator.Lt;
comparator_option comp_a (Just x) Nothing = Comparator.Gt;
comparator_option comp_a (Just x) (Just y) = comp_a x y;

ccompare_option ::
  forall a. (Ccompare a) => Maybe (Maybe a -> Maybe a -> Comparator.Order);
ccompare_option = (case ccompare of {
                    Nothing -> Nothing;
                    Just comp_a -> Just (comparator_option comp_a);
                  });

instance (Ccompare a) => Ccompare (Maybe a) where {
  ccompare = ccompare_option;
};

cproper_interval_option ::
  forall a. (Cproper_interval a) => Maybe (Maybe a) -> Maybe (Maybe a) -> Bool;
cproper_interval_option Nothing Nothing = True;
cproper_interval_option Nothing (Just x) = not (is_none x);
cproper_interval_option (Just x) Nothing = cproper_interval x Nothing;
cproper_interval_option (Just x) (Just Nothing) = False;
cproper_interval_option (Just x) (Just (Just y)) = cproper_interval x (Just y);

instance (Cproper_interval a) => Cproper_interval (Maybe a) where {
  cproper_interval = cproper_interval_option;
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

ceq_prod :: forall a b. (Ceq a, Ceq b) => Maybe ((a, b) -> (a, b) -> Bool);
ceq_prod =
  (case ceq of {
    Nothing -> Nothing;
    Just eq_a ->
      (case ceq of {
        Nothing -> Nothing;
        Just eq_b -> Just (Equality_Instances.equality_prod eq_a eq_b);
      });
  });

instance (Ceq a, Ceq b) => Ceq (a, b) where {
  ceq = ceq_prod;
};

set_impl_choose2 :: Set_impla -> Set_impla -> Set_impla;
set_impl_choose2 Set_Monada Set_Monada = Set_Monada;
set_impl_choose2 Set_RBT Set_RBT = Set_RBT;
set_impl_choose2 Set_DList Set_DList = Set_DList;
set_impl_choose2 Set_Collect Set_Collect = Set_Collect;
set_impl_choose2 x y = Set_Choose;

set_impl_prod ::
  forall a b. (Set_impl a, Set_impl b) => Phantom_Type.Phantom (a, b) Set_impla;
set_impl_prod =
  Phantom_Type.Phantom
    (set_impl_choose2
      (Phantom_Type.of_phantom (set_impl :: Phantom_Type.Phantom a Set_impla))
      (Phantom_Type.of_phantom (set_impl :: Phantom_Type.Phantom b Set_impla)));

instance (Set_impl a, Set_impl b) => Set_impl (a, b) where {
  set_impl = set_impl_prod;
};

finite_UNIV_prod ::
  forall a b.
    (Finite_UNIV a, Finite_UNIV b) => Phantom_Type.Phantom (a, b) Bool;
finite_UNIV_prod =
  Phantom_Type.Phantom
    (Phantom_Type.of_phantom (finite_UNIV :: Phantom_Type.Phantom a Bool) &&
      Phantom_Type.of_phantom (finite_UNIV :: Phantom_Type.Phantom b Bool));

card_UNIV_prod ::
  forall a b. (Card_UNIV a, Card_UNIV b) => Phantom_Type.Phantom (a, b) Nat;
card_UNIV_prod =
  Phantom_Type.Phantom
    (times_nat
      (Phantom_Type.of_phantom (card_UNIV :: Phantom_Type.Phantom a Nat))
      (Phantom_Type.of_phantom (card_UNIV :: Phantom_Type.Phantom b Nat)));

instance (Finite_UNIV a, Finite_UNIV b) => Finite_UNIV (a, b) where {
  finite_UNIV = finite_UNIV_prod;
};

instance (Card_UNIV a, Card_UNIV b) => Card_UNIV (a, b) where {
  card_UNIV = card_UNIV_prod;
};

product :: forall a b. [a] -> [b] -> [(a, b)];
product [] uu = [];
product (x : xs) ys = map (\ a -> (x, a)) ys ++ product xs ys;

cEnum_prod ::
  forall a b.
    (Cenum a,
      Cenum b) => Maybe ([(a, b)],
                          (((a, b) -> Bool) -> Bool, ((a, b) -> Bool) -> Bool));
cEnum_prod =
  (case cEnum of {
    Nothing -> Nothing;
    Just (enum_a, (enum_all_a, enum_ex_a)) ->
      (case cEnum of {
        Nothing -> Nothing;
        Just (enum_b, (enum_all_b, enum_ex_b)) ->
          Just (product enum_a enum_b,
                 ((\ p -> enum_all_a (\ x -> enum_all_b (\ y -> p (x, y)))),
                   (\ p -> enum_ex_a (\ x -> enum_ex_b (\ y -> p (x, y))))));
      });
  });

instance (Cenum a, Cenum b) => Cenum (a, b) where {
  cEnum = cEnum_prod;
};

ccompare_prod ::
  forall a b.
    (Ccompare a, Ccompare b) => Maybe ((a, b) -> (a, b) -> Comparator.Order);
ccompare_prod =
  (case ccompare of {
    Nothing -> Nothing;
    Just comp_a -> (case ccompare of {
                     Nothing -> Nothing;
                     Just comp_b -> Just (comparator_prod comp_a comp_b);
                   });
  });

instance (Ccompare a, Ccompare b) => Ccompare (a, b) where {
  ccompare = ccompare_prod;
};

cproper_interval_prod ::
  forall a b.
    (Cproper_interval a,
      Cproper_interval b) => Maybe (a, b) -> Maybe (a, b) -> Bool;
cproper_interval_prod Nothing Nothing = True;
cproper_interval_prod Nothing (Just (y1, y2)) =
  cproper_interval Nothing (Just y1) || cproper_interval Nothing (Just y2);
cproper_interval_prod (Just (x1, x2)) Nothing =
  cproper_interval (Just x1) Nothing || cproper_interval (Just x2) Nothing;
cproper_interval_prod (Just (x1, x2)) (Just (y1, y2)) =
  cproper_interval (Just x1) (Just y1) ||
    (Comparator.lt_of_comp (the ccompare) x1 y1 &&
       (cproper_interval (Just x2) Nothing ||
         cproper_interval Nothing (Just y2)) ||
      not (Comparator.lt_of_comp (the ccompare) y1 x1) &&
        cproper_interval (Just x2) (Just y2));

instance (Cproper_interval a,
           Cproper_interval b) => Cproper_interval (a, b) where {
  cproper_interval = cproper_interval_prod;
};

comparator_unit :: () -> () -> Comparator.Order;
comparator_unit x y = Comparator.Eqa;

compare_unit :: () -> () -> Comparator.Order;
compare_unit = comparator_unit;

instance Compare.Compare () where {
  compare = compare_unit;
};

instance Quasi_Order.Quasi_order Integer where {
};

instance Quasi_Order.Weak_order Integer where {
};

instance Quasi_Order.Preorder Integer where {
};

instance Quasi_Order.Order Integer where {
};

instance Quasi_Order.Linorder Integer where {
};

compare_integer :: Integer -> Integer -> Comparator.Order;
compare_integer = Comparator.comparator_of;

instance Compare.Compare Integer where {
  compare = compare_integer;
};

ceq_integer :: Maybe (Integer -> Integer -> Bool);
ceq_integer = Just (\ a b -> a == b);

instance Ceq Integer where {
  ceq = ceq_integer;
};

set_impl_integer :: Phantom_Type.Phantom Integer Set_impla;
set_impl_integer = Phantom_Type.Phantom Set_RBT;

instance Set_impl Integer where {
  set_impl = set_impl_integer;
};

finite_UNIV_integer :: Phantom_Type.Phantom Integer Bool;
finite_UNIV_integer = Phantom_Type.Phantom False;

card_UNIV_integer :: Phantom_Type.Phantom Integer Nat;
card_UNIV_integer = Phantom_Type.Phantom zero_nat;

instance Finite_UNIV Integer where {
  finite_UNIV = finite_UNIV_integer;
};

instance Card_UNIV Integer where {
  card_UNIV = card_UNIV_integer;
};

cEnum_integer ::
  Maybe ([Integer], ((Integer -> Bool) -> Bool, (Integer -> Bool) -> Bool));
cEnum_integer = Nothing;

instance Cenum Integer where {
  cEnum = cEnum_integer;
};

instance Compare.Compare_order Integer where {
};

ccompare_integer :: Maybe (Integer -> Integer -> Comparator.Order);
ccompare_integer = Just compare_integer;

instance Ccompare Integer where {
  ccompare = ccompare_integer;
};

class (One a, Zero a, Dvd a) => Gcda a where {
  gcda :: a -> a -> a;
  lcma :: a -> a -> a;
};

class (Gcda a) => Gcd a where {
  gcd :: Set a -> a;
  lcm :: Set a -> a;
};

class (Idom a, Semidom_divide a) => Idom_divide a where {
};

class (Idom a) => Ufd a where {
};

class (Divide a) => Inverse a where {
  inverse :: a -> a;
};

class (Inverse a, Divide_trivial a,
        Ring_1_no_zero_divisors a) => Division_ring a where {
};

class (Division_ring a, Idom_divide a, Ufd a) => Field a where {
};

class (Gcda a, Comm_semiring_1 a) => Comm_monoid_gcd a where {
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

class (Normalization_semidom a, Comm_monoid_gcd a) => Semiring_gcd a where {
};

class (Idom a, Comm_monoid_gcd a) => Idom_gcd a where {
};

class (Semiring_gcd a, Idom_gcd a) => Ring_gcd a where {
};

class (Gcd a, Semiring_gcd a) => Semiring_Gcd a where {
};

class (Field a, Ring_char_0 a) => Field_char_0 a where {
};

class (Field a, Idom_abs_sgn a) => Field_abs_sgn a where {
};

class (Field_abs_sgn a, Field_char_0 a, Quasi_Order.Unbounded_dense_linorder a,
        Linordered_idom a) => Linordered_field a where {
};

class (Normalization_semidom a) => Normalization_semidom_multiplicative a where {
};

class (Semiring_gcd a,
        Normalization_semidom_multiplicative a) => Semiring_gcd_mult_normalize a where {
};

class (Semidom_modulo a) => Euclidean_semiring a where {
  euclidean_size :: a -> Nat;
};

newtype Comp_fun_idem b a = Abs_comp_fun_idem (b -> a -> a);

newtype Semilattice_set a = Abs_semilattice_set (a -> a -> a);

nat :: Int -> Nat;
nat = nat_of_integer . integer_of_int;

dlist_ex :: forall a. (Ceq a) => (a -> Bool) -> Set_dlist a -> Bool;
dlist_ex x xc = any x (list_of_dlist xc);

rBT_Impl_rbt_ex :: forall a b. (a -> b -> Bool) -> Rbt a b -> Bool;
rBT_Impl_rbt_ex p Empty = False;
rBT_Impl_rbt_ex p (Branch c l k v r) =
  p k v || (rBT_Impl_rbt_ex p l || rBT_Impl_rbt_ex p r);

ex :: forall a b. (Ccompare a) => (a -> b -> Bool) -> Mapping_rbt a b -> Bool;
ex xb xc = rBT_Impl_rbt_ex xb (impl_of xc);

bex :: forall a. (Ceq a, Ccompare a) => Set a -> (a -> Bool) -> Bool;
bex (RBT_set rbt) p =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "Bex RBT_set: ccompare = None" (\ _ -> bex (RBT_set rbt) p);
    Just _ -> ex (\ k _ -> p k) rbt;
  });
bex (DList_set dxs) p =
  (case (ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a) "Bex DList_set: ceq = None"
        (\ _ -> bex (DList_set dxs) p);
    Just _ -> dlist_ex p dxs;
  });
bex (Set_Monad xs) p = any p xs;

nth :: forall a. [a] -> Nat -> a;
nth (x : xs) n =
  (if equal_nat n zero_nat then x else nth xs (minus_nat n one_nat));

upt :: Nat -> Nat -> [Nat];
upt i j = (if less_nat i j then i : upt (suc i) j else []);

rBT_Impl_rbt_all :: forall a b. (a -> b -> Bool) -> Rbt a b -> Bool;
rBT_Impl_rbt_all p Empty = True;
rBT_Impl_rbt_all p (Branch c l k v r) =
  p k v && rBT_Impl_rbt_all p l && rBT_Impl_rbt_all p r;

alla :: forall a b. (Ccompare a) => (a -> b -> Bool) -> Mapping_rbt a b -> Bool;
alla xb xc = rBT_Impl_rbt_all xb (impl_of xc);

ball :: forall a. (Ceq a, Ccompare a) => Set a -> (a -> Bool) -> Bool;
ball (RBT_set rbt) p =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "Ball RBT_set: ccompare = None" (\ _ -> ball (RBT_set rbt) p);
    Just _ -> alla (\ k _ -> p k) rbt;
  });
ball (DList_set dxs) p =
  (case (ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a) "Ball DList_set: ceq = None"
        (\ _ -> ball (DList_set dxs) p);
    Just _ -> dlist_all p dxs;
  });
ball (Set_Monad xs) p = all p xs;

drop :: forall a. Nat -> [a] -> [a];
drop n [] = [];
drop n (x : xs) =
  (if equal_nat n zero_nat then x : xs else drop (minus_nat n one_nat) xs);

find :: forall a. (a -> Bool) -> [a] -> Maybe a;
find uu [] = Nothing;
find p (x : xs) = (if p x then Just x else find p xs);

last :: forall a. [a] -> a;
last (x : xs) = (if null xs then x else last xs);

take :: forall a. Nat -> [a] -> [a];
take n [] = [];
take n (x : xs) =
  (if equal_nat n zero_nat then [] else x : take (minus_nat n one_nat) xs);

foldb ::
  forall a b. (Ccompare a) => (a -> b -> b) -> Mapping_rbt a () -> b -> b;
foldb x xc = folda (\ a _ -> x a) (impl_of xc);

image ::
  forall a b.
    (Ceq a, Ccompare a, Ceq b, Ccompare b,
      Set_impl b) => (a -> b) -> Set a -> Set b;
image h (RBT_set rbt) =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "image RBT_set: ccompare = None" (\ _ -> image h (RBT_set rbt));
    Just _ -> foldb (insert . h) rbt bot_set;
  });
image g (DList_set dxs) =
  (case (ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "image DList_set: ceq = None" (\ _ -> image g (DList_set dxs));
    Just _ -> foldc (insert . g) dxs bot_set;
  });
image f (Complement (Complement b)) = image f b;
image f (Collect_set a) =
  (error :: forall a. String -> (() -> a) -> a) "image Collect_set"
    (\ _ -> image f (Collect_set a));
image f (Set_Monad xs) = Set_Monad (map f xs);

foldr :: forall a b. (a -> b -> b) -> [a] -> b -> b;
foldr f [] = id;
foldr f (x : xs) = f x . foldr f xs;

map_option :: forall a b. (a -> b) -> Maybe a -> Maybe b;
map_option f Nothing = Nothing;
map_option f (Just x2) = Just (f x2);

those :: forall a. [Maybe a] -> Maybe [a];
those [] = Just [];
those (x : xs) = (case x of {
                   Nothing -> Nothing;
                   Just y -> map_option (\ a -> y : a) (those xs);
                 });

membera :: forall a. (Eq a) => [a] -> a -> Bool;
membera [] y = False;
membera (x : xs) y = x == y || membera xs y;

inserta :: forall a. (Eq a) => a -> [a] -> [a];
inserta x xs = (if membera xs x then xs else x : xs);

union :: forall a. (Eq a) => [a] -> [a] -> [a];
union = fold inserta;

funpow :: forall a. Nat -> (a -> a) -> a -> a;
funpow n f =
  (if equal_nat n zero_nat then id else f . funpow (minus_nat n one_nat) f);

filtera :: forall a. (Ceq a, Ccompare a) => (a -> Bool) -> Set a -> Set a;
filtera p a = inf_set a (Collect_set p);

bind :: forall a b. Maybe a -> (a -> Maybe b) -> Maybe b;
bind Nothing f = Nothing;
bind (Just x) f = f x;

hda :: forall a. [a] -> a;
hda (x21 : x22) = x21;

hd :: forall a. (Ceq a) => Set_dlist a -> a;
hd xa = hda (list_of_dlist xa);

tla :: forall a. [a] -> [a];
tla [] = [];
tla (x21 : x22) = x22;

tl :: forall a. (Ceq a) => Set_dlist a -> Set_dlist a;
tl xa = Abs_dlist (tla (list_of_dlist xa));

butlast :: forall a. [a] -> [a];
butlast [] = [];
butlast (x : xs) = (if null xs then [] else x : butlast xs);

extract :: forall a. (a -> Bool) -> [a] -> Maybe ([a], (a, [a]));
extract p [] = Nothing;
extract p (x : xs) =
  (if p x then Just ([], (x, xs))
    else (case extract p xs of {
           Nothing -> Nothing;
           Just (ys, (y, zs)) -> Just (x : ys, (y, zs));
         }));

productb ::
  forall a b. (Ceq a, Ceq b) => Set_dlist a -> Set_dlist b -> Set_dlist (a, b);
productb dxs1 dxs2 =
  Abs_dlist (foldc (\ a -> foldc (\ c -> (\ b -> (a, c) : b)) dxs2) dxs1 []);

rbt_product ::
  forall a b c d e.
    (a -> b -> c -> d -> e) -> Rbt a b -> Rbt c d -> Rbt (a, c) e;
rbt_product f rbt1 rbt2 =
  rbtreeify
    (reverse
      (folda (\ a b -> folda (\ c d -> (\ e -> ((a, c), f a b c d) : e)) rbt2)
        rbt1 []));

productd ::
  forall a d b e c.
    (Ccompare a,
      Ccompare b) => (a -> d -> b -> e -> c) ->
                       Mapping_rbt a d ->
                         Mapping_rbt b e -> Mapping_rbt (a, b) c;
productd xc xd xe = Mapping_RBT (rbt_product xc (impl_of xd) (impl_of xe));

producta ::
  forall a b.
    (Ccompare a,
      Ccompare b) => Mapping_rbt a () ->
                       Mapping_rbt b () -> Mapping_rbt (a, b) ();
producta rbt1 rbt2 = productd (\ _ _ _ _ -> ()) rbt1 rbt2;

productc ::
  forall a b.
    (Ceq a, Ccompare a, Set_impl a, Ceq b, Ccompare b,
      Set_impl b) => Set a -> Set b -> Set (a, b);
productc (RBT_set rbt1) (RBT_set rbt2) =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "product RBT_set RBT_set: ccompare1 = None"
        (\ _ -> productc (RBT_set rbt1) (RBT_set rbt2));
    Just _ ->
      (case (ccompare :: Maybe (b -> b -> Comparator.Order)) of {
        Nothing ->
          (error :: forall a. String -> (() -> a) -> a)
            "product RBT_set RBT_set: ccompare2 = None"
            (\ _ -> productc (RBT_set rbt1) (RBT_set rbt2));
        Just _ -> RBT_set (producta rbt1 rbt2);
      });
  });
productc a2 (RBT_set rbt2) =
  (case (ccompare :: Maybe (b -> b -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "product RBT_set: ccompare2 = None" (\ _ -> productc a2 (RBT_set rbt2));
    Just _ -> foldb (\ y -> sup_set (image (\ x -> (x, y)) a2)) rbt2 bot_set;
  });
productc (RBT_set rbt1) b2 =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "product RBT_set: ccompare1 = None" (\ _ -> productc (RBT_set rbt1) b2);
    Just _ -> foldb (\ x -> sup_set (image (\ a -> (x, a)) b2)) rbt1 bot_set;
  });
productc (DList_set dxs) (DList_set dys) =
  (case (ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "product DList_set DList_set: ceq1 = None"
        (\ _ -> productc (DList_set dxs) (DList_set dys));
    Just _ ->
      (case (ceq :: Maybe (b -> b -> Bool)) of {
        Nothing ->
          (error :: forall a. String -> (() -> a) -> a)
            "product DList_set DList_set: ceq2 = None"
            (\ _ -> productc (DList_set dxs) (DList_set dys));
        Just _ -> DList_set (productb dxs dys);
      });
  });
productc a1 (DList_set dys) =
  (case (ceq :: Maybe (b -> b -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "product DList_set2: ceq = None" (\ _ -> productc a1 (DList_set dys));
    Just _ -> foldc (\ y -> sup_set (image (\ x -> (x, y)) a1)) dys bot_set;
  });
productc (DList_set dxs) b1 =
  (case (ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "product DList_set1: ceq = None" (\ _ -> productc (DList_set dxs) b1);
    Just _ -> foldc (\ x -> sup_set (image (\ a -> (x, a)) b1)) dxs bot_set;
  });
productc (Set_Monad xs) (Set_Monad ys) =
  Set_Monad (fold (\ x -> fold (\ y -> (\ a -> (x, y) : a)) ys) xs []);
productc a b = Collect_set (\ (x, y) -> member x a && member y b);

set_Cons ::
  forall a. (Ceq a, Ccompare a, Set_impl a) => Set a -> Set [a] -> Set [a];
set_Cons a xs =
  image (\ (aa, b) -> aa : b)
    (productc (inf_set (image (\ x -> x) a) top_set)
      (inf_set top_set (image (\ xsa -> xsa) xs)));

listset :: forall a. (Ceq a, Ccompare a, Set_impl a) => [Set a] -> Set [a];
listset [] = insert [] (set_empty (Phantom_Type.of_phantom set_impl_list));
listset (a : asa) = set_Cons a (listset asa);

remdups :: forall a. (Eq a) => [a] -> [a];
remdups [] = [];
remdups (x : xs) = (if membera xs x then remdups xs else x : remdups xs);

remove1 :: forall a. (Eq a) => a -> [a] -> [a];
remove1 x [] = [];
remove1 x (y : xs) = (if x == y then xs else y : remove1 x xs);

image_filter ::
  forall a b.
    (Ceq a, Ccompare a, Ceq b, Ccompare b,
      Set_impl b) => (a -> Maybe b) -> Set a -> Set b;
image_filter h (RBT_set rbt) =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "Option.image_filter RBT_set: ccompare = None"
        (\ _ -> image_filter h (RBT_set rbt));
    Just _ -> foldb (\ x a -> (case h x of {
                                Nothing -> a;
                                Just y -> insert y a;
                              }))
                rbt bot_set;
  });
image_filter g (DList_set dxs) =
  (case (ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "Option.image_filter DList_set: ceq = None"
        (\ _ -> image_filter g (DList_set dxs));
    Just _ -> foldc (\ x a -> (case g x of {
                                Nothing -> a;
                                Just y -> insert y a;
                              }))
                dxs bot_set;
  });
image_filter f (Set_Monad xs) = Set_Monad (map_filter f xs);

these :: forall a. (Ceq a, Ccompare a, Set_impl a) => Set (Maybe a) -> Set a;
these a = image_filter (\ x -> x) a;

mapa :: forall a b c. (a -> b -> c) -> Rbt a b -> Rbt a c;
mapa f Empty = Empty;
mapa f (Branch c lt k v rt) = Branch c (mapa f lt) k (f k v) (mapa f rt);

is_emptya :: forall a b. (Ccompare a) => Mapping_rbt a b -> Bool;
is_emptya xa = (case impl_of xa of {
                 Empty -> True;
                 Branch _ _ _ _ _ -> False;
               });

exhaustive_fusion ::
  forall a b. (Maybe a -> Maybe a -> Bool) -> Generator a b -> b -> Bool;
exhaustive_fusion proper_interval g s =
  has_next g s &&
    (case next g s of {
      (x, sa) ->
        not (proper_interval Nothing (Just x)) &&
          exhaustive_above_fusion proper_interval g x sa;
    });

is_UNIV :: forall a. (Card_UNIV a, Ceq a, Cproper_interval a) => Set a -> Bool;
is_UNIV (RBT_set rbt) =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "is_UNIV RBT_set: ccompare = None" (\ _ -> is_UNIV (RBT_set rbt));
    Just _ ->
      Phantom_Type.of_phantom (finite_UNIV :: Phantom_Type.Phantom a Bool) &&
        exhaustive_fusion cproper_interval rbt_keys_generator (init rbt);
  });
is_UNIV a =
  let {
    aa = Phantom_Type.of_phantom (card_UNIV :: Phantom_Type.Phantom a Nat);
    b = card a;
  } in (if less_nat zero_nat aa then equal_nat aa b
         else (if less_nat zero_nat b then False
                else (error :: forall a. String -> (() -> a) -> a)
                       "is_UNIV called on infinite type and set"
                       (\ _ -> is_UNIV a)));

nulla :: forall a. (Ceq a) => Set_dlist a -> Bool;
nulla xa = null (list_of_dlist xa);

is_empty :: forall a. (Card_UNIV a, Ceq a, Cproper_interval a) => Set a -> Bool;
is_empty (Complement a) = is_UNIV a;
is_empty (RBT_set rbt) =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "is_empty RBT_set: ccompare = None" (\ _ -> is_empty (RBT_set rbt));
    Just _ -> is_emptya rbt;
  });
is_empty (DList_set dxs) =
  (case (ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "is_empty DList_set: ceq = None" (\ _ -> is_empty (DList_set dxs));
    Just _ -> nulla dxs;
  });
is_empty (Set_Monad xs) = null xs;

distinct :: forall a. (Eq a) => [a] -> Bool;
distinct [] = True;
distinct (x : xs) = not (membera xs x) && distinct xs;

superset :: forall a. (Eq a) => [a] -> [a] -> Bool;
superset xs = all (membera xs);

enumerate :: forall a. Nat -> [a] -> [(Nat, a)];
enumerate n [] = [];
enumerate n (x : xs) = (n, x) : enumerate (suc n) xs;

partition :: forall a. (a -> Bool) -> [a] -> ([a], [a]);
partition p [] = ([], []);
partition p (x : xs) =
  (case partition p xs of {
    (yes, no) -> (if p x then (x : yes, no) else (yes, x : no));
  });

removeAll :: forall a. (Eq a) => a -> [a] -> [a];
removeAll x [] = [];
removeAll x (y : xs) = (if x == y then removeAll x xs else y : removeAll x xs);

replicate :: forall a. Nat -> a -> [a];
replicate n x =
  (if equal_nat n zero_nat then [] else x : replicate (minus_nat n one_nat) x);

rBT_Impl_fold1 :: forall a. (a -> a -> a) -> Rbt a () -> a;
rBT_Impl_fold1 f Empty = error "undefined";
rBT_Impl_fold1 f (Branch c Empty k v r) = folda (\ ka _ -> f ka) r k;
rBT_Impl_fold1 f (Branch ca (Branch c l ka va ra) k v r) =
  folda (\ kb _ -> f kb) r (f k (rBT_Impl_fold1 f (Branch c l ka va ra)));

fold1 :: forall a. (Ccompare a) => (a -> a -> a) -> Mapping_rbt a () -> a;
fold1 x xc = rBT_Impl_fold1 x (impl_of xc);

filter_comp_minus ::
  forall a b c. (a -> a -> Comparator.Order) -> Rbt a b -> Rbt a c -> [(a, b)];
filter_comp_minus c t1 t2 =
  filter (\ (k, _) -> is_none (rbt_comp_lookup c t2 k)) (entries t1);

small_rbt :: forall a b. Rbt a b -> Bool;
small_rbt t = less_nat (bheight t) (nat_of_integer (4 :: Integer));

comp_minus ::
  forall a b. (a -> a -> Comparator.Order) -> Rbt a b -> Rbt a b -> Rbt a b;
comp_minus c t1 t2 =
  (if small_rbt t2 then folda (\ k _ -> rbt_comp_delete c k) t2 t1
    else (if small_rbt t1 then rbtreeify (filter_comp_minus c t1 t2)
           else (case t2 of {
                  Empty -> t1;
                  Branch _ l2 a _ r2 ->
                    (case rbt_split_comp c t1 a of {
                      (l1, (_, r1)) ->
                        rbt_join2 (comp_minus c l1 l2) (comp_minus c r1 r2);
                    });
                })));

rbt_comp_minus ::
  forall a b. (a -> a -> Comparator.Order) -> Rbt a b -> Rbt a b -> Rbt a b;
rbt_comp_minus c t1 t2 = paint B (comp_minus c t1 t2);

minus ::
  forall a.
    (Ccompare a) => Mapping_rbt a () -> Mapping_rbt a () -> Mapping_rbt a ();
minus xb xc =
  Mapping_RBT (rbt_comp_minus (the ccompare) (impl_of xb) (impl_of xc));

implode :: [Char] -> String;
implode cs = Str_Literal.literalOfAsciis (map integer_of_char cs);

list_update :: forall a. [a] -> Nat -> a -> [a];
list_update [] i y = [];
list_update (x : xs) i y =
  (if equal_nat i zero_nat then y : xs
    else x : list_update xs (minus_nat i one_nat) y);

remdups_adj :: forall a. (Eq a) => [a] -> [a];
remdups_adj [] = [];
remdups_adj [x] = [x];
remdups_adj (x : y : xs) =
  (if x == y then remdups_adj (x : xs) else x : remdups_adj (y : xs));

max_sls :: forall a. (Quasi_Order.Linorder a) => Semilattice_set a;
max_sls = Abs_semilattice_set Quasi_Order.max;

sup_cfi :: forall a. (Quasi_Order.Lattice a) => Comp_fun_idem a a;
sup_cfi = Abs_comp_fun_idem Quasi_Order.sup;

flip_rbt :: forall a b. Rbt a b -> Rbt a b -> Bool;
flip_rbt t1 t2 = less_nat (bheight t2) (bheight t1);

rec_list :: forall a b. a -> (b -> [b] -> a -> a) -> [b] -> a;
rec_list f1 f2 [] = f1;
rec_list f1 f2 (x21 : x22) = f2 x21 x22 (rec_list f1 f2 x22);

product_lists :: forall a. [[a]] -> [[a]];
product_lists [] = [[]];
product_lists (xs : xss) =
  concatMap (\ x -> map (\ a -> x : a) (product_lists xss)) xs;

curry :: forall a b c. ((a, b) -> c) -> a -> b -> c;
curry f a b = f (a, b);

semilattice_set_apply :: forall a. Semilattice_set a -> a -> a -> a;
semilattice_set_apply (Abs_semilattice_set x) = x;

set_fold1 ::
  forall a.
    (Ceq a, Ccompare a,
      Quasi_Order.Lattice a) => Semilattice_set a -> Set a -> a;
set_fold1 f (RBT_set rbt) =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "set_fold1 RBT_set: ccompare = None" (\ _ -> set_fold1 f (RBT_set rbt));
    Just _ ->
      (if is_emptya rbt
        then (error :: forall a. String -> (() -> a) -> a)
               "set_fold1 RBT_set: empty set" (\ _ -> set_fold1 f (RBT_set rbt))
        else fold1 (semilattice_set_apply f) rbt);
  });
set_fold1 f (DList_set dxs) =
  (case (ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "set_fold1 DList_set: ceq = None" (\ _ -> set_fold1 f (DList_set dxs));
    Just _ ->
      (if nulla dxs
        then (error :: forall a. String -> (() -> a) -> a)
               "set_fold1 DList_set: empty set"
               (\ _ -> set_fold1 f (DList_set dxs))
        else foldc (semilattice_set_apply f) (tl dxs) (hd dxs));
  });
set_fold1 f (Set_Monad (x : xs)) = fold (semilattice_set_apply f) xs x;
set_fold1 f (Collect_set p) =
  (error :: forall a. String -> (() -> a) -> a) "set_fold1: Collect_set"
    (\ _ -> set_fold1 f (Collect_set p));
set_fold1 f (Complement a) =
  (error :: forall a. String -> (() -> a) -> a) "set_fold1: Complement"
    (\ _ -> set_fold1 f (Complement a));

inter_list_set :: forall a. (Eq a) => [a] -> [a] -> [a];
inter_list_set xs ys = filter (membera ys) xs;

list_all2 :: forall a b. (a -> b -> Bool) -> [a] -> [b] -> Bool;
list_all2 p [] ys = null ys;
list_all2 p xs [] = null xs;
list_all2 p (x : xs) (y : ys) = p x y && list_all2 p xs ys;

dvd :: forall a. (Eq a, Semidom_modulo a) => a -> a -> Bool;
dvd a b = modulo b a == zero;

rbt_ins ::
  forall a b.
    (a -> a -> Bool) -> (a -> b -> b -> b) -> a -> b -> Rbt a b -> Rbt a b;
rbt_ins less f k v Empty = Branch R Empty k v Empty;
rbt_ins less f k v (Branch B l x y r) =
  (if less k x then balance (rbt_ins less f k v l) x y r
    else (if less x k then balance l x y (rbt_ins less f k v r)
           else Branch B l x (f k y v) r));
rbt_ins less f k v (Branch R l x y r) =
  (if less k x then Branch R (rbt_ins less f k v l) x y r
    else (if less x k then Branch R l x y (rbt_ins less f k v r)
           else Branch R l x (f k y v) r));

comp_fun_idem_apply :: forall b a. Comp_fun_idem b a -> b -> a -> a;
comp_fun_idem_apply (Abs_comp_fun_idem x) = x;

set_fold_cfi ::
  forall a b. (Ceq a, Ccompare a) => Comp_fun_idem a b -> b -> Set a -> b;
set_fold_cfi f b (RBT_set rbt) =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "set_fold_cfi RBT_set: ccompare = None"
        (\ _ -> set_fold_cfi f b (RBT_set rbt));
    Just _ -> foldb (comp_fun_idem_apply f) rbt b;
  });
set_fold_cfi f b (DList_set dxs) =
  (case (ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "set_fold_cfi DList_set: ceq = None"
        (\ _ -> set_fold_cfi f b (DList_set dxs));
    Just _ -> foldc (comp_fun_idem_apply f) dxs b;
  });
set_fold_cfi f b (Set_Monad xs) = fold (comp_fun_idem_apply f) xs b;
set_fold_cfi f b (Collect_set p) =
  (error :: forall a. String -> (() -> a) -> a)
    "set_fold_cfi not supported on Collect_set"
    (\ _ -> set_fold_cfi f b (Collect_set p));
set_fold_cfi f b (Complement a) =
  (error :: forall a. String -> (() -> a) -> a)
    "set_fold_cfi not supported on Complement"
    (\ _ -> set_fold_cfi f b (Complement a));

swap :: forall a b. (a, b) -> (b, a);
swap p = (snd p, fst p);

char_of_integer :: Integer -> Char;
char_of_integer k =
  Chr (if (0 :: Integer) <= k && k < (256 :: Integer) then k
        else modulo_integer k (256 :: Integer));

explode :: String -> [Char];
explode s = map char_of_integer (Str_Literal.asciisOfLiteral s);

power :: forall a. (Power a) => a -> Nat -> a;
power a n =
  (if equal_nat n zero_nat then one
    else times a (power a (minus_nat n one_nat)));

rbt_insert_with_key ::
  forall a b.
    (a -> a -> Bool) -> (a -> b -> b -> b) -> a -> b -> Rbt a b -> Rbt a b;
rbt_insert_with_key less f k v t = paint B (rbt_ins less f k v t);

rbt_insert :: forall a b. (a -> a -> Bool) -> a -> b -> Rbt a b -> Rbt a b;
rbt_insert less = rbt_insert_with_key less (\ _ _ nv -> nv);

rbt_lookup :: forall a b. (a -> a -> Bool) -> Rbt a b -> a -> Maybe b;
rbt_lookup less Empty k = Nothing;
rbt_lookup less (Branch uu l x y r) k =
  (if less k x then rbt_lookup less l k
    else (if less x k then rbt_lookup less r k else Just y));

gcd_int :: Int -> Int -> Int;
gcd_int (Int_of_integer x) (Int_of_integer y) =
  Int_of_integer (Prelude.gcd x y);

lcm_integer :: Integer -> Integer -> Integer;
lcm_integer a b =
  divide_integer (Prelude.abs a * Prelude.abs b) (Prelude.gcd a b);

lcm_int :: Int -> Int -> Int;
lcm_int (Int_of_integer x) (Int_of_integer y) =
  Int_of_integer (lcm_integer x y);

rel_option :: forall a b. (a -> b -> Bool) -> Maybe a -> Maybe b -> Bool;
rel_option r Nothing (Just y2) = False;
rel_option r (Just y2) Nothing = False;
rel_option r Nothing Nothing = True;
rel_option r (Just x2) (Just y2) = r x2 y2;

set_option :: forall a. (Ceq a, Ccompare a, Set_impl a) => Maybe a -> Set a;
set_option Nothing = bot_set;
set_option (Just x2) = insert x2 bot_set;

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

rbt_del :: forall a b. (Compare.Compare_order a) => a -> Rbt a b -> Rbt a b;
rbt_del x Empty = Empty;
rbt_del x (Branch c a y s b) = (case Compare.compare x y of {
                                 Comparator.Eqa -> combine a b;
                                 Comparator.Lt -> rbt_del_from_left x a y s b;
                                 Comparator.Gt -> rbt_del_from_right x a y s b;
                               });

rbt_del_from_left ::
  forall a b.
    (Compare.Compare_order a) => a -> Rbt a b -> a -> b -> Rbt a b -> Rbt a b;
rbt_del_from_left x (Branch B lt z v rt) y s b =
  balance_left (rbt_del x (Branch B lt z v rt)) y s b;
rbt_del_from_left x Empty y s b = Branch R (rbt_del x Empty) y s b;
rbt_del_from_left x (Branch R va vb vc vd) y s b =
  Branch R (rbt_del x (Branch R va vb vc vd)) y s b;

rbt_del_from_right ::
  forall a b.
    (Compare.Compare_order a) => a -> Rbt a b -> a -> b -> Rbt a b -> Rbt a b;
rbt_del_from_right x a y s (Branch B lt z v rt) =
  balance_right a y s (rbt_del x (Branch B lt z v rt));
rbt_del_from_right x a y s Empty = Branch R a y s (rbt_del x Empty);
rbt_del_from_right x a y s (Branch R va vb vc vd) =
  Branch R a y s (rbt_del x (Branch R va vb vc vd));

rbt_insa ::
  forall a b.
    (Compare.Compare_order a) => (a -> b -> b -> b) ->
                                   a -> b -> Rbt a b -> Rbt a b;
rbt_insa f k v Empty = Branch R Empty k v Empty;
rbt_insa f k v (Branch B l x y r) =
  (case Compare.compare k x of {
    Comparator.Eqa -> Branch B l x (f k y v) r;
    Comparator.Lt -> balance (rbt_insa f k v l) x y r;
    Comparator.Gt -> balance l x y (rbt_insa f k v r);
  });
rbt_insa f k v (Branch R l x y r) =
  (case Compare.compare k x of {
    Comparator.Eqa -> Branch R l x (f k y v) r;
    Comparator.Lt -> Branch R (rbt_insa f k v l) x y r;
    Comparator.Gt -> Branch R l x y (rbt_insa f k v r);
  });

of_nat :: forall a. (Semiring_1 a) => Nat -> a;
of_nat n =
  (if equal_nat n zero_nat then zero
    else (case divmod_nat n (nat_of_integer (2 :: Integer)) of {
           (m, q) -> let {
                       ma = times (numeral (Bit0 One)) (of_nat m);
                     } in (if equal_nat q zero_nat then ma else plus ma one);
         }));

char_0x20 :: Char;
char_0x20 = Chr (32 :: Integer);

char_0x21 :: Char;
char_0x21 = Chr (33 :: Integer);

char_0x22 :: Char;
char_0x22 = Chr (34 :: Integer);

char_0x23 :: Char;
char_0x23 = Chr (35 :: Integer);

char_0x26 :: Char;
char_0x26 = Chr (38 :: Integer);

char_0x27 :: Char;
char_0x27 = Chr (39 :: Integer);

char_0x28 :: Char;
char_0x28 = Chr (40 :: Integer);

char_0x29 :: Char;
char_0x29 = Chr (41 :: Integer);

char_0x2A :: Char;
char_0x2A = Chr (42 :: Integer);

char_0x2B :: Char;
char_0x2B = Chr (43 :: Integer);

char_0x2C :: Char;
char_0x2C = Chr (44 :: Integer);

char_0x2D :: Char;
char_0x2D = Chr (45 :: Integer);

char_0x2F :: Char;
char_0x2F = Chr (47 :: Integer);

char_0x30 :: Char;
char_0x30 = Chr (48 :: Integer);

char_0x31 :: Char;
char_0x31 = Chr (49 :: Integer);

char_0x32 :: Char;
char_0x32 = Chr (50 :: Integer);

char_0x33 :: Char;
char_0x33 = Chr (51 :: Integer);

char_0x34 :: Char;
char_0x34 = Chr (52 :: Integer);

char_0x35 :: Char;
char_0x35 = Chr (53 :: Integer);

char_0x36 :: Char;
char_0x36 = Chr (54 :: Integer);

char_0x37 :: Char;
char_0x37 = Chr (55 :: Integer);

char_0x38 :: Char;
char_0x38 = Chr (56 :: Integer);

char_0x39 :: Char;
char_0x39 = Chr (57 :: Integer);

char_0x3A :: Char;
char_0x3A = Chr (58 :: Integer);

char_0x3B :: Char;
char_0x3B = Chr (59 :: Integer);

char_0x3C :: Char;
char_0x3C = Chr (60 :: Integer);

char_0x3D :: Char;
char_0x3D = Chr (61 :: Integer);

char_0x3E :: Char;
char_0x3E = Chr (62 :: Integer);

char_0x3F :: Char;
char_0x3F = Chr (63 :: Integer);

char_0x41 :: Char;
char_0x41 = Chr (65 :: Integer);

char_0x42 :: Char;
char_0x42 = Chr (66 :: Integer);

char_0x43 :: Char;
char_0x43 = Chr (67 :: Integer);

char_0x44 :: Char;
char_0x44 = Chr (68 :: Integer);

char_0x45 :: Char;
char_0x45 = Chr (69 :: Integer);

char_0x46 :: Char;
char_0x46 = Chr (70 :: Integer);

char_0x47 :: Char;
char_0x47 = Chr (71 :: Integer);

char_0x48 :: Char;
char_0x48 = Chr (72 :: Integer);

char_0x49 :: Char;
char_0x49 = Chr (73 :: Integer);

char_0x4A :: Char;
char_0x4A = Chr (74 :: Integer);

char_0x4B :: Char;
char_0x4B = Chr (75 :: Integer);

char_0x4C :: Char;
char_0x4C = Chr (76 :: Integer);

char_0x4D :: Char;
char_0x4D = Chr (77 :: Integer);

char_0x4E :: Char;
char_0x4E = Chr (78 :: Integer);

char_0x4F :: Char;
char_0x4F = Chr (79 :: Integer);

char_0x50 :: Char;
char_0x50 = Chr (80 :: Integer);

char_0x51 :: Char;
char_0x51 = Chr (81 :: Integer);

char_0x52 :: Char;
char_0x52 = Chr (82 :: Integer);

char_0x53 :: Char;
char_0x53 = Chr (83 :: Integer);

char_0x54 :: Char;
char_0x54 = Chr (84 :: Integer);

char_0x55 :: Char;
char_0x55 = Chr (85 :: Integer);

char_0x56 :: Char;
char_0x56 = Chr (86 :: Integer);

char_0x57 :: Char;
char_0x57 = Chr (87 :: Integer);

char_0x58 :: Char;
char_0x58 = Chr (88 :: Integer);

char_0x59 :: Char;
char_0x59 = Chr (89 :: Integer);

char_0x5A :: Char;
char_0x5A = Chr (90 :: Integer);

char_0x5B :: Char;
char_0x5B = Chr (91 :: Integer);

char_0x5D :: Char;
char_0x5D = Chr (93 :: Integer);

char_0x5F :: Char;
char_0x5F = Chr (95 :: Integer);

char_0x61 :: Char;
char_0x61 = Chr (97 :: Integer);

char_0x62 :: Char;
char_0x62 = Chr (98 :: Integer);

char_0x63 :: Char;
char_0x63 = Chr (99 :: Integer);

char_0x64 :: Char;
char_0x64 = Chr (100 :: Integer);

char_0x65 :: Char;
char_0x65 = Chr (101 :: Integer);

char_0x66 :: Char;
char_0x66 = Chr (102 :: Integer);

char_0x67 :: Char;
char_0x67 = Chr (103 :: Integer);

char_0x68 :: Char;
char_0x68 = Chr (104 :: Integer);

char_0x69 :: Char;
char_0x69 = Chr (105 :: Integer);

char_0x6A :: Char;
char_0x6A = Chr (106 :: Integer);

char_0x6B :: Char;
char_0x6B = Chr (107 :: Integer);

char_0x6C :: Char;
char_0x6C = Chr (108 :: Integer);

char_0x6D :: Char;
char_0x6D = Chr (109 :: Integer);

char_0x6E :: Char;
char_0x6E = Chr (110 :: Integer);

char_0x6F :: Char;
char_0x6F = Chr (111 :: Integer);

char_0x70 :: Char;
char_0x70 = Chr (112 :: Integer);

char_0x71 :: Char;
char_0x71 = Chr (113 :: Integer);

char_0x72 :: Char;
char_0x72 = Chr (114 :: Integer);

char_0x73 :: Char;
char_0x73 = Chr (115 :: Integer);

char_0x74 :: Char;
char_0x74 = Chr (116 :: Integer);

char_0x75 :: Char;
char_0x75 = Chr (117 :: Integer);

char_0x76 :: Char;
char_0x76 = Chr (118 :: Integer);

char_0x77 :: Char;
char_0x77 = Chr (119 :: Integer);

char_0x78 :: Char;
char_0x78 = Chr (120 :: Integer);

char_0x79 :: Char;
char_0x79 = Chr (121 :: Integer);

char_0x7A :: Char;
char_0x7A = Chr (122 :: Integer);

interval :: forall a. (Eq a, Interval a) => a -> a -> [a];
interval a b =
  (if Quasi_Order.less a b then a : interval (plus a one) b
    else (if a == b then [a] else []));

sort_key :: forall a b. (Quasi_Order.Linorder b) => (a -> b) -> [a] -> [a];
sort_key key = Efficient_Sort.msort_key key;

rbt_split ::
  forall a b.
    (Compare.Compare_order a) => Rbt a b -> a -> (Rbt a b, (Maybe b, Rbt a b));
rbt_split Empty k = (Empty, (Nothing, Empty));
rbt_split (Branch uu l a b r) x =
  (case Compare.compare x a of {
    Comparator.Eqa -> (l, (Just b, r));
    Comparator.Lt -> (case rbt_split l x of {
                       (l1, (beta, l2)) -> (l1, (beta, rbt_join l2 a b r));
                     });
    Comparator.Gt -> (case rbt_split r x of {
                       (r1, (beta, r2)) -> (rbt_join l a b r1, (beta, r2));
                     });
  });

rbt_insert_with_keya ::
  forall a b.
    (Compare.Compare_order a) => (a -> b -> b -> b) ->
                                   a -> b -> Rbt a b -> Rbt a b;
rbt_insert_with_keya f k v t = paint B (rbt_insa f k v t);

rbt_union_swap_rec ::
  forall a b.
    (Compare.Compare_order a) => (a -> b -> b -> b) ->
                                   Bool -> Rbt a b -> Rbt a b -> Rbt a b;
rbt_union_swap_rec f gamma t1 t2 =
  (case (if flip_rbt t2 t1 then (not gamma, (t1, t2)) else (gamma, (t2, t1))) of
    {
    (gammaa, (t2a, t1a)) ->
      let {
        fa = (if gammaa then (\ k v va -> f k va v) else f);
      } in (if small_rbt t2a then folda (rbt_insert_with_keya fa) t2a t1a
             else (case t1a of {
                    Empty -> t2a;
                    Branch _ l1 a b r1 ->
                      (case rbt_split t2a a of {
                        (l2, (beta, r2)) ->
                          rbt_join (rbt_union_swap_rec f gammaa l1 l2) a
                            (case beta of {
                              Nothing -> b;
                              Just c -> fa a b c;
                            })
                            (rbt_union_swap_rec f gammaa r1 r2);
                      });
                  }));
  });

rbt_union_with_key ::
  forall a b.
    (Compare.Compare_order a) => (a -> b -> b -> b) ->
                                   Rbt a b -> Rbt a b -> Rbt a b;
rbt_union_with_key f t1 t2 = paint B (rbt_union_swap_rec f False t1 t2);

rbt_union ::
  forall a b. (Compare.Compare_order a) => Rbt a b -> Rbt a b -> Rbt a b;
rbt_union = rbt_union_with_key (\ _ _ rv -> rv);

minus_set :: forall a. (Ceq a, Ccompare a) => Set a -> Set a -> Set a;
minus_set (RBT_set rbt1) (RBT_set rbt2) =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "minus RBT_set RBT_set: ccompare = None"
        (\ _ -> minus_set (RBT_set rbt1) (RBT_set rbt2));
    Just _ -> RBT_set (minus rbt1 rbt2);
  });
minus_set a b = inf_set a (uminus_set b);

rbt_delete :: forall a b. (Compare.Compare_order a) => a -> Rbt a b -> Rbt a b;
rbt_delete k t = paint B (rbt_del k t);

rbt_inserta ::
  forall a b. (Compare.Compare_order a) => a -> b -> Rbt a b -> Rbt a b;
rbt_inserta = rbt_insert_with_keya (\ _ _ nv -> nv);

rbt_lookupa :: forall a b. (Compare.Compare_order a) => Rbt a b -> a -> Maybe b;
rbt_lookupa Empty k = Nothing;
rbt_lookupa (Branch uu l x y r) k = (case Compare.compare k x of {
                                      Comparator.Eqa -> Just y;
                                      Comparator.Lt -> rbt_lookupa l k;
                                      Comparator.Gt -> rbt_lookupa r k;
                                    });

rbt_bulkload :: forall a b. (Compare.Compare_order a) => [(a, b)] -> Rbt a b;
rbt_bulkload xs = foldr (\ (a, b) -> rbt_inserta a b) xs Empty;

all_interval :: forall a. (Eq a, Interval a) => (a -> Bool) -> a -> a -> Bool;
all_interval p a b =
  (if Quasi_Order.less a b then p a && all_interval p (plus a one) b
    else True) &&
    (if a == b then p a else True);

sorted_list_of_set ::
  forall a. (Ceq a, Ccompare a, Eq a, Quasi_Order.Linorder a) => Set a -> [a];
sorted_list_of_set (RBT_set rbt) =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "sorted_list_of_set RBT_set: ccompare = None"
        (\ _ -> sorted_list_of_set (RBT_set rbt));
    Just _ -> sort_key (\ x -> x) (keysa rbt);
  });
sorted_list_of_set (DList_set dxs) =
  (case (ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "sorted_list_of_set DList_set: ceq = None"
        (\ _ -> sorted_list_of_set (DList_set dxs));
    Just _ -> sort_key (\ x -> x) (list_of_dlist dxs);
  });
sorted_list_of_set (Set_Monad xs) = sort_key (\ x -> x) (remdups xs);

divide_int :: Int -> Int -> Int;
divide_int k l =
  Int_of_integer (divide_integer (integer_of_int k) (integer_of_int l));

}
