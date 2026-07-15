{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Rat(Rat, quotient_of, equal_rat, times_rat, abs_rat, one_rat, sgn_rat,
       uminus_rat, minus_rat, zero_rat, plus_rat, inverse_rat, divide_rat,
       less_eq_rat, less_rat, floor_rat, of_int)
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
import qualified HOL;
import qualified Archimedean_Field;
import qualified SN_Orders;
import qualified Quasi_Order;
import qualified Arith;

newtype Rat = Frct (Arith.Int, Arith.Int);

quotient_of :: Rat -> (Arith.Int, Arith.Int);
quotient_of (Frct x) = x;

equal_rat :: Rat -> Rat -> Bool;
equal_rat a b = quotient_of a == quotient_of b;

instance Eq Rat where {
  a == b = equal_rat a b;
};

normalize :: (Arith.Int, Arith.Int) -> (Arith.Int, Arith.Int);
normalize p =
  (if Arith.less_int Arith.zero_int (snd p)
    then let {
           a = Arith.gcd_int (fst p) (snd p);
         } in (Arith.divide_int (fst p) a, Arith.divide_int (snd p) a)
    else (if Arith.equal_int (snd p) Arith.zero_int
           then (Arith.zero_int, Arith.one_int)
           else let {
                  a = Arith.uminus_int (Arith.gcd_int (fst p) (snd p));
                } in (Arith.divide_int (fst p) a, Arith.divide_int (snd p) a)));

times_rat :: Rat -> Rat -> Rat;
times_rat p q =
  Frct (case quotient_of p of {
         (a, c) ->
           (case quotient_of q of {
             (b, d) -> normalize (Arith.times_int a b, Arith.times_int c d);
           });
       });

instance Arith.Times Rat where {
  times = times_rat;
};

instance Arith.Dvd Rat where {
};

abs_rat :: Rat -> Rat;
abs_rat p = Frct (case quotient_of p of {
                   (a, b) -> (Arith.abs_int a, b);
                 });

instance Arith.Abs Rat where {
  absa = abs_rat;
};

one_rat :: Rat;
one_rat = Frct (Arith.one_int, Arith.one_int);

instance Arith.One Rat where {
  one = one_rat;
};

sgn_rat :: Rat -> Rat;
sgn_rat p = Frct (Arith.sgn_int (fst (quotient_of p)), Arith.one_int);

instance Arith.Sgn Rat where {
  sgn = sgn_rat;
};

uminus_rat :: Rat -> Rat;
uminus_rat p = Frct (case quotient_of p of {
                      (a, b) -> (Arith.uminus_int a, b);
                    });

minus_rat :: Rat -> Rat -> Rat;
minus_rat p q =
  Frct (case quotient_of p of {
         (a, c) ->
           (case quotient_of q of {
             (b, d) ->
               normalize
                 (Arith.minus_int (Arith.times_int a d) (Arith.times_int b c),
                   Arith.times_int c d);
           });
       });

zero_rat :: Rat;
zero_rat = Frct (Arith.zero_int, Arith.one_int);

plus_rat :: Rat -> Rat -> Rat;
plus_rat p q =
  Frct (case quotient_of p of {
         (a, c) ->
           (case quotient_of q of {
             (b, d) ->
               normalize
                 (Arith.plus_int (Arith.times_int a d) (Arith.times_int b c),
                   Arith.times_int c d);
           });
       });

instance Arith.Plus Rat where {
  plus = plus_rat;
};

instance Arith.Semigroup_add Rat where {
};

instance Arith.Cancel_semigroup_add Rat where {
};

instance Arith.Ab_semigroup_add Rat where {
};

instance Arith.Minus Rat where {
  minusa = minus_rat;
};

instance Arith.Cancel_ab_semigroup_add Rat where {
};

instance Arith.Zero Rat where {
  zero = zero_rat;
};

instance Arith.Monoid_add Rat where {
};

instance Arith.Comm_monoid_add Rat where {
};

instance Arith.Cancel_comm_monoid_add Rat where {
};

instance Arith.Mult_zero Rat where {
};

instance Arith.Semigroup_mult Rat where {
};

instance Arith.Semiring Rat where {
};

instance Arith.Semiring_0 Rat where {
};

instance Arith.Semiring_0_cancel Rat where {
};

instance Arith.Ab_semigroup_mult Rat where {
};

instance Arith.Comm_semiring Rat where {
};

instance Arith.Comm_semiring_0 Rat where {
};

instance Arith.Comm_semiring_0_cancel Rat where {
};

instance Arith.Power Rat where {
};

instance Arith.Monoid_mult Rat where {
};

instance Arith.Numeral Rat where {
};

instance Arith.Semiring_numeral Rat where {
};

instance Arith.Zero_neq_one Rat where {
};

instance Arith.Semiring_1 Rat where {
};

instance Arith.Semiring_1_cancel Rat where {
};

instance Arith.Comm_monoid_mult Rat where {
};

instance Arith.Comm_semiring_1 Rat where {
};

instance Arith.Comm_semiring_1_cancel Rat where {
};

instance Arith.Comm_semiring_1_cancel_crossproduct Rat where {
};

instance Arith.Semiring_no_zero_divisors Rat where {
};

instance Arith.Semiring_1_no_zero_divisors Rat where {
};

instance Arith.Semiring_no_zero_divisors_cancel Rat where {
};

instance Arith.Uminus Rat where {
  uminus = uminus_rat;
};

instance Arith.Group_add Rat where {
};

instance Arith.Ab_group_add Rat where {
};

instance Arith.Ring Rat where {
};

instance Arith.Ring_no_zero_divisors Rat where {
};

instance Arith.Neg_numeral Rat where {
};

instance Arith.Ring_1 Rat where {
};

instance Arith.Ring_1_no_zero_divisors Rat where {
};

instance Arith.Comm_ring Rat where {
};

instance Arith.Comm_ring_1 Rat where {
};

instance Arith.Semidom Rat where {
};

instance Arith.Idom Rat where {
};

inverse_rat :: Rat -> Rat;
inverse_rat p =
  Frct (case quotient_of p of {
         (a, b) ->
           (if Arith.equal_int a Arith.zero_int
             then (Arith.zero_int, Arith.one_int)
             else (Arith.times_int (Arith.sgn_int a) b, Arith.abs_int a));
       });

divide_rat :: Rat -> Rat -> Rat;
divide_rat p q =
  Frct (case quotient_of p of {
         (a, c) ->
           (case quotient_of q of {
             (b, d) -> normalize (Arith.times_int a d, Arith.times_int c b);
           });
       });

instance Arith.Ufd Rat where {
};

instance Arith.Divide Rat where {
  divide = divide_rat;
};

instance Arith.Divide_trivial Rat where {
};

instance Arith.Inverse Rat where {
  inverse = inverse_rat;
};

instance Arith.Division_ring Rat where {
};

instance Arith.Semidom_divide Rat where {
};

instance Arith.Idom_divide Rat where {
};

instance Arith.Field Rat where {
};

less_eq_rat :: Rat -> Rat -> Bool;
less_eq_rat p q =
  (case quotient_of p of {
    (a, c) ->
      (case quotient_of q of {
        (b, d) -> Arith.less_eq_int (Arith.times_int a d) (Arith.times_int c b);
      });
  });

less_rat :: Rat -> Rat -> Bool;
less_rat p q =
  (case quotient_of p of {
    (a, c) ->
      (case quotient_of q of {
        (b, d) -> Arith.less_int (Arith.times_int a d) (Arith.times_int c b);
      });
  });

instance Quasi_Order.Ord Rat where {
  less_eq = less_eq_rat;
  less = less_rat;
};

inf_rat :: Rat -> Rat -> Rat;
inf_rat = Quasi_Order.min;

instance Quasi_Order.Inf Rat where {
  inf = inf_rat;
};

sup_rat :: Rat -> Rat -> Rat;
sup_rat = Quasi_Order.max;

instance Quasi_Order.Sup Rat where {
  sup = sup_rat;
};

instance Arith.Abs_if Rat where {
};

instance Arith.Semiring_char_0 Rat where {
};

instance Arith.Ring_char_0 Rat where {
};

instance Quasi_Order.Quasi_order Rat where {
};

instance Quasi_Order.Weak_order Rat where {
};

instance Quasi_Order.Preorder Rat where {
};

instance Quasi_Order.Order Rat where {
};

instance Quasi_Order.Quasi_order_sup Rat where {
};

instance Quasi_Order.Quasi_semilattice_sup Rat where {
};

instance Quasi_Order.Semilattice_sup Rat where {
};

instance Quasi_Order.Semilattice_inf Rat where {
};

instance Quasi_Order.Lattice Rat where {
};

instance Quasi_Order.No_bot Rat where {
};

instance Quasi_Order.No_top Rat where {
};

instance Quasi_Order.Linorder Rat where {
};

instance Arith.Idom_abs_sgn Rat where {
};

instance Arith.Ordered_ab_semigroup_add Rat where {
};

instance Arith.Strict_ordered_ab_semigroup_add Rat where {
};

instance Arith.Ordered_cancel_ab_semigroup_add Rat where {
};

instance Arith.Ordered_semigroup_mult_zero Rat where {
};

instance Arith.Ordered_comm_monoid_add Rat where {
};

instance Arith.Ordered_semiring Rat where {
};

instance Arith.Ordered_semiring_0 Rat where {
};

instance Arith.Ordered_cancel_semiring Rat where {
};

instance Arith.Ordered_ab_semigroup_add_imp_le Rat where {
};

instance Arith.Strict_ordered_comm_monoid_add Rat where {
};

instance Arith.Ordered_cancel_comm_monoid_add Rat where {
};

instance Arith.Ordered_ab_semigroup_monoid_add_imp_le Rat where {
};

instance Arith.Ordered_ab_group_add Rat where {
};

instance Arith.Ordered_ring Rat where {
};

instance Arith.Field_char_0 Rat where {
};

instance Arith.Zero_less_one Rat where {
};

instance Arith.Field_abs_sgn Rat where {
};

instance Quasi_Order.Dense_order Rat where {
};

instance Arith.Ordered_semiring_strict Rat where {
};

instance Arith.Linordered_ab_semigroup_add Rat where {
};

instance Arith.Linordered_cancel_ab_semigroup_add Rat where {
};

instance Arith.Linordered_semiring Rat where {
};

instance Arith.Linordered_semiring_strict Rat where {
};

instance Arith.Ordered_semiring_1 Rat where {
};

instance Arith.Ordered_semiring_1_strict Rat where {
};

instance Arith.Ordered_semiring_1a Rat where {
};

instance Arith.Linordered_semiring_1 Rat where {
};

instance Arith.Linordered_semiring_1_strict Rat where {
};

instance Arith.Ordered_ab_group_add_abs Rat where {
};

instance Arith.Linordered_ab_group_add Rat where {
};

instance Arith.Linordered_ring Rat where {
};

instance Arith.Linordered_ring_strict Rat where {
};

instance Arith.Semiring_real_line Rat where {
};

instance Arith.Semiring_1_real_line Rat where {
};

instance Arith.Ordered_comm_semiring Rat where {
};

instance Arith.Ordered_cancel_comm_semiring Rat where {
};

instance Arith.Ordered_comm_semiring_strict Rat where {
};

instance Arith.Linordered_comm_semiring_strict Rat where {
};

instance Arith.Linordered_nonzero_semiring Rat where {
};

instance Arith.Linordered_semidom Rat where {
};

instance Arith.Ordered_comm_ring Rat where {
};

instance Arith.Ordered_ring_abs Rat where {
};

instance Arith.Linordered_idom Rat where {
};

instance SN_Orders.Non_strict_order Rat where {
};

instance SN_Orders.Ordered_ab_semigroup Rat where {
};

instance SN_Orders.Ordered_semiring_0 Rat where {
};

instance SN_Orders.Ordered_semiring_1 Rat where {
};

instance SN_Orders.Poly_carrier Rat where {
};

instance Quasi_Order.Unbounded_dense_order Rat where {
};

instance Quasi_Order.Dense_linorder Rat where {
};

instance Quasi_Order.Unbounded_dense_linorder Rat where {
};

instance Arith.Linordered_field Rat where {
};

floor_rat :: Rat -> Arith.Int;
floor_rat p = (case quotient_of p of {
                (a, b) -> Arith.divide_int a b;
              });

instance Archimedean_Field.Archimedean_field Rat where {
};

instance SN_Orders.Large_ordered_semiring_1 Rat where {
};

instance Archimedean_Field.Floor_ceiling Rat where {
  floor = floor_rat;
};

of_int :: Arith.Int -> Rat;
of_int a = Frct (a, Arith.one_int);

}
