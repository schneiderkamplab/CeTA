{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Real(Mini_alg, Mini_alg_unique, Real(..), equal_real, times_real, uminus_real,
        zero_real, plus_real, minus_real, ratreal, less_real, abs_real,
        one_real, sgn_real, divide_real, less_eq_real, mau_sqrt, mau_coeff,
        mau_show_real)
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
import qualified Show_Instances;
import qualified Showa;
import qualified Prime_Product;
import qualified Sqrt_Babylonian;
import qualified HOL;
import qualified Rat;
import qualified Archimedean_Field;
import qualified SN_Orders;
import qualified Quasi_Order;
import qualified Arith;

newtype Mini_alg = Abs_mini_alg (Rat.Rat, (Rat.Rat, Arith.Nat));

newtype Mini_alg_unique = Abs_mini_alg_unique Mini_alg;

newtype Real = Real_of_u Mini_alg_unique;

rep_mini_alg_unique :: Mini_alg_unique -> Mini_alg;
rep_mini_alg_unique (Abs_mini_alg_unique x) = x;

rep_mini_alg :: Mini_alg -> (Rat.Rat, (Rat.Rat, Arith.Nat));
rep_mini_alg (Abs_mini_alg x) = x;

ma_identity :: Mini_alg -> Mini_alg -> Bool;
ma_identity xa xc = rep_mini_alg xa == rep_mini_alg xc;

mau_equal :: Mini_alg_unique -> Mini_alg_unique -> Bool;
mau_equal xa xc = ma_identity (rep_mini_alg_unique xa) (rep_mini_alg_unique xc);

equal_real :: Real -> Real -> Bool;
equal_real (Real_of_u r1) (Real_of_u r2) = mau_equal r1 r2;

instance Eq Real where {
  a == b = equal_real a b;
};

ma_compatible :: Mini_alg -> Mini_alg -> Bool;
ma_compatible xa xc =
  (case rep_mini_alg xa of {
    (_, (q1, b1)) ->
      (\ (_, (q2, b2)) ->
        Rat.equal_rat q1 Rat.zero_rat ||
          (Rat.equal_rat q2 Rat.zero_rat || Arith.equal_nat b1 b2));
  })
    (rep_mini_alg xc);

mau_compatible :: Mini_alg_unique -> Mini_alg_unique -> Bool;
mau_compatible xa xc =
  ma_compatible (rep_mini_alg_unique xa) (rep_mini_alg_unique xc);

ma_normalize ::
  (Rat.Rat, (Rat.Rat, Arith.Nat)) -> (Rat.Rat, (Rat.Rat, Arith.Nat));
ma_normalize x =
  (case x of {
    (a, (b, c)) ->
      (if Rat.equal_rat b Rat.zero_rat then (a, (Rat.zero_rat, Arith.zero_nat))
        else (a, (b, c)));
  });

ma_times :: Mini_alg -> Mini_alg -> Mini_alg;
ma_times xb xc =
  Abs_mini_alg
    ((case rep_mini_alg xb of {
       (p1, (q1, b1)) ->
         (\ (p2, (q2, b2)) ->
           (if Rat.equal_rat q1 Rat.zero_rat
             then ma_normalize (Rat.times_rat p1 p2, (Rat.times_rat p1 q2, b2))
             else ma_normalize
                    (Rat.plus_rat (Rat.times_rat p1 p2)
                       (Rat.times_rat (Rat.times_rat (Arith.of_nat b2) q1) q2),
                      (Rat.plus_rat (Rat.times_rat p1 q2) (Rat.times_rat q1 p2),
                        b1))));
     })
      (rep_mini_alg xc));

mau_times :: Mini_alg_unique -> Mini_alg_unique -> Mini_alg_unique;
mau_times xb xc =
  Abs_mini_alg_unique
    (ma_times (rep_mini_alg_unique xb) (rep_mini_alg_unique xc));

times_real :: Real -> Real -> Real;
times_real (Real_of_u r1) (Real_of_u r2) =
  (if mau_compatible r1 r2 then Real_of_u (mau_times r1 r2)
    else (error :: forall a. String -> (() -> a) -> a) "different base"
           (\ _ -> times_real (Real_of_u r1) (Real_of_u r2)));

instance Arith.Times Real where {
  times = times_real;
};

instance Arith.Dvd Real where {
};

ma_uminus :: Mini_alg -> Mini_alg;
ma_uminus xa =
  Abs_mini_alg
    (case rep_mini_alg xa of {
      (p1, (q1, b1)) -> (Rat.uminus_rat p1, (Rat.uminus_rat q1, b1));
    });

mau_uminus :: Mini_alg_unique -> Mini_alg_unique;
mau_uminus xa = Abs_mini_alg_unique (ma_uminus (rep_mini_alg_unique xa));

uminus_real :: Real -> Real;
uminus_real (Real_of_u r) = Real_of_u (mau_uminus r);

ma_of_rat :: Rat.Rat -> Mini_alg;
ma_of_rat xa = Abs_mini_alg (xa, (Rat.zero_rat, Arith.zero_nat));

mau_of_rat :: Rat.Rat -> Mini_alg_unique;
mau_of_rat xa = Abs_mini_alg_unique (ma_of_rat xa);

zero_real :: Real;
zero_real = Real_of_u (mau_of_rat Rat.zero_rat);

ma_plus :: Mini_alg -> Mini_alg -> Mini_alg;
ma_plus xb xc =
  Abs_mini_alg
    ((case rep_mini_alg xb of {
       (p1, (q1, b1)) ->
         (\ (p2, (q2, b2)) ->
           (if Rat.equal_rat q1 Rat.zero_rat then (Rat.plus_rat p1 p2, (q2, b2))
             else ma_normalize (Rat.plus_rat p1 p2, (Rat.plus_rat q1 q2, b1))));
     })
      (rep_mini_alg xc));

mau_plus :: Mini_alg_unique -> Mini_alg_unique -> Mini_alg_unique;
mau_plus xb xc =
  Abs_mini_alg_unique
    (ma_plus (rep_mini_alg_unique xb) (rep_mini_alg_unique xc));

plus_real :: Real -> Real -> Real;
plus_real (Real_of_u r1) (Real_of_u r2) =
  (if mau_compatible r1 r2 then Real_of_u (mau_plus r1 r2)
    else (error :: forall a. String -> (() -> a) -> a) "different base"
           (\ _ -> plus_real (Real_of_u r1) (Real_of_u r2)));

minus_real :: Real -> Real -> Real;
minus_real x y = plus_real x (uminus_real y);

ma_floor :: Mini_alg -> Arith.Int;
ma_floor xa =
  (case rep_mini_alg xa of {
    (p, (q, b)) ->
      (case (Rat.quotient_of p, Rat.quotient_of q) of {
        ((z1, n1), (z2, n2)) ->
          let {
            z2n1 = Arith.times_int z2 n1;
            z1n2 = Arith.times_int z1 n2;
            n12 = Arith.times_int n1 n2;
            prod =
              Arith.times_int (Arith.times_int z2n1 z2n1) (Arith.int_of_nat b);
          } in Arith.divide_int
                 (Arith.plus_int z1n2
                   (if Arith.less_eq_int Arith.zero_int z2n1
                     then Sqrt_Babylonian.sqrt_int_floor_pos prod
                     else Arith.uminus_int
                            (Sqrt_Babylonian.sqrt_int_ceiling_pos prod)))
                 n12;
      });
  });

mau_floor :: Mini_alg_unique -> Arith.Int;
mau_floor xa = ma_floor (rep_mini_alg_unique xa);

floor_real :: Real -> Arith.Int;
floor_real (Real_of_u r) = mau_floor r;

ratreal :: Rat.Rat -> Real;
ratreal = Real_of_u . mau_of_rat;

real_lt :: Real -> Real -> Bool;
real_lt x y =
  let {
    fx = floor_real x;
    fy = floor_real y;
  } in (if Arith.less_int fx fy then True
         else (if Arith.less_int fy fx then False
                else real_lt
                       (times_real x
                         (ratreal
                           (Rat.of_int
                             (Arith.Int_of_integer (1024 :: Integer)))))
                       (times_real y
                         (ratreal
                           (Rat.of_int
                             (Arith.Int_of_integer (1024 :: Integer)))))));

ma_ge_0 :: Mini_alg -> Bool;
ma_ge_0 xa =
  (case rep_mini_alg xa of {
    (p, (q, b)) ->
      let {
        bqq = Rat.times_rat (Rat.times_rat (Arith.of_nat b) q) q;
        pp = Rat.times_rat p p;
      } in Rat.less_eq_rat Rat.zero_rat p && Rat.less_eq_rat bqq pp ||
             Rat.less_eq_rat Rat.zero_rat q && Rat.less_eq_rat pp bqq;
  });

mau_ge_0 :: Mini_alg_unique -> Bool;
mau_ge_0 xa = ma_ge_0 (rep_mini_alg_unique xa);

ge_0 :: Real -> Bool;
ge_0 (Real_of_u x) = mau_ge_0 x;

less_real :: Real -> Real -> Bool;
less_real (Real_of_u x) (Real_of_u y) =
  not (equal_real (Real_of_u x) (Real_of_u y)) &&
    (if mau_compatible x y then ge_0 (minus_real (Real_of_u y) (Real_of_u x))
      else real_lt (Real_of_u x) (Real_of_u y));

abs_real :: Real -> Real;
abs_real a = (if less_real a zero_real then uminus_real a else a);

instance Arith.Abs Real where {
  absa = abs_real;
};

one_real :: Real;
one_real = Real_of_u (mau_of_rat Rat.one_rat);

instance Arith.One Real where {
  one = one_real;
};

sgn_real :: Real -> Real;
sgn_real a =
  (if equal_real a zero_real then zero_real
    else (if less_real zero_real a then one_real else uminus_real one_real));

instance Arith.Sgn Real where {
  sgn = sgn_real;
};

instance Arith.Plus Real where {
  plus = plus_real;
};

instance Arith.Semigroup_add Real where {
};

instance Arith.Cancel_semigroup_add Real where {
};

instance Arith.Ab_semigroup_add Real where {
};

instance Arith.Minus Real where {
  minusa = minus_real;
};

instance Arith.Cancel_ab_semigroup_add Real where {
};

instance Arith.Zero Real where {
  zero = zero_real;
};

instance Arith.Monoid_add Real where {
};

instance Arith.Comm_monoid_add Real where {
};

instance Arith.Cancel_comm_monoid_add Real where {
};

instance Arith.Mult_zero Real where {
};

instance Arith.Semigroup_mult Real where {
};

instance Arith.Semiring Real where {
};

instance Arith.Semiring_0 Real where {
};

instance Arith.Semiring_0_cancel Real where {
};

instance Arith.Ab_semigroup_mult Real where {
};

instance Arith.Comm_semiring Real where {
};

instance Arith.Comm_semiring_0 Real where {
};

instance Arith.Comm_semiring_0_cancel Real where {
};

instance Arith.Power Real where {
};

instance Arith.Monoid_mult Real where {
};

instance Arith.Numeral Real where {
};

instance Arith.Semiring_numeral Real where {
};

instance Arith.Zero_neq_one Real where {
};

instance Arith.Semiring_1 Real where {
};

instance Arith.Semiring_1_cancel Real where {
};

instance Arith.Comm_monoid_mult Real where {
};

instance Arith.Comm_semiring_1 Real where {
};

instance Arith.Comm_semiring_1_cancel Real where {
};

instance Arith.Comm_semiring_1_cancel_crossproduct Real where {
};

instance Arith.Semiring_no_zero_divisors Real where {
};

instance Arith.Semiring_1_no_zero_divisors Real where {
};

instance Arith.Semiring_no_zero_divisors_cancel Real where {
};

instance Arith.Uminus Real where {
  uminus = uminus_real;
};

instance Arith.Group_add Real where {
};

instance Arith.Ab_group_add Real where {
};

instance Arith.Ring Real where {
};

instance Arith.Ring_no_zero_divisors Real where {
};

instance Arith.Neg_numeral Real where {
};

instance Arith.Ring_1 Real where {
};

instance Arith.Ring_1_no_zero_divisors Real where {
};

instance Arith.Comm_ring Real where {
};

instance Arith.Comm_ring_1 Real where {
};

instance Arith.Semidom Real where {
};

instance Arith.Idom Real where {
};

ma_inverse :: Mini_alg -> Mini_alg;
ma_inverse xa =
  Abs_mini_alg
    (case rep_mini_alg xa of {
      (p, (q, b)) ->
        let {
          d = Rat.inverse_rat
                (Rat.minus_rat (Rat.times_rat p p)
                  (Rat.times_rat (Rat.times_rat (Arith.of_nat b) q) q));
        } in ma_normalize
               (Rat.times_rat p d, (Rat.times_rat (Rat.uminus_rat q) d, b));
    });

mau_inverse :: Mini_alg_unique -> Mini_alg_unique;
mau_inverse xa = Abs_mini_alg_unique (ma_inverse (rep_mini_alg_unique xa));

inverse_real :: Real -> Real;
inverse_real (Real_of_u r) = Real_of_u (mau_inverse r);

divide_real :: Real -> Real -> Real;
divide_real x y = times_real x (inverse_real y);

instance Arith.Ufd Real where {
};

instance Arith.Divide Real where {
  divide = divide_real;
};

instance Arith.Divide_trivial Real where {
};

instance Arith.Inverse Real where {
  inverse = inverse_real;
};

instance Arith.Division_ring Real where {
};

instance Arith.Semidom_divide Real where {
};

instance Arith.Idom_divide Real where {
};

instance Arith.Field Real where {
};

less_eq_real :: Real -> Real -> Bool;
less_eq_real (Real_of_u x) (Real_of_u y) =
  equal_real (Real_of_u x) (Real_of_u y) ||
    (if mau_compatible x y then ge_0 (minus_real (Real_of_u y) (Real_of_u x))
      else real_lt (Real_of_u x) (Real_of_u y));

instance Quasi_Order.Ord Real where {
  less_eq = less_eq_real;
  less = less_real;
};

instance Arith.Abs_if Real where {
};

instance Arith.Semiring_char_0 Real where {
};

instance Arith.Ring_char_0 Real where {
};

instance Quasi_Order.Quasi_order Real where {
};

instance Quasi_Order.Weak_order Real where {
};

instance Quasi_Order.Preorder Real where {
};

instance Quasi_Order.Order Real where {
};

instance Quasi_Order.No_bot Real where {
};

instance Quasi_Order.No_top Real where {
};

instance Quasi_Order.Linorder Real where {
};

instance Arith.Idom_abs_sgn Real where {
};

instance Arith.Ordered_ab_semigroup_add Real where {
};

instance Arith.Strict_ordered_ab_semigroup_add Real where {
};

instance Arith.Ordered_cancel_ab_semigroup_add Real where {
};

instance Arith.Ordered_semigroup_mult_zero Real where {
};

instance Arith.Ordered_comm_monoid_add Real where {
};

instance Arith.Ordered_semiring Real where {
};

instance Arith.Ordered_semiring_0 Real where {
};

instance Arith.Ordered_cancel_semiring Real where {
};

instance Arith.Ordered_ab_semigroup_add_imp_le Real where {
};

instance Arith.Strict_ordered_comm_monoid_add Real where {
};

instance Arith.Ordered_cancel_comm_monoid_add Real where {
};

instance Arith.Ordered_ab_semigroup_monoid_add_imp_le Real where {
};

instance Arith.Ordered_ab_group_add Real where {
};

instance Arith.Ordered_ring Real where {
};

instance Arith.Field_char_0 Real where {
};

instance Arith.Zero_less_one Real where {
};

instance Arith.Field_abs_sgn Real where {
};

instance Quasi_Order.Dense_order Real where {
};

instance Arith.Ordered_semiring_strict Real where {
};

instance Arith.Linordered_ab_semigroup_add Real where {
};

instance Arith.Linordered_cancel_ab_semigroup_add Real where {
};

instance Arith.Linordered_semiring Real where {
};

instance Arith.Linordered_semiring_strict Real where {
};

instance Arith.Ordered_semiring_1 Real where {
};

instance Arith.Ordered_semiring_1_strict Real where {
};

instance Arith.Ordered_semiring_1a Real where {
};

instance Arith.Linordered_semiring_1 Real where {
};

instance Arith.Linordered_semiring_1_strict Real where {
};

instance Arith.Ordered_ab_group_add_abs Real where {
};

instance Arith.Linordered_ab_group_add Real where {
};

instance Arith.Linordered_ring Real where {
};

instance Arith.Linordered_ring_strict Real where {
};

instance Arith.Semiring_real_line Real where {
};

instance Arith.Semiring_1_real_line Real where {
};

instance Arith.Ordered_comm_semiring Real where {
};

instance Arith.Ordered_cancel_comm_semiring Real where {
};

instance Arith.Ordered_comm_semiring_strict Real where {
};

instance Arith.Linordered_comm_semiring_strict Real where {
};

instance Arith.Linordered_nonzero_semiring Real where {
};

instance Arith.Linordered_semidom Real where {
};

instance Arith.Ordered_comm_ring Real where {
};

instance Arith.Ordered_ring_abs Real where {
};

instance Arith.Linordered_idom Real where {
};

instance SN_Orders.Non_strict_order Real where {
};

instance SN_Orders.Ordered_ab_semigroup Real where {
};

instance SN_Orders.Ordered_semiring_0 Real where {
};

instance SN_Orders.Ordered_semiring_1 Real where {
};

instance SN_Orders.Poly_carrier Real where {
};

instance Quasi_Order.Unbounded_dense_order Real where {
};

instance Quasi_Order.Dense_linorder Real where {
};

instance Quasi_Order.Unbounded_dense_linorder Real where {
};

instance Arith.Linordered_field Real where {
};

instance Archimedean_Field.Archimedean_field Real where {
};

instance SN_Orders.Large_ordered_semiring_1 Real where {
};

instance Archimedean_Field.Floor_ceiling Real where {
  floor = floor_real;
};

ma_rat :: Mini_alg -> Rat.Rat;
ma_rat xa = fst (rep_mini_alg xa);

ma_sqrt :: Mini_alg -> Mini_alg;
ma_sqrt xa =
  Abs_mini_alg
    (case rep_mini_alg xa of {
      (p, (_, _)) ->
        (case Rat.quotient_of p of {
          (a, b) ->
            let {
              aa = Arith.abs_int (Arith.times_int a b);
            } in (case Sqrt_Babylonian.sqrt_int aa of {
                   [] -> (Rat.zero_rat,
                           (Rat.inverse_rat (Rat.of_int b), Arith.nat aa));
                   s : _ ->
                     (Rat.divide_rat (Rat.of_int s) (Rat.of_int b),
                       (Rat.zero_rat, Arith.zero_nat));
                 });
        });
    });

ma_coeff :: Mini_alg -> Rat.Rat;
ma_coeff xa = fst (snd (rep_mini_alg xa));

mau_sqrt :: Mini_alg_unique -> Mini_alg_unique;
mau_sqrt xa =
  Abs_mini_alg_unique
    (case Rat.quotient_of (ma_rat (rep_mini_alg_unique xa)) of {
      (a, b) ->
        (case Prime_Product.prime_product_factor
                (Arith.nat (Arith.times_int (Arith.abs_int a) b))
          of {
          (sq, fact) ->
            let {
              ma = ma_of_rat
                     (Rat.divide_rat
                       (Rat.times_rat (Rat.of_int (Arith.sgn_int a))
                         (Arith.of_nat sq))
                       (Rat.of_int b));
            } in ma_times ma (ma_sqrt (ma_of_rat (Arith.of_nat fact)));
        });
    });

mau_coeff :: Mini_alg_unique -> Rat.Rat;
mau_coeff xa = ma_coeff (rep_mini_alg_unique xa);

ma_show_real :: Mini_alg -> [Arith.Char];
ma_show_real xa =
  (case rep_mini_alg xa of {
    (p, (q, b)) ->
      let {
        sb = (Showa.shows_prec_list Arith.zero_nat
                [Arith.char_0x73, Arith.char_0x71, Arith.char_0x72,
                  Arith.char_0x74, Arith.char_0x28] .
               Show_Instances.shows_prec_nat Arith.zero_nat b) .
               Showa.shows_prec_list Arith.zero_nat [Arith.char_0x29];
        qb = (if Rat.equal_rat q Rat.one_rat then sb
               else (if Rat.equal_rat q (Rat.uminus_rat Rat.one_rat)
                      then Showa.shows_prec_list Arith.zero_nat
                             [Arith.char_0x2D] .
                             sb
                      else (Show_Instances.shows_prec_rat Arith.zero_nat q .
                             Showa.shows_prec_list Arith.zero_nat
                               [Arith.char_0x2A]) .
                             sb));
      } in (if Rat.equal_rat q Rat.zero_rat
             then Show_Instances.shows_prec_rat Arith.zero_nat p []
             else (if Rat.equal_rat p Rat.zero_rat then qb []
                    else (if Rat.less_rat q Rat.zero_rat
                           then Show_Instances.shows_prec_rat Arith.zero_nat p
                                  (qb [])
                           else Show_Instances.shows_prec_rat Arith.zero_nat p
                                  (Showa.shows_prec_list Arith.zero_nat
                                    [Arith.char_0x2B] (qb [])))));
  });

mau_show_real :: Mini_alg_unique -> [Arith.Char];
mau_show_real xa = ma_show_real (rep_mini_alg_unique xa);

}
