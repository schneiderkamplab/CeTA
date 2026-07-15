{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Field_as_Ring() where {

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
import qualified Euclidean_Algorithm;
import qualified Factorial_Ring;
import qualified Unique_Factorization;
import qualified Arith;
import qualified Real;
import qualified Set;
import qualified GCD;

euclidean_size_field :: forall a. (Arith.Field a, Eq a) => a -> Arith.Nat;
euclidean_size_field x =
  (if x == Arith.zero then Arith.zero_nat else Arith.one_nat);

euclidean_size_real :: Real.Real -> Arith.Nat;
euclidean_size_real = euclidean_size_field;

normalize_field :: forall a. (Arith.Field a, Eq a) => a -> a;
normalize_field x = (if x == Arith.zero then Arith.zero else Arith.one);

normalize_real :: Real.Real -> Real.Real;
normalize_real = normalize_field;

unit_factor_field :: forall a. (Arith.Field a) => a -> a;
unit_factor_field x = x;

unit_factor_real :: Real.Real -> Real.Real;
unit_factor_real = unit_factor_field;

mod_field :: forall a. (Arith.Field a, Eq a) => a -> a -> a;
mod_field x y = (if y == Arith.zero then x else Arith.zero);

modulo_real :: Real.Real -> Real.Real -> Real.Real;
modulo_real = mod_field;

instance Arith.Modulo Real.Real where {
  modulo = modulo_real;
};

instance Arith.Semiring_modulo Real.Real where {
};

instance Arith.Semiring_modulo_trivial Real.Real where {
};

instance Arith.Algebraic_semidom Real.Real where {
};

instance Arith.Semidom_modulo Real.Real where {
};

instance Arith.Euclidean_semiring Real.Real where {
  euclidean_size = euclidean_size_real;
};

instance Arith.Unit_factor Real.Real where {
  unit_factor = unit_factor_real;
};

instance Arith.Semidom_divide_unit_factor Real.Real where {
};

instance Arith.Normalization_semidom Real.Real where {
  normalize = normalize_real;
};

instance Factorial_Ring.Factorial_semiring Real.Real where {
};

instance Euclidean_Algorithm.Normalization_euclidean_semiring Real.Real where {
};

lcm_reala :: Real.Real -> Real.Real -> Real.Real;
lcm_reala = Euclidean_Algorithm.lcma;

gcd_reala :: Real.Real -> Real.Real -> Real.Real;
gcd_reala = Euclidean_Algorithm.gcda;

lcm_real :: Set.Set Real.Real -> Real.Real;
lcm_real = Euclidean_Algorithm.lcm;

gcd_real :: Set.Set Real.Real -> Real.Real;
gcd_real = Euclidean_Algorithm.gcd;

instance GCD.Gcda Real.Real where {
  gcda = gcd_reala;
  lcma = lcm_reala;
};

instance GCD.Gcd Real.Real where {
  gcd = gcd_real;
  lcm = lcm_real;
};

instance Unique_Factorization.Comm_monoid_gcd Real.Real where {
};

instance Unique_Factorization.Idom_gcd Real.Real where {
};

instance GCD.Semiring_gcd Real.Real where {
};

instance GCD.Ring_gcd Real.Real where {
};

instance GCD.Semiring_Gcd Real.Real where {
};

instance Arith.Normalization_semidom_multiplicative Real.Real where {
};

instance GCD.Semiring_gcd_mult_normalize Real.Real where {
};

instance Factorial_Ring.Factorial_semiring_gcd Real.Real where {
};

instance Factorial_Ring.Factorial_ring_gcd Real.Real where {
};

}
