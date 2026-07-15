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
import qualified Term_Rewriting;
import qualified Arith;

euclidean_size_field :: forall a. (Arith.Field a, Eq a) => a -> Arith.Nat;
euclidean_size_field x =
  (if x == Arith.zero then Arith.zero_nat else Arith.one_nat);

euclidean_size_real :: Term_Rewriting.Real -> Arith.Nat;
euclidean_size_real = euclidean_size_field;

normalize_field :: forall a. (Arith.Field a, Eq a) => a -> a;
normalize_field x = (if x == Arith.zero then Arith.zero else Arith.one);

normalize_real :: Term_Rewriting.Real -> Term_Rewriting.Real;
normalize_real = normalize_field;

unit_factor_field :: forall a. (Arith.Field a) => a -> a;
unit_factor_field x = x;

unit_factor_real :: Term_Rewriting.Real -> Term_Rewriting.Real;
unit_factor_real = unit_factor_field;

mod_field :: forall a. (Arith.Field a, Eq a) => a -> a -> a;
mod_field x y = (if y == Arith.zero then x else Arith.zero);

modulo_real ::
  Term_Rewriting.Real -> Term_Rewriting.Real -> Term_Rewriting.Real;
modulo_real = mod_field;

instance Arith.Modulo Term_Rewriting.Real where {
  modulo = modulo_real;
};

instance Arith.Semiring_modulo Term_Rewriting.Real where {
};

instance Arith.Semiring_modulo_trivial Term_Rewriting.Real where {
};

instance Arith.Algebraic_semidom Term_Rewriting.Real where {
};

instance Arith.Semidom_modulo Term_Rewriting.Real where {
};

instance Arith.Euclidean_semiring Term_Rewriting.Real where {
  euclidean_size = euclidean_size_real;
};

instance Arith.Unit_factor Term_Rewriting.Real where {
  unit_factor = unit_factor_real;
};

instance Arith.Semidom_divide_unit_factor Term_Rewriting.Real where {
};

instance Arith.Normalization_semidom Term_Rewriting.Real where {
  normalize = normalize_real;
};

instance Factorial_Ring.Factorial_semiring Term_Rewriting.Real where {
};

instance Euclidean_Algorithm.Normalization_euclidean_semiring Term_Rewriting.Real where {
};

lcm_reala :: Term_Rewriting.Real -> Term_Rewriting.Real -> Term_Rewriting.Real;
lcm_reala = Euclidean_Algorithm.lcma;

gcd_reala :: Term_Rewriting.Real -> Term_Rewriting.Real -> Term_Rewriting.Real;
gcd_reala = Euclidean_Algorithm.gcda;

lcm_real :: Arith.Set Term_Rewriting.Real -> Term_Rewriting.Real;
lcm_real = Euclidean_Algorithm.lcm;

gcd_real :: Arith.Set Term_Rewriting.Real -> Term_Rewriting.Real;
gcd_real = Euclidean_Algorithm.gcd;

instance Arith.Gcda Term_Rewriting.Real where {
  gcda = gcd_reala;
  lcma = lcm_reala;
};

instance Arith.Gcd Term_Rewriting.Real where {
  gcd = gcd_real;
  lcm = lcm_real;
};

instance Arith.Comm_monoid_gcd Term_Rewriting.Real where {
};

instance Arith.Idom_gcd Term_Rewriting.Real where {
};

instance Arith.Semiring_gcd Term_Rewriting.Real where {
};

instance Arith.Ring_gcd Term_Rewriting.Real where {
};

instance Arith.Semiring_Gcd Term_Rewriting.Real where {
};

instance Arith.Normalization_semidom_multiplicative Term_Rewriting.Real where {
};

instance Arith.Semiring_gcd_mult_normalize Term_Rewriting.Real where {
};

instance Factorial_Ring.Factorial_semiring_gcd Term_Rewriting.Real where {
};

instance Factorial_Ring.Factorial_ring_gcd Term_Rewriting.Real where {
};

}
