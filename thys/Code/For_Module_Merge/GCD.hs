{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  GCD(Gcda(..), Gcd(..), Semiring_gcd, Ring_gcd, Semiring_Gcd,
       Semiring_gcd_mult_normalize, gcd_int, lcm_int)
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
import qualified Set;
import qualified Unique_Factorization;
import qualified Arith;

class (Arith.One a, Arith.Zero a, Arith.Dvd a) => Gcda a where {
  gcda :: a -> a -> a;
  lcma :: a -> a -> a;
};

class (Gcda a) => Gcd a where {
  gcd :: Set.Set a -> a;
  lcm :: Set.Set a -> a;
};

class (Arith.Normalization_semidom a,
        Unique_Factorization.Comm_monoid_gcd a) => Semiring_gcd a where {
};

class (Semiring_gcd a, Unique_Factorization.Idom_gcd a) => Ring_gcd a where {
};

class (Gcd a, Semiring_gcd a) => Semiring_Gcd a where {
};

class (Semiring_gcd a,
        Arith.Normalization_semidom_multiplicative a) => Semiring_gcd_mult_normalize a where {
};

gcd_int :: Arith.Int -> Arith.Int -> Arith.Int;
gcd_int (Arith.Int_of_integer x) (Arith.Int_of_integer y) =
  Arith.Int_of_integer (Prelude.gcd x y);

lcm_integer :: Integer -> Integer -> Integer;
lcm_integer a b =
  Arith.divide_integer (Prelude.abs a * Prelude.abs b) (Prelude.gcd a b);

lcm_int :: Arith.Int -> Arith.Int -> Arith.Int;
lcm_int (Arith.Int_of_integer x) (Arith.Int_of_integer y) =
  Arith.Int_of_integer (lcm_integer x y);

}
