{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Matrix_Kernel(kernel_dim) where {

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
import qualified Gauss_Jordan_Elimination;
import qualified List;
import qualified Matrix;
import qualified Arith;

kernel_dim :: forall a. (Arith.Field a, Eq a) => Matrix.Mat a -> Arith.Nat;
kernel_dim a =
  Arith.minus_nat (Matrix.dim_col a)
    (List.size_list
      (Gauss_Jordan_Elimination.pivot_positions_gen Arith.zero
        (Gauss_Jordan_Elimination.gauss_jordan_single a)));

}
