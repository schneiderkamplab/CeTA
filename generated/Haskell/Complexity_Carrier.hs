{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Complexity_Carrier(Large_real_ordered_semiring_1) where {

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
import qualified Quasi_Order;
import qualified Arith;
import qualified SN_Orders;
import qualified Term_Rewriting;
import qualified Ring_Hom_Matrix;

class (Ring_Hom_Matrix.Real_embedding a,
        SN_Orders.Large_ordered_semiring_1 a) => Large_real_ordered_semiring_1 a where {
};

instance Large_real_ordered_semiring_1 Arith.Int where {
};

instance Large_real_ordered_semiring_1 Term_Rewriting.Rat where {
};

instance Large_real_ordered_semiring_1 Term_Rewriting.Real where {
};

}
