{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Archimedean_Field(Archimedean_field, Floor_ceiling(..), ceiling) where {

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
import qualified Arith;
import qualified SN_Orders;

class (Arith.Linordered_field a) => Archimedean_field a where {
};

class (Archimedean_field a,
        SN_Orders.Large_ordered_semiring_1 a) => Floor_ceiling a where {
  floor :: a -> Arith.Int;
};

ceiling :: forall a. (Floor_ceiling a) => a -> Arith.Int;
ceiling x = Arith.uminus_int (floor (Arith.uminus x));

}
