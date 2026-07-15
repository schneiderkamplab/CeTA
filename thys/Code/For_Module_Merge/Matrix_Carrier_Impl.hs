{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Matrix_Carrier_Impl() where {

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
import qualified Matrix_IArray_Impl;
import qualified Comparator;
import qualified Collection_Order;
import qualified Collection_Enum;
import qualified Phantom_Type;
import qualified Set_Impl;
import qualified Matrix;
import qualified Collection_Eq;

ceq_mat :: forall a. (Eq a) => Maybe (Matrix.Mat a -> Matrix.Mat a -> Bool);
ceq_mat = Just Matrix_IArray_Impl.equal_mat;

instance (Eq a) => Collection_Eq.Ceq (Matrix.Mat a) where {
  ceq = ceq_mat;
};

set_impl_mat ::
  forall a. Phantom_Type.Phantom (Matrix.Mat a) Set_Impl.Set_impla;
set_impl_mat = Phantom_Type.Phantom Set_Impl.Set_DList;

instance Set_Impl.Set_impl (Matrix.Mat a) where {
  set_impl = set_impl_mat;
};

cEnum_mat ::
  forall a.
    Maybe ([Matrix.Mat a],
            ((Matrix.Mat a -> Bool) -> Bool, (Matrix.Mat a -> Bool) -> Bool));
cEnum_mat = Nothing;

instance Collection_Enum.Cenum (Matrix.Mat a) where {
  cEnum = cEnum_mat;
};

ccompare_mat ::
  forall a. Maybe (Matrix.Mat a -> Matrix.Mat a -> Comparator.Order);
ccompare_mat = Nothing;

instance Collection_Order.Ccompare (Matrix.Mat a) where {
  ccompare = ccompare_mat;
};

}
