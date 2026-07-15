{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Mapping_Impl(Mapping_impla(..), Mapping_impl(..), mapping_impl_nat,
                mapping_impl_list, mapping_impl_prod, mapping_empty)
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
import qualified Option;
import qualified Comparator;
import qualified RBT_Mapping2;
import qualified Mapping;
import qualified DAList;
import qualified Collection_Order;
import qualified Phantom_Type;
import qualified Arith;

data Mapping_impla = Mapping_Choose | Mapping_Assoc_List | Mapping_RBT
  | Mapping_Mapping;

mapping_impl_int :: Phantom_Type.Phantom Arith.Int Mapping_impla;
mapping_impl_int = Phantom_Type.Phantom Mapping_RBT;

class Mapping_impl a where {
  mapping_impl :: Phantom_Type.Phantom a Mapping_impla;
};

instance Mapping_impl Arith.Int where {
  mapping_impl = mapping_impl_int;
};

mapping_impl_nat :: Phantom_Type.Phantom Arith.Nat Mapping_impla;
mapping_impl_nat = Phantom_Type.Phantom Mapping_RBT;

instance Mapping_impl Arith.Nat where {
  mapping_impl = mapping_impl_nat;
};

mapping_impl_list :: forall a. Phantom_Type.Phantom [a] Mapping_impla;
mapping_impl_list = Phantom_Type.Phantom Mapping_Choose;

instance Mapping_impl [a] where {
  mapping_impl = mapping_impl_list;
};

mapping_impl_option ::
  forall a. (Mapping_impl a) => Phantom_Type.Phantom (Maybe a) Mapping_impla;
mapping_impl_option =
  Phantom_Type.Phantom
    (Phantom_Type.of_phantom
      (mapping_impl :: Phantom_Type.Phantom a Mapping_impla));

instance (Mapping_impl a) => Mapping_impl (Maybe a) where {
  mapping_impl = mapping_impl_option;
};

mapping_impl_choose2 :: Mapping_impla -> Mapping_impla -> Mapping_impla;
mapping_impl_choose2 Mapping_RBT Mapping_RBT = Mapping_RBT;
mapping_impl_choose2 Mapping_Assoc_List Mapping_Assoc_List = Mapping_Assoc_List;
mapping_impl_choose2 Mapping_Mapping Mapping_Mapping = Mapping_Mapping;
mapping_impl_choose2 x y = Mapping_Choose;

mapping_impl_prod ::
  forall a b.
    (Mapping_impl a,
      Mapping_impl b) => Phantom_Type.Phantom (a, b) Mapping_impla;
mapping_impl_prod =
  Phantom_Type.Phantom
    (mapping_impl_choose2
      (Phantom_Type.of_phantom
        (mapping_impl :: Phantom_Type.Phantom a Mapping_impla))
      (Phantom_Type.of_phantom
        (mapping_impl :: Phantom_Type.Phantom b Mapping_impla)));

instance (Mapping_impl a, Mapping_impl b) => Mapping_impl (a, b) where {
  mapping_impl = mapping_impl_prod;
};

mapping_empty_choose ::
  forall a b. (Collection_Order.Ccompare a) => Mapping.Mapping a b;
mapping_empty_choose =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing -> Mapping.Assoc_List_Mapping DAList.empty;
    Just _ -> Mapping.RBT_Mapping RBT_Mapping2.empty;
  });

mapping_empty ::
  forall a b.
    (Collection_Order.Ccompare a) => Mapping_impla -> Mapping.Mapping a b;
mapping_empty Mapping_RBT = Mapping.RBT_Mapping RBT_Mapping2.empty;
mapping_empty Mapping_Assoc_List = Mapping.Assoc_List_Mapping DAList.empty;
mapping_empty Mapping_Mapping = Mapping.Mapping (\ _ -> Nothing);
mapping_empty Mapping_Choose = mapping_empty_choose;

}
