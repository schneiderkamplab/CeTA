{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Mapping(Mapping_impla(..), Mapping_impl(..), mapping_impl_nat,
           mapping_impl_list, mapping_impl_prod, Mapping, mapping_empty, empty,
           delete, lookup, update, of_alist, tabulate, lookup_default)
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
import qualified AssocList;
import qualified Fun;
import qualified Comparator;
import qualified DAList;
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

data Mapping a b = Assoc_List_Mapping (DAList.Alist a b)
  | RBT_Mapping (Arith.Mapping_rbt a b) | Mapping (a -> Maybe b);

mapping_empty_choose :: forall a b. (Arith.Ccompare a) => Mapping a b;
mapping_empty_choose =
  (case (Arith.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing -> Assoc_List_Mapping DAList.empty;
    Just _ -> RBT_Mapping Arith.emptya;
  });

mapping_empty :: forall a b. (Arith.Ccompare a) => Mapping_impla -> Mapping a b;
mapping_empty Mapping_RBT = RBT_Mapping Arith.emptya;
mapping_empty Mapping_Assoc_List = Assoc_List_Mapping DAList.empty;
mapping_empty Mapping_Mapping = Mapping (\ _ -> Nothing);
mapping_empty Mapping_Choose = mapping_empty_choose;

empty :: forall a b. (Arith.Ccompare a, Mapping_impl a) => Mapping a b;
empty =
  mapping_empty
    (Phantom_Type.of_phantom
      (mapping_impl :: Phantom_Type.Phantom a Mapping_impla));

delete ::
  forall a b. (Arith.Ccompare a, Eq a) => a -> Mapping a b -> Mapping a b;
delete k (RBT_Mapping t) =
  (case (Arith.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "delete RBT_Mapping: ccompare = None" (\ _ -> delete k (RBT_Mapping t));
    Just _ -> RBT_Mapping (Arith.delete k t);
  });
delete k (Assoc_List_Mapping al) = Assoc_List_Mapping (AssocList.delete k al);
delete k (Mapping m) = Mapping (Fun.fun_upd m k Nothing);

lookup :: forall a b. (Arith.Ccompare a, Eq a) => Mapping a b -> a -> Maybe b;
lookup (RBT_Mapping t) = Arith.lookup t;
lookup (Assoc_List_Mapping al) = DAList.lookup al;

update ::
  forall a b. (Arith.Ccompare a, Eq a) => a -> b -> Mapping a b -> Mapping a b;
update k v (RBT_Mapping t) =
  (case (Arith.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "update RBT_Mapping: ccompare = None"
        (\ _ -> update k v (RBT_Mapping t));
    Just _ -> RBT_Mapping (Arith.insertc k v t);
  });
update k v (Assoc_List_Mapping al) = Assoc_List_Mapping (DAList.update k v al);
update k v (Mapping m) = Mapping (Fun.fun_upd m k (Just v));

of_alist ::
  forall a b.
    (Arith.Ccompare a, Eq a, Mapping_impl a) => [(a, b)] -> Mapping a b;
of_alist xs = Arith.foldr (\ (a, b) -> update a b) xs empty;

tabulate ::
  forall a b.
    (Arith.Ccompare a, Eq a, Mapping_impl a) => [a] -> (a -> b) -> Mapping a b;
tabulate xs f = Arith.fold (\ k -> update k (f k)) xs empty;

lookup_default ::
  forall a b. (Arith.Ccompare b, Eq b) => a -> Mapping b a -> b -> a;
lookup_default d m k = (case lookup m k of {
                         Nothing -> d;
                         Just v -> v;
                       });

}
