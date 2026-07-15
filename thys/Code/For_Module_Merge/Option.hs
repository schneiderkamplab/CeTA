{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Option(bind, these, is_none, the, map_option, rel_option, set_option)
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
import qualified List;
import qualified RBT_Set2;
import qualified RBT_Mapping2;
import qualified DList_Set;
import qualified Comparator;
import qualified Set;
import qualified Set_Impl;
import qualified Collection_Order;
import qualified Collection_Eq;

bind :: forall a b. Maybe a -> (a -> Maybe b) -> Maybe b;
bind Nothing f = Nothing;
bind (Just x) f = f x;

image_filter ::
  forall a b.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Collection_Eq.Ceq b,
      Collection_Order.Ccompare b,
      Set_Impl.Set_impl b) => (a -> Maybe b) -> Set.Set a -> Set.Set b;
image_filter h (Set.RBT_set rbt) =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "Option.image_filter RBT_set: ccompare = None"
        (\ _ -> image_filter h (Set.RBT_set rbt));
    Just _ ->
      RBT_Set2.fold (\ x a -> (case h x of {
                                Nothing -> a;
                                Just y -> Set.insert y a;
                              }))
        rbt Set.bot_set;
  });
image_filter g (Set.DList_set dxs) =
  (case (Collection_Eq.ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "Option.image_filter DList_set: ceq = None"
        (\ _ -> image_filter g (Set.DList_set dxs));
    Just _ ->
      DList_Set.fold (\ x a -> (case g x of {
                                 Nothing -> a;
                                 Just y -> Set.insert y a;
                               }))
        dxs Set.bot_set;
  });
image_filter f (Set.Set_Monad xs) = Set.Set_Monad (List.map_filter f xs);

these ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Set_Impl.Set_impl a) => Set.Set (Maybe a) -> Set.Set a;
these a = image_filter (\ x -> x) a;

is_none :: forall a. Maybe a -> Bool;
is_none Nothing = True;
is_none (Just x) = False;

the :: forall a. Maybe a -> a;
the (Just x2) = x2;

map_option :: forall a b. (a -> b) -> Maybe a -> Maybe b;
map_option f Nothing = Nothing;
map_option f (Just x2) = Just (f x2);

rel_option :: forall a b. (a -> b -> Bool) -> Maybe a -> Maybe b -> Bool;
rel_option r Nothing (Just y2) = False;
rel_option r (Just y2) Nothing = False;
rel_option r Nothing Nothing = True;
rel_option r (Just x2) (Just y2) = r x2 y2;

set_option ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Set_Impl.Set_impl a) => Maybe a -> Set.Set a;
set_option Nothing = Set.bot_set;
set_option (Just x2) = Set.insert x2 Set.bot_set;

}
