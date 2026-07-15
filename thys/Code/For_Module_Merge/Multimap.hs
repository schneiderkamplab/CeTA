{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Multimap(values, delete_values, insert_values, intersect_values) where {

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
import qualified Orderings;
import qualified Option;
import qualified List;
import qualified RBT;
import qualified Compare;

aux ::
  forall a b.
    (Eq a,
      Compare.Compare_order b) => (a -> Maybe b) ->
                                    RBT.Rbt b [a] ->
                                      a -> RBT.Rbt b [a] -> RBT.Rbt b [a];
aux key ma v m =
  (case key v of {
    Nothing -> m;
    Just k ->
      (case RBT.lookup ma k of {
        Nothing -> m;
        Just ws ->
          (if List.member ws v
            then (case RBT.lookup m k of {
                   Nothing -> RBT.insert k [v] m;
                   Just vs -> RBT.insert k (List.insert v vs) m;
                 })
            else m);
      });
  });

values :: forall a b. (Orderings.Linorder a) => RBT.Rbt a [b] -> [b];
values m = concatMap snd (RBT.entries m);

delete_value ::
  forall a b.
    (Eq a,
      Compare.Compare_order b) => (a -> Maybe b) ->
                                    a -> RBT.Rbt b [a] -> RBT.Rbt b [a];
delete_value key v m =
  (case key v of {
    Nothing -> m;
    Just k -> (case RBT.lookup m k of {
                Nothing -> m;
                Just vs -> RBT.insert k (List.removeAll v vs) m;
              });
  });

insert_value ::
  forall a b.
    (Eq a,
      Compare.Compare_order b) => (a -> Maybe b) ->
                                    a -> RBT.Rbt b [a] -> RBT.Rbt b [a];
insert_value key v m =
  (case key v of {
    Nothing -> m;
    Just k -> (case RBT.lookup m k of {
                Nothing -> RBT.insert k [v] m;
                Just vs -> RBT.insert k (List.insert v vs) m;
              });
  });

delete_values ::
  forall a b.
    (Eq a,
      Compare.Compare_order b) => (a -> Maybe b) ->
                                    [a] -> RBT.Rbt b [a] -> RBT.Rbt b [a];
delete_values uu [] m = m;
delete_values key (v : vs) m = delete_value key v (delete_values key vs m);

insert_values ::
  forall a b.
    (Eq a,
      Compare.Compare_order b) => (a -> Maybe b) ->
                                    [a] -> RBT.Rbt b [a] -> RBT.Rbt b [a];
insert_values uu [] m = m;
insert_values key (v : vs) m = insert_value key v (insert_values key vs m);

intersect_values ::
  forall a b.
    (Eq a,
      Compare.Compare_order b) => (a -> Maybe b) ->
                                    [a] -> RBT.Rbt b [a] -> RBT.Rbt b [a];
intersect_values key vs m = List.foldr (aux key m) vs RBT.empty;

}
