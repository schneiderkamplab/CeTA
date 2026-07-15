{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  RBT_Map_Set_Extension(rs_Union, rs_subset, rBT_is_key, rBT_from_list,
                         rm_set_lookup, rBT_list_union, elem_list_to_rm)
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
import qualified HOL;
import qualified Option;
import qualified Utility;
import qualified Orderings;
import qualified List;
import qualified RBT;
import qualified Compare;

rs_Union ::
  forall a. (Compare.Compare_order a) => [RBT.Rbt a ()] -> RBT.Rbt a ();
rs_Union = List.foldl RBT.union RBT.empty;

rs_subset ::
  forall a.
    (Eq a, Orderings.Linorder a) => RBT.Rbt a () -> RBT.Rbt a () -> Maybe a;
rs_subset asa bs = Utility.sorted_list_subset (RBT.keys asa) (RBT.keys bs);

rBT_is_key :: forall a b. (Compare.Compare_order a) => a -> RBT.Rbt a b -> Bool;
rBT_is_key a t = not (Option.is_none (RBT.lookup t a));

rBT_from_list :: forall a. (Compare.Compare_order a) => [a] -> RBT.Rbt a ();
rBT_from_list asa = RBT.bulkload (map (\ x -> (x, ())) asa);

rm_set_lookup ::
  forall a b. (Compare.Compare_order a) => RBT.Rbt a [b] -> a -> [b];
rm_set_lookup rm = (\ a -> (case RBT.lookup rm a of {
                             Nothing -> [];
                             Just rules -> rules;
                           }));

rBT_list_union ::
  forall a. (Compare.Compare_order a) => [a] -> RBT.Rbt a () -> RBT.Rbt a ();
rBT_list_union asa bs = RBT.union bs (rBT_from_list asa);

elem_list_to_rm ::
  forall a b. (Compare.Compare_order b) => (a -> b) -> [a] -> RBT.Rbt b [a];
elem_list_to_rm key [] = RBT.empty;
elem_list_to_rm key (d : ds) = let {
                                 t = elem_list_to_rm key ds;
                                 k = key d;
                               } in (case RBT.lookup t k of {
                                      Nothing -> RBT.insert k [d] t;
                                      Just dataa -> RBT.insert k (d : dataa) t;
                                    });

}
