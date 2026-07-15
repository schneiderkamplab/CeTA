{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Tree_Automata_Det_Container(memo_list_rtrancl_set) where {

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
import qualified Transitive_Closure_List_Impl;
import qualified Option;
import qualified List;
import qualified Map;
import qualified HOL;
import qualified Set;
import qualified Collection_Order;
import qualified Set_Impl;
import qualified Collection_Eq;

memo_list_rtrancl_set ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Eq a,
      Set_Impl.Set_impl a) => [(a, a)] -> a -> Set.Set a;
memo_list_rtrancl_set r =
  let {
    tr = Transitive_Closure_List_Impl.rtrancl_list_impl r;
    rm = Map.map_of
           (map (\ a -> (a, List.set (tr [a]))) ((List.remdups . map fst) r));
  } in (\ a -> (case rm a of {
                 Nothing -> Set.insert a Set.bot_set;
                 Just asa -> asa;
               }));

}
