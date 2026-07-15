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
import qualified Map;
import qualified HOL;
import qualified Arith;

memo_list_rtrancl_set ::
  forall a.
    (Arith.Ceq a, Arith.Ccompare a, Eq a,
      Arith.Set_impl a) => [(a, a)] -> a -> Arith.Set a;
memo_list_rtrancl_set r =
  let {
    tr = Transitive_Closure_List_Impl.rtrancl_list_impl r;
    rm = Map.map_of
           (map (\ a -> (a, Arith.set (tr [a]))) ((Arith.remdups . map fst) r));
  } in (\ a -> (case rm a of {
                 Nothing -> Arith.insert a Arith.bot_set;
                 Just asa -> asa;
               }));

}
