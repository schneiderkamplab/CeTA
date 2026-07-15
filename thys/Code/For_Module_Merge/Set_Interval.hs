{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Set_Interval(atLeastLessThan) where {

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
import qualified Set;
import qualified Collection_Order;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Orderings;
import qualified List;
import qualified Arith;

atLeastLessThan ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Eq a, List.Interval a,
      Set_Impl.Set_impl a) => a -> a -> Set.Set a;
atLeastLessThan a b =
  let {
    d = Arith.minus b Arith.one;
  } in (if Orderings.less d b then List.set (List.interval a d)
         else Set.bot_set);

}
