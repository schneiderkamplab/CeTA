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
import qualified Quasi_Order;
import qualified Arith;

atLeastLessThan ::
  forall a.
    (Arith.Ceq a, Arith.Ccompare a, Eq a, Arith.Interval a,
      Arith.Set_impl a) => a -> a -> Arith.Set a;
atLeastLessThan a b =
  let {
    d = Arith.minusa b Arith.one;
  } in (if Quasi_Order.less d b then Arith.set (Arith.interval a d)
         else Arith.bot_set);

}
