{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module More_List(nth_default, strip_while) where {

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
import qualified Arith;

nth_default :: forall a. a -> [a] -> Arith.Nat -> a;
nth_default dflt xs n =
  (if Arith.less_nat n (Arith.size_list xs) then Arith.nth xs n else dflt);

strip_while :: forall a. (a -> Bool) -> [a] -> [a];
strip_while p = (reverse . dropWhile p) . reverse;

}
