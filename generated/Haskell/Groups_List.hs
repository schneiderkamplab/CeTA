{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Groups_List(sum_list, prod_list, horner_sum) where {

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

sum_list :: forall a. (Arith.Monoid_add a) => [a] -> a;
sum_list xs = Arith.foldr Arith.plus xs Arith.zero;

prod_list :: forall a. (Arith.Monoid_mult a) => [a] -> a;
prod_list xs = Arith.foldr Arith.times xs Arith.one;

horner_sum ::
  forall a b. (Arith.Comm_semiring_0 b) => (a -> b) -> b -> [a] -> b;
horner_sum f a xs =
  Arith.foldr (\ x b -> Arith.plus (f x) (Arith.times a b)) xs Arith.zero;

}
