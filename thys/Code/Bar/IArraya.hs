{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module IArraya(length, sub, list_of, equal_iarray, of_fun) where {

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

length :: forall a. IArray.IArray a -> Arith.Nat;
length asa = Arith.nat_of_integer (IArray.length asa);

sub :: forall a. IArray.IArray a -> Arith.Nat -> a;
sub asa n = IArray.sub (asa, Arith.integer_of_nat n);

list_of :: forall a. IArray.IArray a -> [a];
list_of asa = map (sub asa) (Arith.upt Arith.zero_nat (length asa));

equal_iarray :: forall a. (Eq a) => IArray.IArray a -> IArray.IArray a -> Bool;
equal_iarray asa bs = list_of asa == list_of bs;

instance (Eq a) => Eq (IArray.IArray a) where {
  a == b = equal_iarray a b;
};

of_fun :: forall a. (Arith.Nat -> a) -> Arith.Nat -> IArray.IArray a;
of_fun f n = IArray.tabulate (Arith.integer_of_nat n, f . Arith.nat_of_integer);

}
