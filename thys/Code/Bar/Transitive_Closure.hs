{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Transitive_Closure(trancl) where {

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
import qualified Relation;
import qualified HOL;
import qualified Arith;

ntrancl ::
  forall a.
    (Arith.Ceq a, Arith.Ccompare a,
      Arith.Set_impl a) => Arith.Nat -> Arith.Set (a, a) -> Arith.Set (a, a);
ntrancl n r =
  (if Arith.equal_nat n Arith.zero_nat then r
    else let {
           ra = ntrancl (Arith.minus_nat n Arith.one_nat) r;
         } in Arith.sup_set ra (Relation.relcomp ra r));

trancl ::
  forall a.
    (Arith.Card_UNIV a, Arith.Ceq a, Arith.Ccompare a,
      Arith.Set_impl a) => Arith.Set (a, a) -> Arith.Set (a, a);
trancl a =
  (if Arith.finite a
    then ntrancl (Arith.minus_nat (Arith.card a) Arith.one_nat) a
    else (error :: forall a. String -> (() -> a) -> a) "trancl: infinite set"
           (\ _ -> trancl a));

}
