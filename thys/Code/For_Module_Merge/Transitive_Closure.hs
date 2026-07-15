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
import qualified Finite_Set;
import qualified Set;
import qualified Arith;
import qualified Set_Impl;
import qualified Collection_Order;
import qualified Cardinality;
import qualified Collection_Eq;

ntrancl ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Set_Impl.Set_impl a) => Arith.Nat -> Set.Set (a, a) -> Set.Set (a, a);
ntrancl n r =
  (if Arith.equal_nat n Arith.zero_nat then r
    else let {
           ra = ntrancl (Arith.minus_nat n Arith.one_nat) r;
         } in Set.sup_set ra (Relation.relcomp ra r));

trancl ::
  forall a.
    (Cardinality.Card_UNIV a, Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Set_Impl.Set_impl a) => Set.Set (a, a) -> Set.Set (a, a);
trancl a =
  (if Finite_Set.finite a
    then ntrancl (Arith.minus_nat (Finite_Set.card a) Arith.one_nat) a
    else (error :: forall a. String -> (() -> a) -> a) "trancl: infinite set"
           (\ _ -> trancl a));

}
