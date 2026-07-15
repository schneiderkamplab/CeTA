{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Transitive_Closure_Impl(trancl_impl, rtrancl_impl) where {

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
import qualified List;
import qualified HOL;
import qualified Arith;

relpow_impl ::
  forall a b.
    ([a] -> [a]) ->
      ([a] -> b -> b) -> (a -> b -> Bool) -> [a] -> b -> Arith.Nat -> b;
relpow_impl succ un memb new have m =
  (if Arith.equal_nat m Arith.zero_nat then un new have
    else (if null new then have
           else let {
                  maybe = succ new;
                  havea = un new have;
                  newa = filter (\ n -> not (memb n havea)) maybe;
                } in relpow_impl succ un memb newa havea
                       (Arith.minus_nat m Arith.one_nat)));

trancl_impl ::
  forall a b.
    ([(a, a)] -> [a] -> [a]) ->
      ([a] -> b -> b) -> (a -> b -> Bool) -> b -> [(a, a)] -> [a] -> b;
trancl_impl gen_succ un memb emp rel =
  let {
    succ = gen_succ rel;
    n = List.size_list rel;
  } in (\ asa -> relpow_impl succ un memb (succ asa) emp n);

rtrancl_impl ::
  forall a b.
    ([(a, a)] -> [a] -> [a]) ->
      ([a] -> b -> b) -> (a -> b -> Bool) -> b -> [(a, a)] -> [a] -> b;
rtrancl_impl gen_succ un memb emp rel =
  let {
    succ = gen_succ rel;
    n = List.size_list rel;
  } in (\ asa -> relpow_impl succ un memb asa emp n);

}
