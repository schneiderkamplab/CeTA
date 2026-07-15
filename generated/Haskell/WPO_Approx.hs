{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module WPO_Approx(wpo_ub) where {

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
import qualified WPO_Mem_Impl;
import qualified WPO;
import qualified Status;
import qualified Term_Rewriting;
import qualified Arith;

wpo_ub ::
  forall a b.
    (Eq b) => ((a, Arith.Nat) -> (a, Arith.Nat) -> (Bool, Bool)) ->
                ((a, Arith.Nat) -> Bool) ->
                  Bool ->
                    ((a, Arith.Nat) -> Bool) ->
                      (Term_Rewriting.Term a b ->
                        Term_Rewriting.Term a b -> Bool) ->
                        (Term_Rewriting.Term a b ->
                          Term_Rewriting.Term a b -> Bool) ->
                          Status.Status a ->
                            ((a, Arith.Nat) -> WPO.Order_tag) ->
                              Term_Rewriting.Term a b ->
                                Term_Rewriting.Term a b -> (Bool, Bool);
wpo_ub pr prl ssimple large cS cNS sigma c s t =
  WPO_Mem_Impl.wpo_mem_impl pr prl ssimple large cS cNS sigma c s t;

}
