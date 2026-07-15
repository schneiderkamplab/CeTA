{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Multiset_Extension2_Impl(mul_ext_impl, ass_list_to_single_list) where {

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
import qualified Arith;
import qualified Multiset_Extension_Pair_Impl;
import qualified Product_Type;

mul_ex_dom ::
  forall a. (a -> a -> (Bool, Bool)) -> [a] -> [a] -> a -> [a] -> (Bool, Bool);
mul_ex_dom sns [] xs y ys = (False, False);
mul_ex_dom sns (x : xsa) xs y ys =
  (case sns x y of {
    (True, _) ->
      (if snd (mul_ext_impl sns (xsa ++ xs)
                (filter (\ ya -> not (fst (sns x ya))) ys))
        then (True, True) else mul_ex_dom sns xsa (x : xs) y ys);
    (False, True) ->
      Multiset_Extension_Pair_Impl.or2 (mul_ext_impl sns (xsa ++ xs) ys)
        (mul_ex_dom sns xsa (x : xs) y ys);
    (False, False) -> mul_ex_dom sns xsa (x : xs) y ys;
  });

mul_ext_impl ::
  forall a. (a -> a -> (Bool, Bool)) -> [a] -> [a] -> (Bool, Bool);
mul_ext_impl sns [] [] = (False, True);
mul_ext_impl sns [] (v : va) = (False, False);
mul_ext_impl sns (v : va) [] = (True, True);
mul_ext_impl sns (v : va) (y : ys) = mul_ex_dom sns (v : va) [] y ys;

ass_list_to_single_list :: forall a. [(a, Arith.Nat)] -> [a];
ass_list_to_single_list [] = [];
ass_list_to_single_list ((x, n) : xs) =
  List.replicate n x ++ ass_list_to_single_list xs;

}
