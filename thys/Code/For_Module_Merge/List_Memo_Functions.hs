{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  List_Memo_Functions(exists_mem, forall_mem, mul_ext_mem,
                       lex_ext_unbounded_mem)
  where {

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
import qualified Multiset_Extension_Pair_Impl;
import qualified Mapping;
import qualified Arith;
import qualified Product_Type;

exists_mem ::
  forall a b c d.
    (a -> b) -> (c -> b -> (d, c)) -> (d -> Bool) -> c -> [a] -> (Bool, c);
exists_mem pre f post mem [] = (False, mem);
exists_mem pre f post mem (x : xs) =
  (case f mem (pre x) of {
    (c, mema) ->
      (if post c then (True, mema) else exists_mem pre f post mema xs);
  });

filter_mem ::
  forall a b c d.
    (a -> b) -> (c -> b -> (d, c)) -> (d -> Bool) -> c -> [a] -> ([a], c);
filter_mem pre f post mem [] = ([], mem);
filter_mem pre f post mem (x : xs) =
  (case f mem (pre x) of {
    (c, mema) ->
      (case filter_mem pre f post mema xs of {
        (ys, memb) -> (if post c then (x : ys, memb) else (ys, memb));
      });
  });

forall_mem ::
  forall a b c d.
    (a -> b) -> (c -> b -> (d, c)) -> (d -> Bool) -> c -> [a] -> (Bool, c);
forall_mem pre f post mem [] = (True, mem);
forall_mem pre f post mem (x : xs) =
  (case f mem (pre x) of {
    (c, mema) ->
      (if post c then forall_mem pre f post mema xs else (False, mema));
  });

mul_ext_mem ::
  forall a.
    (Mapping.Mapping (Arith.Int, Arith.Int) (Bool, Bool) ->
      (a, a) ->
        ((Bool, Bool), Mapping.Mapping (Arith.Int, Arith.Int) (Bool, Bool))) ->
      Mapping.Mapping (Arith.Int, Arith.Int) (Bool, Bool) ->
        [a] ->
          [a] ->
            ((Bool, Bool), Mapping.Mapping (Arith.Int, Arith.Int) (Bool, Bool));
mul_ext_mem f mem [] [] = ((False, True), mem);
mul_ext_mem f mem [] (v : va) = ((False, False), mem);
mul_ext_mem f mem (v : va) [] = ((True, True), mem);
mul_ext_mem f mem (v : va) (y : ys) = mul_ext_dom_mem f mem (v : va) [] y ys;

mul_ext_dom_mem ::
  forall a.
    (Mapping.Mapping (Arith.Int, Arith.Int) (Bool, Bool) ->
      (a, a) ->
        ((Bool, Bool), Mapping.Mapping (Arith.Int, Arith.Int) (Bool, Bool))) ->
      Mapping.Mapping (Arith.Int, Arith.Int) (Bool, Bool) ->
        [a] ->
          [a] ->
            a -> [a] ->
                   ((Bool, Bool),
                     Mapping.Mapping (Arith.Int, Arith.Int) (Bool, Bool));
mul_ext_dom_mem f mem [] xs y ys = ((False, False), mem);
mul_ext_dom_mem f mem (x : xsa) xs y ys =
  (case f mem (x, y) of {
    ((True, _), mem_new_1) ->
      (case filter_mem (\ a -> (x, a)) f (\ p -> not (fst p)) mem_new_1 ys of {
        (ys_new, mem_new_2) ->
          (case mul_ext_mem f mem_new_2 (xsa ++ xs) ys_new of {
            (tmp_res, mem_new_3) ->
              (if snd tmp_res then ((True, True), mem_new_3)
                else mul_ext_dom_mem f mem_new_3 xsa (x : xs) y ys);
          });
      });
    ((False, True), mem_new_1) ->
      (case mul_ext_mem f mem_new_1 (xsa ++ xs) ys of {
        (sns_res_a, mem_new_2) ->
          (if sns_res_a == (True, True) then (sns_res_a, mem_new_2)
            else (case mul_ext_dom_mem f mem_new_2 xsa (x : xs) y ys of {
                   (sns_res_b, a) ->
                     (Multiset_Extension_Pair_Impl.or2 sns_res_a sns_res_b, a);
                 }));
      });
    ((False, False), mem_new_1) ->
      mul_ext_dom_mem f mem_new_1 xsa (x : xs) y ys;
  });

lex_ext_unbounded_mem ::
  forall a.
    (Mapping.Mapping (Arith.Int, Arith.Int) (Bool, Bool) ->
      (a, a) ->
        ((Bool, Bool), Mapping.Mapping (Arith.Int, Arith.Int) (Bool, Bool))) ->
      Mapping.Mapping (Arith.Int, Arith.Int) (Bool, Bool) ->
        [a] ->
          [a] ->
            ((Bool, Bool), Mapping.Mapping (Arith.Int, Arith.Int) (Bool, Bool));
lex_ext_unbounded_mem f mem [] [] = ((False, True), mem);
lex_ext_unbounded_mem f mem (uu : uv) [] = ((True, True), mem);
lex_ext_unbounded_mem f mem [] (uw : ux) = ((False, False), mem);
lex_ext_unbounded_mem f mem (a : asa) (b : bs) =
  (case f mem (a, b) of {
    ((True, _), mem_new) -> ((True, True), mem_new);
    ((False, True), mem_new) -> lex_ext_unbounded_mem f mem_new asa bs;
    ((False, False), mem_new) -> ((False, False), mem_new);
  });

}
