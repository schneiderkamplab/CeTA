{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Name(fresh_strings_list, fresh_string, x_1_to_x_n) where {

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
import qualified Show_Instances;
import qualified List;
import qualified Str;
import qualified Arith;

fresh_strings_list ::
  [Str.Char] -> Arith.Nat -> [[Str.Char]] -> Arith.Nat -> [[Str.Char]];
fresh_strings_list name offset used n =
  List.take n
    (filter (\ s -> not (List.member (List.remdups used) s))
      (map (\ i ->
             name ++
               Show_Instances.shows_prec_nat Arith.zero_nat
                 (Arith.plus_nat i offset) [])
        (List.upt Arith.zero_nat
          (Arith.plus_nat n (List.size_list (List.remdups used))))));

fresh_string :: [Str.Char] -> [[Str.Char]] -> [Str.Char];
fresh_string pre =
  (\ s -> List.hd (fresh_strings_list pre Arith.one_nat s Arith.one_nat));

x_1_to_x_n :: Arith.Nat -> [[Str.Char]];
x_1_to_x_n = fresh_strings_list [Str.char_0x78] Arith.one_nat [];

}
