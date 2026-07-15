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
import qualified Arith;

fresh_strings_list ::
  [Arith.Char] -> Arith.Nat -> [[Arith.Char]] -> Arith.Nat -> [[Arith.Char]];
fresh_strings_list name offset used n =
  Arith.take n
    (filter (\ s -> not (Arith.membera (Arith.remdups used) s))
      (map (\ i ->
             name ++
               Show_Instances.shows_prec_nat Arith.zero_nat
                 (Arith.plus_nat i offset) [])
        (Arith.upt Arith.zero_nat
          (Arith.plus_nat n (Arith.size_list (Arith.remdups used))))));

fresh_string :: [Arith.Char] -> [[Arith.Char]] -> [Arith.Char];
fresh_string pre =
  (\ s -> Arith.hda (fresh_strings_list pre Arith.one_nat s Arith.one_nat));

x_1_to_x_n :: Arith.Nat -> [[Arith.Char]];
x_1_to_x_n = fresh_strings_list [Arith.char_0x78] Arith.one_nat [];

}
