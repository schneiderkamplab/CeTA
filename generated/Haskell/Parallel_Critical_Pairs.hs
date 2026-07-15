{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Parallel_Critical_Pairs(Lab_filter(..), renaming2, lab_filter) where {

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
import qualified RenamingN;
import qualified Renaming2;
import qualified Arith;
import qualified Fresh;

data Lab_filter = No_Lab_Filter | Zero_Zero_Filter;

renaming2 ::
  forall a.
    (Fresh.Infinite a) => RenamingN.RenamingN a -> Renaming2.Renaming2 a;
renaming2 xa =
  Renaming2.Abs_renaming2 (case RenamingN.rep_renamingN xa of {
                            (r1, a) -> ((\ x -> r1 (Arith.zero_nat, x)), a);
                          });

lab_filter :: Lab_filter -> Arith.Nat -> Arith.Nat -> Bool;
lab_filter No_Lab_Filter k m = True;
lab_filter Zero_Zero_Filter k m =
  not (Arith.equal_nat k Arith.zero_nat) ||
    not (Arith.equal_nat m Arith.zero_nat);

}
