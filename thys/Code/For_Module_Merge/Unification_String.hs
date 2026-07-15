{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Unification_String(mgu_vd_string) where {

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
import qualified Unification;
import qualified Term;
import qualified Str;

mgu_vd_string ::
  forall a.
    (Eq a) => Term.Term a [Str.Char] ->
                Term.Term a [Str.Char] ->
                  Maybe ([Str.Char] -> Term.Term a [Str.Char],
                          [Str.Char] -> Term.Term a [Str.Char]);
mgu_vd_string =
  Unification.mgu_var_disjoint_generic (\ a -> Str.char_0x78 : a)
    (\ a -> Str.char_0x79 : a);

}
