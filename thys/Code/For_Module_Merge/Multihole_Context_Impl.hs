{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Multihole_Context_Impl(add_funas_mctxt, showsl_mctxt) where {

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
import qualified Shows_Literal;
import qualified List;
import qualified Multihole_Context;
import qualified Arith;

add_funas_mctxt ::
  forall a b.
    Multihole_Context.Mctxt a b -> [(a, Arith.Nat)] -> [(a, Arith.Nat)];
add_funas_mctxt (Multihole_Context.MFun f cs) fs =
  (f, List.size_list cs) : List.foldr add_funas_mctxt cs fs;
add_funas_mctxt (Multihole_Context.MVar v) fs = fs;
add_funas_mctxt Multihole_Context.MHole fs = fs;

showsl_mctxt ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => Multihole_Context.Mctxt a b -> String -> String;
showsl_mctxt Multihole_Context.MHole = Shows_Literal.showsl_lit "[]";
showsl_mctxt (Multihole_Context.MVar x) = Shows_Literal.showsl x;
showsl_mctxt (Multihole_Context.MFun f cs) =
  Shows_Literal.showsl f .
    Shows_Literal.showsl_list_gen id "" "(" ", " ")" (map showsl_mctxt cs);

}
