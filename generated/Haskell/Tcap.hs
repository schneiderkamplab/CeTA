{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Tcap(tcap) where {

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
import qualified Compare;
import qualified Arith;
import qualified Term_Rewriting;

tcap ::
  forall a b.
    (Compare.Compare a, Eq a, Compare.Compare b,
      Eq b) => Arith.Set (Term_Rewriting.Term a b, Term_Rewriting.Term a b) ->
                 Term_Rewriting.Term a b -> Term_Rewriting.Gctxt a b;
tcap uu (Term_Rewriting.Var uv) = Term_Rewriting.GCHole;
tcap r (Term_Rewriting.Fun f ts) =
  let {
    h = Term_Rewriting.GCFun f (map (tcap r) ts);
  } in (if Arith.bex r (\ ra -> Term_Rewriting.matcha h (fst ra))
         then Term_Rewriting.GCHole else h);

}
