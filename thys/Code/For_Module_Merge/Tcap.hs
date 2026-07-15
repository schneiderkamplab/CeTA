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
import qualified Ground_Context;
import qualified Term;
import qualified Set;
import qualified Compare;
import qualified Collection_Order;
import qualified Collection_Eq;
import qualified Container_Setup;

tcap ::
  forall a b.
    (Compare.Compare a, Eq a, Compare.Compare b,
      Eq b) => Set.Set (Term.Term a b, Term.Term a b) ->
                 Term.Term a b -> Ground_Context.Gctxt a b;
tcap uu (Term.Var uv) = Ground_Context.GCHole;
tcap r (Term.Fun f ts) =
  let {
    h = Ground_Context.GCFun f (map (tcap r) ts);
  } in (if Set.bex r (\ ra -> Ground_Context.match h (fst ra))
         then Ground_Context.GCHole else h);

}
