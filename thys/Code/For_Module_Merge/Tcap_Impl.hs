{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Tcap_Impl(tcapI, tcapRM2, tcapRM, match_tcap_below_impl) where {

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
import qualified HOL;
import qualified Ground_Context;
import qualified Term;

tcapI ::
  forall a b.
    (Eq a,
      Eq b) => [(Term.Term a b, Term.Term a b)] ->
                 Term.Term a b -> Ground_Context.Gctxt a b;
tcapI uu (Term.Var uv) = Ground_Context.GCHole;
tcapI r (Term.Fun f ts) =
  let {
    h = Ground_Context.GCFun f (map (tcapI r) ts);
  } in (if any (\ ra -> Ground_Context.match h (fst ra)) r
         then Ground_Context.GCHole else h);

tcapRM2 ::
  forall a b.
    (Eq a,
      Eq b) => ((a, Arith.Nat) -> [(Term.Term a b, Term.Term a b)]) ->
                 Term.Term a b -> Ground_Context.Gctxt a b;
tcapRM2 uu (Term.Var uv) = Ground_Context.GCHole;
tcapRM2 rm (Term.Fun f ts) =
  let {
    h = Ground_Context.GCFun f (map (tcapRM2 rm) ts);
    n = List.size_list ts;
  } in (if any (\ r -> Ground_Context.match h (fst r)) (rm (f, n))
         then Ground_Context.GCHole else h);

tcapRM ::
  forall a b.
    (Eq a,
      Eq b) => Bool ->
                 ((a, Arith.Nat) -> [(Term.Term a b, Term.Term a b)]) ->
                   Term.Term a b -> Ground_Context.Gctxt a b;
tcapRM nlv rm = (if nlv then tcapRM2 rm else (\ _ -> Ground_Context.GCHole));

match_tcap_below_impl ::
  forall a b.
    (Eq a,
      Eq b) => Term.Term a b ->
                 [(Term.Term a b, Term.Term a b)] -> Term.Term a b -> Bool;
match_tcap_below_impl l r (Term.Fun f ts) =
  Ground_Context.match (Ground_Context.GCFun f (map (tcapI r) ts)) l;
match_tcap_below_impl l r (Term.Var x) = False;

}
