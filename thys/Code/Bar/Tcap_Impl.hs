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
import qualified Arith;
import qualified HOL;
import qualified Term_Rewriting;

tcapI ::
  forall a b.
    (Eq a,
      Eq b) => [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                 Term_Rewriting.Term a b -> Term_Rewriting.Gctxt a b;
tcapI uu (Term_Rewriting.Var uv) = Term_Rewriting.GCHole;
tcapI r (Term_Rewriting.Fun f ts) =
  let {
    h = Term_Rewriting.GCFun f (map (tcapI r) ts);
  } in (if any (\ ra -> Term_Rewriting.matcha h (fst ra)) r
         then Term_Rewriting.GCHole else h);

tcapRM2 ::
  forall a b.
    (Eq a,
      Eq b) => ((a, Arith.Nat) ->
                 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]) ->
                 Term_Rewriting.Term a b -> Term_Rewriting.Gctxt a b;
tcapRM2 uu (Term_Rewriting.Var uv) = Term_Rewriting.GCHole;
tcapRM2 rm (Term_Rewriting.Fun f ts) =
  let {
    h = Term_Rewriting.GCFun f (map (tcapRM2 rm) ts);
    n = Arith.size_list ts;
  } in (if any (\ r -> Term_Rewriting.matcha h (fst r)) (rm (f, n))
         then Term_Rewriting.GCHole else h);

tcapRM ::
  forall a b.
    (Eq a,
      Eq b) => Bool ->
                 ((a, Arith.Nat) ->
                   [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]) ->
                   Term_Rewriting.Term a b -> Term_Rewriting.Gctxt a b;
tcapRM nlv rm = (if nlv then tcapRM2 rm else (\ _ -> Term_Rewriting.GCHole));

match_tcap_below_impl ::
  forall a b.
    (Eq a,
      Eq b) => Term_Rewriting.Term a b ->
                 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                   Term_Rewriting.Term a b -> Bool;
match_tcap_below_impl l r (Term_Rewriting.Fun f ts) =
  Term_Rewriting.matcha (Term_Rewriting.GCFun f (map (tcapI r) ts)) l;
match_tcap_below_impl l r (Term_Rewriting.Var x) = False;

}
