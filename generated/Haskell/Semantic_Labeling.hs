{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Semantic_Labeling(eval_lab, lab_root, lge_to_lgr) where {

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
import qualified Term_Rewriting;
import qualified Arith;

eval_lab ::
  forall a b c d e.
    (a -> [b] -> b) ->
      (a -> [b] -> c) ->
        (a -> Arith.Nat -> c -> d) ->
          (e -> b) -> Term_Rewriting.Term a e -> (b, Term_Rewriting.Term d e);
eval_lab i l lc alpha (Term_Rewriting.Var x) = (alpha x, Term_Rewriting.Var x);
eval_lab i l lc alpha (Term_Rewriting.Fun f ts) =
  let {
    clts = map (eval_lab i l lc alpha) ts;
    cs = map fst clts;
    c = i f cs;
    lts = map snd clts;
  } in (c, Term_Rewriting.Fun (lc f (Arith.size_list ts) (l f cs)) lts);

lab_root ::
  forall a b c d e.
    (a -> [b] -> b) ->
      (a -> [b] -> c) ->
        (a -> [b] -> c) ->
          (a -> Arith.Nat -> c -> d) ->
            (e -> b) -> Term_Rewriting.Term a e -> Term_Rewriting.Term d e;
lab_root i la l lc alpha (Term_Rewriting.Fun f ts) =
  let {
    clts = map (eval_lab i la lc alpha) ts;
    cs = map fst clts;
    a = map snd clts;
  } in Term_Rewriting.Fun (lc f (Arith.size_list ts) (l f cs)) a;
lab_root uu uv uw ux uy (Term_Rewriting.Var x) = Term_Rewriting.Var x;

lge_to_lgr ::
  forall a b.
    (Eq b) => (a -> Arith.Nat -> b -> b -> Bool) ->
                (a -> Arith.Nat -> b -> Bool) ->
                  a -> Arith.Nat -> b -> b -> Bool;
lge_to_lgr lge ls f n =
  let {
    lSfn = ls f n;
    lgefn = lge f n;
  } in (\ l la -> not (l == la) && lSfn l && lSfn la && lgefn l la);

}
