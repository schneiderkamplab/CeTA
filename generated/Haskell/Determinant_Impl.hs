{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Determinant_Impl(det_code, fst_sel_fun, trivial_mute_fun) where {

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
import qualified Groups_List;
import qualified Gauss_Jordan_Elimination;
import qualified HOL;
import qualified Matrix;
import qualified Arith;

mute ::
  forall a.
    (Eq a,
      Arith.Idom_divide a) => (a -> a -> (a, (a, a))) ->
                                a -> Arith.Nat ->
                                       Arith.Nat ->
 (a, Matrix.Mat a) -> (a, Matrix.Mat a);
mute mf a_ll k l (r, a) =
  let {
    p = Matrix.index_mat a (k, l);
  } in (if p == Arith.zero then (r, a)
         else (case mf a_ll p of {
                (q, (pa, _)) ->
                  (Arith.times r q,
                    Gauss_Jordan_Elimination.mat_addrow_gen Arith.plus
                      Arith.times (Arith.uminus pa) k l
                      (Gauss_Jordan_Elimination.mat_multrow_gen Arith.times k q
                        a));
              }));

sub1 ::
  forall a.
    (Eq a,
      Arith.Idom_divide a) => (a -> a -> (a, (a, a))) ->
                                a -> Arith.Nat ->
                                       Arith.Nat ->
 (a, Matrix.Mat a) -> (a, Matrix.Mat a);
sub1 mf q k l rA =
  (if Arith.equal_nat k Arith.zero_nat then rA
    else mute mf q
           (Arith.plus_nat l (Arith.suc (Arith.minus_nat k Arith.one_nat))) l
           (sub1 mf q (Arith.minus_nat k Arith.one_nat) l rA));

find_non0 ::
  forall a.
    (Eq a,
      Arith.Idom_divide a) => ([(Arith.Nat, a)] -> Arith.Nat) ->
                                Arith.Nat -> Matrix.Mat a -> Maybe Arith.Nat;
find_non0 sel_fun l a =
  let {
    is = Arith.upt (Arith.suc l) (Matrix.dim_row a);
    ais = filter (\ (_, ail) -> not (ail == Arith.zero))
            (map (\ i -> (i, Matrix.index_mat a (i, l))) is);
  } in (case ais of {
         [] -> Nothing;
         _ : _ -> Just (sel_fun ais);
       });

sub2 ::
  forall a.
    (Eq a,
      Arith.Idom_divide a) => ([(Arith.Nat, a)] -> Arith.Nat) ->
                                (a -> a -> (a, (a, a))) ->
                                  Arith.Nat ->
                                    Arith.Nat ->
                                      (a, Matrix.Mat a) -> (a, Matrix.Mat a);
sub2 sel_fun mf d l (r, a) =
  (case find_non0 sel_fun l a of {
    Nothing -> (r, a);
    Just m ->
      let {
        aa = Gauss_Jordan_Elimination.mat_swaprows m l a;
      } in sub1 mf (Matrix.index_mat aa (l, l))
             (Arith.minus_nat d (Arith.suc l)) l (Arith.uminus r, aa);
  });

sub3 ::
  forall a.
    (Eq a,
      Arith.Idom_divide a) => ([(Arith.Nat, a)] -> Arith.Nat) ->
                                (a -> a -> (a, (a, a))) ->
                                  Arith.Nat ->
                                    Arith.Nat ->
                                      (a, Matrix.Mat a) -> (a, Matrix.Mat a);
sub3 sel_fun mf d l rA =
  (if Arith.equal_nat l Arith.zero_nat then rA
    else sub2 sel_fun mf d (Arith.minus_nat l Arith.one_nat)
           (sub3 sel_fun mf d (Arith.minus_nat l Arith.one_nat) rA));

triangulize ::
  forall a.
    (Eq a,
      Arith.Idom_divide a) => ([(Arith.Nat, a)] -> Arith.Nat) ->
                                (a -> a -> (a, (a, a))) ->
                                  Matrix.Mat a -> (a, Matrix.Mat a);
triangulize sel_fun mf a =
  sub3 sel_fun mf (Matrix.dim_row a) (Matrix.dim_row a) (Arith.one, a);

det_code ::
  forall a.
    (Eq a,
      Arith.Idom_divide a) => ([(Arith.Nat, a)] -> Arith.Nat) ->
                                (a -> a -> (a, (a, a))) -> Matrix.Mat a -> a;
det_code sel_fun mf a =
  (if Arith.equal_nat (Matrix.dim_row a) (Matrix.dim_col a)
    then (case triangulize sel_fun mf a of {
           (m, aa) ->
             Arith.divide (Groups_List.prod_list (Matrix.diag_mat aa)) m;
         })
    else Arith.zero);

fst_sel_fun :: forall a. [(Arith.Nat, a)] -> Arith.Nat;
fst_sel_fun x = fst (Arith.hda x);

trivial_mute_fun :: forall a. (Arith.Comm_ring_1 a) => a -> a -> (a, (a, a));
trivial_mute_fun x y = (x, (y, Arith.one));

}
