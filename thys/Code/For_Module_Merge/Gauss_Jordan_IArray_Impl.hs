{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Gauss_Jordan_IArray_Impl(mat_swaprows_impl, mat_addrow_gen_impl,
                            mat_multrow_gen_impl)
  where {

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
import qualified Orderings;
import qualified Product_Type;
import qualified List;
import qualified IArraya;
import qualified HOL;
import qualified Matrix_IArray_Impl;
import qualified Arith;

mat_swaprows_impl ::
  forall a.
    Arith.Nat ->
      Arith.Nat ->
        Matrix_IArray_Impl.Mat_impl a -> Matrix_IArray_Impl.Mat_impl a;
mat_swaprows_impl xc xd xe =
  Matrix_IArray_Impl.Abs_mat_impl
    (case Matrix_IArray_Impl.rep_mat_impl xe of {
      (nr, (nc, a)) ->
        (if Arith.less_nat xc nr && Arith.less_nat xd nr
          then let {
                 ai = IArraya.sub a xc;
                 aj = IArraya.sub a xd;
                 arows = IArraya.list_of a;
                 aa = IArray.of_list
                        (List.list_update (List.list_update arows xc aj) xd ai);
               } in (nr, (nc, aa))
          else (nr, (nc, a)));
    });

mat_addrow_gen_impl ::
  forall a.
    (a -> a -> a) ->
      (a -> a -> a) ->
        a -> Arith.Nat ->
               Arith.Nat ->
                 Matrix_IArray_Impl.Mat_impl a -> Matrix_IArray_Impl.Mat_impl a;
mat_addrow_gen_impl xd xe xf xh xi xj =
  Matrix_IArray_Impl.Abs_mat_impl
    (case Matrix_IArray_Impl.rep_mat_impl xj of {
      (nr, (nc, a)) ->
        (if Arith.less_nat xi nr
          then let {
                 ak = IArraya.sub a xh;
                 al = IArraya.sub a xi;
                 aka = IArraya.of_fun
                         (\ i ->
                           xd (xe xf (IArraya.sub al i)) (IArraya.sub ak i))
                         (Orderings.min (IArraya.length ak)
                           (IArraya.length al));
                 aa = IArraya.of_fun
                        (\ i ->
                          (if Arith.equal_nat i xh then aka
                            else IArraya.sub a i))
                        (IArraya.length a);
               } in (nr, (nc, aa))
          else (nr, (nc, a)));
    });

mat_multrow_gen_impl ::
  forall a.
    (a -> a -> a) ->
      Arith.Nat ->
        a -> Matrix_IArray_Impl.Mat_impl a -> Matrix_IArray_Impl.Mat_impl a;
mat_multrow_gen_impl xc xd xe xf =
  Matrix_IArray_Impl.Abs_mat_impl
    (case Matrix_IArray_Impl.rep_mat_impl xf of {
      (nr, (nc, a)) ->
        let {
          ak = IArraya.sub a xd;
          arows = IArraya.list_of a;
          aka = IArray.of_list (map (xc xe) (IArraya.list_of ak));
          aa = IArray.of_list (List.list_update arows xd aka);
        } in (nr, (nc, aa));
    });

}
