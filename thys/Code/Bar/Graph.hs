{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Graph(check_graph_decomp) where {

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
import qualified Shows_Literal;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Sum_Type;

check_no_edge ::
  forall a.
    (a -> String -> String) ->
      ((a, a) -> Bool) -> a -> a -> Sum_Type.Sum (String -> String) ();
check_no_edge ss g m n =
  Check_Monad.check (not (g (m, n)))
    (((Shows_Literal.showsl_lit "edge from " . ss m) .
       Shows_Literal.showsl_lit " to ") .
      ss n);

check_edges ::
  forall a.
    (a -> String -> String) ->
      ((a, a) -> Bool) -> [a] -> [a] -> Sum_Type.Sum (String -> String) ();
check_edges ss g c d =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ n ->
        Error_Monad.catch_error (Error_Monad.forallM (check_no_edge ss g n) d)
          (\ x -> Sum_Type.Inl (snd x)))
      c)
    (\ x -> Sum_Type.Inl (snd x));

check_no_back_edges ::
  forall a b.
    (a -> String -> String) ->
      (b -> a -> [a]) ->
        (a -> b -> b) ->
          ((a, a) -> Bool) -> b -> [[a]] -> Sum_Type.Sum (String -> String) ();
check_no_back_edges ss candidates add_index g i [] = Sum_Type.Inr ();
check_no_back_edges ss candidates add_index g i (asa : cs) =
  Error_Monad.bind
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ a ->
          Error_Monad.catch_error
            (Error_Monad.forallM (check_no_edge ss g a) (candidates i a))
            (\ x -> Sum_Type.Inl (snd x)))
        asa)
      (\ x -> Sum_Type.Inl (snd x)))
    (\ _ ->
      check_no_back_edges ss candidates add_index g
        (Arith.foldr add_index asa i) cs);

check_graph_decomp ::
  forall a b.
    (a -> String -> String) ->
      b -> (b -> a -> [a]) ->
             (a -> b -> b) ->
               ((a, a) -> Bool) ->
                 [(Bool, [a])] -> Sum_Type.Sum (String -> String) ();
check_graph_decomp ss empty_index candidates add_index g rcs =
  Error_Monad.bind
    (check_no_back_edges ss candidates add_index g empty_index (map snd rcs))
    (\ _ ->
      Error_Monad.catch_error
        (Error_Monad.forallM (\ c -> check_edges ss g c c)
          (Arith.map_filter
            (\ x -> (if not (fst x) then Just (snd x) else Nothing)) rcs))
        (\ x -> Sum_Type.Inl (snd x)));

}
