{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Check_Monad(check, or_ok, check_disjoint, check_pairwise, check_subseteq,
               check_same_set)
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
import qualified Error_Monad;
import qualified List;
import qualified Sum_Type;

check :: forall a. Bool -> a -> Sum_Type.Sum a ();
check b e = (if b then Sum_Type.Inr () else Sum_Type.Inl e);

or_ok :: forall a. Sum_Type.Sum a () -> Sum_Type.Sum a () -> Sum_Type.Sum a ();
or_ok (Sum_Type.Inl a) b = b;
or_ok (Sum_Type.Inr a) b = Sum_Type.Inr a;

check_disjoint :: forall a. (Eq a) => [a] -> [a] -> Sum_Type.Sum a ();
check_disjoint xs ys =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ x ->
        (if not (List.member ys x) then Sum_Type.Inr () else Sum_Type.Inl x))
      xs)
    (\ x -> Sum_Type.Inl (snd x));

check_pairwise ::
  forall a b. (a -> a -> Sum_Type.Sum b ()) -> [a] -> Sum_Type.Sum b ();
check_pairwise c [] = Sum_Type.Inr ();
check_pairwise c (x : xs) =
  Error_Monad.bind
    (Error_Monad.catch_error (Error_Monad.forallM (c x) xs)
      (\ xa -> Sum_Type.Inl (snd xa)))
    (\ _ -> check_pairwise c xs);

check_subseteq :: forall a. (Eq a) => [a] -> [a] -> Sum_Type.Sum a ();
check_subseteq xs ys =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ x -> (if List.member ys x then Sum_Type.Inr () else Sum_Type.Inl x))
      xs)
    (\ x -> Sum_Type.Inl (snd x));

check_same_set :: forall a. (Eq a) => [a] -> [a] -> Sum_Type.Sum a ();
check_same_set xs ys =
  Error_Monad.bind (check_subseteq xs ys) (\ _ -> check_subseteq ys xs);

}
