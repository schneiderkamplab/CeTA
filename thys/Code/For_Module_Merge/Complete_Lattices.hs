{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Complete_Lattices(sup_set) where {

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
import qualified Finite_Set;
import qualified Collection_Enum;
import qualified Set_Impl;
import qualified Collection_Order;
import qualified Cardinality;
import qualified Collection_Eq;
import qualified Set;

sup_set ::
  forall a.
    (Cardinality.Finite_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a,
      Set_Impl.Set_impl a) => Set.Set (Set.Set a) -> Set.Set a;
sup_set a =
  (if Finite_Set.finite a
    then Set_Impl.set_fold_cfi Set_Impl.sup_cfi Set.bot_set a
    else (error :: forall a. String -> (() -> a) -> a) "Sup: infinite"
           (\ _ -> sup_set a));

}
