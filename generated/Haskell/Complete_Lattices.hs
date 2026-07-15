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
import qualified Arith;

sup_set ::
  forall a.
    (Arith.Finite_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Arith.Set_impl a) => Arith.Set (Arith.Set a) -> Arith.Set a;
sup_set a =
  (if Arith.finite a then Arith.set_fold_cfi Arith.sup_cfi Arith.bot_set a
    else (error :: forall a. String -> (() -> a) -> a) "Sup: infinite"
           (\ _ -> sup_set a));

}
