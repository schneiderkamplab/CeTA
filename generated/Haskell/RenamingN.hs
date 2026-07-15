{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module RenamingN(RenamingN(..), rep_renamingN, rename_many, rename_single)
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
import qualified Arith;
import qualified Fresh;

newtype RenamingN a = Abs_renamingN ((Arith.Nat, a) -> a, a -> a);

rep_renamingN ::
  forall a. (Fresh.Infinite a) => RenamingN a -> ((Arith.Nat, a) -> a, a -> a);
rep_renamingN (Abs_renamingN x) = x;

rename_many ::
  forall a. (Fresh.Infinite a) => RenamingN a -> (Arith.Nat, a) -> a;
rename_many xa = fst (rep_renamingN xa);

rename_single :: forall a. (Fresh.Infinite a) => RenamingN a -> a -> a;
rename_single xa = snd (rep_renamingN xa);

}
