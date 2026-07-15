{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Mgu_List(mgu_list) where {

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
import qualified Option;
import qualified Unification;
import qualified Term;

mgu_list ::
  forall a b.
    (Eq a,
      Eq b) => [(Term.Term a b, Term.Term a b)] -> Maybe (b -> Term.Term a b);
mgu_list pairs =
  Option.map_option Unification.subst_of (Unification.unify pairs []);

}
