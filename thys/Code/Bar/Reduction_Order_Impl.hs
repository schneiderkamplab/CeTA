{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Reduction_Order_Impl(Redord_ext(..), less, valid, min_const) where {

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
import qualified Sum_Type;
import qualified Term_Rewriting;

data Redord_ext a b c =
  Redord_ext (Sum_Type.Sum (String -> String) ())
    (Term_Rewriting.Term a b -> Term_Rewriting.Term a b -> Bool) a c;

less ::
  forall a b c.
    Redord_ext a b c ->
      Term_Rewriting.Term a b -> Term_Rewriting.Term a b -> Bool;
less (Redord_ext valid less min_const more) = less;

valid :: forall a b c. Redord_ext a b c -> Sum_Type.Sum (String -> String) ();
valid (Redord_ext valid less min_const more) = valid;

min_const :: forall a b c. Redord_ext a b c -> a;
min_const (Redord_ext valid less min_const more) = min_const;

}
