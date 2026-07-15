{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Ring(Ring_ext(..), add, zero) where {

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
import qualified Congruence;
import qualified Group;
import qualified Set;

data Ring_ext a b = Ring_ext a (a -> a -> a) b;

add ::
  forall a b.
    Congruence.Partial_object_ext a (Group.Monoid_ext a (Ring_ext a b)) ->
      a -> a -> a;
add (Congruence.Partial_object_ext carrier
      (Group.Monoid_ext mult one (Ring_ext zero add more)))
  = add;

zero ::
  forall a b.
    Congruence.Partial_object_ext a (Group.Monoid_ext a (Ring_ext a b)) -> a;
zero (Congruence.Partial_object_ext carrier
       (Group.Monoid_ext mult one (Ring_ext zero add more)))
  = zero;

}
