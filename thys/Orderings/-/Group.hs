{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Group(Monoid_ext(..), mult) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;
import qualified Congruence;
import qualified Set;

data Monoid_ext a b = Monoid_ext (a -> a -> a) a b;

mult ::
  forall a b. Congruence.Partial_object_ext a (Monoid_ext a b) -> a -> a -> a;
mult (Congruence.Partial_object_ext carrier (Monoid_ext mult one more)) = mult;

}
