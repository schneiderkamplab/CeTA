{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Set(Set, member) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;
import qualified List;

data Set a = Set [a] | Coset [a];

member :: forall a. (Eq a) => a -> Set a -> Bool;
member x (Set xs) = List.member xs x;
member x (Coset xs) = not (List.member xs x);

}
