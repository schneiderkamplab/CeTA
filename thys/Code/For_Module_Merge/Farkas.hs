{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Farkas(Le_rel(..), Le_constraint(..), lec_poly) where {

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
import qualified Abstract_Linear_Poly;

data Le_rel = Leq_Rel | Lt_Rel;

data Le_constraint a = Le_Constraint Le_rel Abstract_Linear_Poly.Linear_poly a;

lec_poly :: forall a. Le_constraint a -> Abstract_Linear_Poly.Linear_poly;
lec_poly (Le_Constraint x1 x2 x3) = x2;

}
