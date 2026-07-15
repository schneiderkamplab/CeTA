{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Forbidden_Patterns(Location(..), equal_location, showsl_location) where {

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
import qualified Shows_Literal;

data Location = H | A | B | R;

equal_location :: Location -> Location -> Bool;
equal_location B R = False;
equal_location R B = False;
equal_location A R = False;
equal_location R A = False;
equal_location A B = False;
equal_location B A = False;
equal_location H R = False;
equal_location R H = False;
equal_location H B = False;
equal_location B H = False;
equal_location H A = False;
equal_location A H = False;
equal_location R R = True;
equal_location B B = True;
equal_location A A = True;
equal_location H H = True;

instance Eq Location where {
  a == b = equal_location a b;
};

showsl_location :: Location -> String -> String;
showsl_location A = Shows_Literal.showsl_lit "above";
showsl_location B = Shows_Literal.showsl_lit "below";
showsl_location H = Shows_Literal.showsl_lit "here";
showsl_location R = Shows_Literal.showsl_lit "right";

}
