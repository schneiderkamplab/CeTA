{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Intf_Comp(Comp_res(..), comp2eq) where {

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

data Comp_res = LESS | EQUAL | GREATER;

comp2eq :: forall a b. (a -> b -> Comp_res) -> a -> b -> Bool;
comp2eq cmp a b = (case cmp a b of {
                    LESS -> False;
                    EQUAL -> True;
                    GREATER -> False;
                  });

}
