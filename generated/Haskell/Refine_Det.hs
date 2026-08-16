{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Refine_Det(Dres(..), dbind, dWHILET) where {

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

data Dres a = DSUCCEEDi | DFAILi | DRETURN a;

dbind :: forall a b. Dres a -> (a -> Dres b) -> Dres b;
dbind (DRETURN x) f = f x;
dbind DSUCCEEDi f = DSUCCEEDi;
dbind DFAILi f = DFAILi;

dWHILET :: forall a. (a -> Bool) -> (a -> Dres a) -> a -> Dres a;
dWHILET b f s = (if b s then dbind (f s) (dWHILET b f) else DRETURN s);

}
