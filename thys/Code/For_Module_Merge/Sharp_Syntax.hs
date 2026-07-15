{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Sharp_Syntax(sharp_term) where {

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
import qualified Term;

sharp_term :: forall a b. (a -> a) -> Term.Term a b -> Term.Term a b;
sharp_term shp (Term.Var x) = Term.Var x;
sharp_term shp (Term.Fun f ss) = Term.Fun (shp f) ss;

}
