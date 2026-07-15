{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Show_Real() where {

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
import qualified Arith;
import qualified Term_Rewriting;

show_real :: Term_Rewriting.Real -> [Arith.Char];
show_real (Term_Rewriting.Real_of_u x) = Term_Rewriting.mau_show_real x;

showsl_real :: Term_Rewriting.Real -> String -> String;
showsl_real x = Term_Rewriting.showsl_lit (Arith.implode (show_real x));

showsl_list_real :: [Term_Rewriting.Real] -> String -> String;
showsl_list_real xs = Term_Rewriting.default_showsl_list showsl_real xs;

instance Term_Rewriting.Showl Term_Rewriting.Real where {
  showsl = showsl_real;
  showsl_list = showsl_list_real;
};

}
