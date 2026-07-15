{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Monadic_Rewriting(str) where {

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
import qualified Term_Rewriting;

str ::
  forall a b.
    (a -> a) -> b -> Term_Rewriting.Term a b -> Term_Rewriting.Term a b;
str d uu (Term_Rewriting.Var x) = Term_Rewriting.Var x;
str d x (Term_Rewriting.Fun f [t]) = Term_Rewriting.Fun f [str d x t];
str d x (Term_Rewriting.Fun f []) =
  Term_Rewriting.Fun (d f) [Term_Rewriting.Var x];
str d x (Term_Rewriting.Fun f (v : vb : vc)) =
  Term_Rewriting.Fun (d f) [Term_Rewriting.Var x];

}
