{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Subterm_Criterion(proj_term) where {

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
import qualified HOL;
import qualified Term_Rewriting;
import qualified Arith;

proj_term ::
  forall a b.
    ((a, Arith.Nat) -> Arith.Nat) ->
      Term_Rewriting.Term a b -> Term_Rewriting.Term a b;
proj_term p (Term_Rewriting.Var x) = Term_Rewriting.Var x;
proj_term p (Term_Rewriting.Fun f ts) =
  let {
    n = Arith.size_list ts;
    i = p (f, n);
  } in (if Arith.less_nat i n then Arith.nth ts i else Term_Rewriting.Fun f ts);

}
