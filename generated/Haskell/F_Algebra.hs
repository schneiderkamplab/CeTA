{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module F_Algebra(eval, constant_positions) where {

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

eval ::
  forall a b c. (a -> [b] -> b) -> Term_Rewriting.Term a c -> (c -> b) -> b;
eval i (Term_Rewriting.Var x) alpha = alpha x;
eval i (Term_Rewriting.Fun f ss) alpha = i f (map (\ s -> eval i s alpha) ss);

constant_positions ::
  forall a b.
    (a -> Arith.Nat -> Term_Rewriting.Term b Arith.Nat) ->
      a -> Arith.Nat -> [Arith.Nat];
constant_positions e f n =
  filter (\ i -> not (Term_Rewriting.contains_var_term i (e f n)))
    (Arith.upt Arith.zero_nat n);

}
