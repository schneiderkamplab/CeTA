{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Nonloop_SRS(term_to_string, word_pat_equiv) where {

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
import qualified Nonloop_SRS_Impl;
import qualified Arith;
import qualified Term;

term_to_string :: forall a b. Term.Term a b -> [a];
term_to_string (Term.Fun f [t]) = f : term_to_string t;
term_to_string (Term.Var v) = [];
term_to_string (Term.Fun v []) = [];
term_to_string (Term.Fun v (vb : vd : ve)) = [];

word_pat_equiv ::
  forall a.
    (Eq a) => ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])) ->
                ([a], ((Arith.Nat, (Arith.Nat, [a])), [a])) -> Bool;
word_pat_equiv wp1 wp2 =
  wp1 == wp2 ||
    Nonloop_SRS_Impl.normalize_wp wp1 == Nonloop_SRS_Impl.normalize_wp wp2;

}
