{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module SCNP(lterms, scnp_af_to_af) where {

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

proja ::
  forall a b. Term_Rewriting.Term a b -> Arith.Nat -> Term_Rewriting.Term a b;
proja (Term_Rewriting.Fun f ts) i =
  (if Arith.less_nat i (Arith.size_list ts) then Arith.nth ts i
    else Term_Rewriting.Fun f ts);

lterms ::
  forall a b.
    ((a, Arith.Nat) -> [(Arith.Nat, Arith.Nat)]) ->
      Term_Rewriting.Term a b -> [(Term_Rewriting.Term a b, Arith.Nat)];
lterms pi =
  (\ (Term_Rewriting.Fun f ts) ->
    map (\ (i, a) -> (proja (Term_Rewriting.Fun f ts) i, a))
      (pi (f, Arith.size_list ts)));

scnp_af_to_af ::
  forall a.
    ((a, Arith.Nat) -> [(Arith.Nat, Arith.Nat)]) ->
      ((a, Arith.Nat) -> Arith.Set Arith.Nat) ->
        (a, Arith.Nat) -> Arith.Set Arith.Nat;
scnp_af_to_af pia pi =
  (\ (f, n) ->
    let {
      is = map fst (pia (f, n));
    } in (if any (Arith.less_eq_nat n) is
           then Arith.sup_set (pi (f, n)) (Arith.set is) else Arith.set is));

}
