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
import qualified Set;
import qualified Collection_Order;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Product_Type;
import qualified List;
import qualified Term;
import qualified Arith;

proja :: forall a b. Term.Term a b -> Arith.Nat -> Term.Term a b;
proja (Term.Fun f ts) i =
  (if Arith.less_nat i (List.size_list ts) then List.nth ts i
    else Term.Fun f ts);

lterms ::
  forall a b.
    ((a, Arith.Nat) -> [(Arith.Nat, Arith.Nat)]) ->
      Term.Term a b -> [(Term.Term a b, Arith.Nat)];
lterms pi =
  (\ (Term.Fun f ts) ->
    map (\ (i, a) -> (proja (Term.Fun f ts) i, a)) (pi (f, List.size_list ts)));

scnp_af_to_af ::
  forall a.
    ((a, Arith.Nat) -> [(Arith.Nat, Arith.Nat)]) ->
      ((a, Arith.Nat) -> Set.Set Arith.Nat) ->
        (a, Arith.Nat) -> Set.Set Arith.Nat;
scnp_af_to_af pia pi =
  (\ (f, n) ->
    let {
      is = map fst (pia (f, n));
    } in (if any (Arith.less_eq_nat n) is
           then Set.sup_set (pi (f, n)) (List.set is) else List.set is));

}
