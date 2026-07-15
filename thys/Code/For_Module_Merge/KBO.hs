{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module KBO(scf_term, weight) where {

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
import qualified Groups_List;
import qualified HOL;
import qualified Term;
import qualified Product_Type;
import qualified List;
import qualified Arith;

scf_list :: forall a. (Arith.Nat -> Arith.Nat) -> [a] -> [a];
scf_list scf xs =
  concatMap (\ (x, i) -> List.replicate (scf i) x)
    (zip xs (List.upt Arith.zero_nat (List.size_list xs)));

scf_term ::
  forall a b.
    ((a, Arith.Nat) -> Arith.Nat -> Arith.Nat) ->
      Term.Term a b -> Term.Term a b;
scf_term scf (Term.Var x) = Term.Var x;
scf_term scf (Term.Fun f ts) =
  Term.Fun f (scf_list (scf (f, List.size_list ts)) (map (scf_term scf) ts));

weight ::
  forall a b.
    ((a, Arith.Nat) -> Arith.Nat) ->
      Arith.Nat ->
        ((a, Arith.Nat) -> Arith.Nat -> Arith.Nat) ->
          Term.Term a b -> Arith.Nat;
weight w w0 scf (Term.Var x) = w0;
weight w w0 scf (Term.Fun f ts) =
  let {
    n = List.size_list ts;
    scff = scf (f, n);
  } in Arith.plus_nat (w (f, n))
         (Groups_List.sum_list
           (map (\ (ti, i) -> Arith.times_nat (weight w w0 scf ti) (scff i))
             (zip ts (List.upt Arith.zero_nat n))));

}
