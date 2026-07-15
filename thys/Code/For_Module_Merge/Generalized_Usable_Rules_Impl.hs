{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Generalized_Usable_Rules_Impl(usable_rules_gen) where {

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
import qualified Generalized_Usable_Rules;
import qualified HOL;
import qualified Product_Type;
import qualified RTrancl;
import qualified List;
import qualified Non_Inf_Order;
import qualified Term;
import qualified Arith;

compat_root ::
  forall a b. (Eq a) => Term.Term a b -> Maybe (a, Arith.Nat) -> Bool;
compat_root uu Nothing = False;
compat_root (Term.Var uv) (Just v) = False;
compat_root (Term.Fun va vb) (Just v) = Term.root (Term.Fun va vb) == Just v;

rel_dep_prod :: Bool -> Non_Inf_Order.Dependance -> [Bool];
rel_dep_prod uu Non_Inf_Order.Ignore = [];
rel_dep_prod b Non_Inf_Order.Increase = [b];
rel_dep_prod b Non_Inf_Order.Decrease = [not b];
rel_dep_prod uv Non_Inf_Order.Wild = [True, False];

usable_rules_gen2 ::
  forall a b.
    (Eq a) => [(Term.Term a b, Term.Term a b)] ->
                (Maybe (a, Arith.Nat), Bool) ->
                  [(Term.Term a b, Term.Term a b)];
usable_rules_gen2 r (fn, b) =
  let {
    rr = concatMap (\ (l, ra) -> (if compat_root l fn then [(l, ra)] else []))
           r;
  } in (if b then rr else map (\ (l, ra) -> (ra, l)) rr);

usable_rules_gen1 ::
  forall a b.
    (Eq a) => ((a, Arith.Nat) -> Arith.Nat -> Non_Inf_Order.Dependance) ->
                [(Term.Term a b, Term.Term a b)] ->
                  (Term.Term a b, Bool) -> [(Term.Term a b, Bool)];
usable_rules_gen1 pi r (Term.Var uu, uv) = [];
usable_rules_gen1 pi r (Term.Fun f ts, b) =
  let {
    n = List.size_list ts;
  } in concatMap
         (\ (l, ra) ->
           (if Generalized_Usable_Rules.compat_root l (Term.Fun f ts)
             then [(ra, b)] else []))
         r ++
         concatMap
           (\ i ->
             map (\ a -> (List.nth ts i, a)) (rel_dep_prod b (pi (f, n) i)))
           (List.upt Arith.zero_nat n);

usable_rules_gen ::
  forall a b.
    (Eq a,
      Eq b) => ((a, Arith.Nat) -> Arith.Nat -> Non_Inf_Order.Dependance) ->
                 [(Term.Term a b, Term.Term a b)] ->
                   [(Term.Term a b, Term.Term a b)] ->
                     [(Term.Term a b, Term.Term a b)];
usable_rules_gen pi r p =
  concatMap (usable_rules_gen2 r)
    (List.remdups
      (map (\ (t, a) -> (Term.root t, a))
        (RTrancl.mk_rtrancl_list (\ a b -> a == b) (usable_rules_gen1 pi r)
          (map (\ (_, t) -> (t, True)) p))));

}
