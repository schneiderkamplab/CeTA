{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Matchbounds(Relation_kind(..), base, lift, roof, match, height, roots_of_cm,
               sym_collect, compute_height, stackable_of_cm)
  where {

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
import qualified Quasi_Order;
import qualified Multiset;
import qualified Complexity;
import qualified HOL;
import qualified Term_Rewriting;
import qualified Arith;

data Relation_kind = Strict_TRS | Weak_TRS (Maybe Arith.Nat);

base :: forall a. (a, Arith.Nat) -> a;
base (f, h) = f;

lift :: forall a. Arith.Nat -> a -> (a, Arith.Nat);
lift h f = (f, h);

roof ::
  forall a b.
    (Arith.Ceq b, Arith.Ccompare b,
      Arith.Set_impl b) => (Term_Rewriting.Term a b, Term_Rewriting.Term a b) ->
                             Term_Rewriting.Term a b -> Bool;
roof (l, r) = let {
                xs = Term_Rewriting.vars_term_list r;
              } in (\ t -> let {
                             xt = Term_Rewriting.vars_term t;
                           } in all (\ x -> Arith.member x xt) xs);

match ::
  forall a b.
    (Term_Rewriting.Term a b, Term_Rewriting.Term a b) ->
      Term_Rewriting.Term a b -> Bool;
match = (\ _ _ -> True);

height :: forall a. (a, Arith.Nat) -> Arith.Nat;
height (f, h) = h;

roots_of_cm ::
  forall a b. Complexity.Complexity_measure a b -> [(a, Arith.Nat)];
roots_of_cm (Complexity.Derivational_Complexity f) = f;
roots_of_cm (Complexity.Runtime_Complexity c d) = d;

sym_collect ::
  forall a b.
    (Term_Rewriting.Term a b -> Bool) -> Term_Rewriting.Term a b -> [a];
sym_collect p (Term_Rewriting.Var x) = [];
sym_collect p (Term_Rewriting.Fun f ts) =
  (if p (Term_Rewriting.Fun f ts) then [f] else []) ++
    concatMap (sym_collect p) ts;

compute_height ::
  forall a b.
    (Eq a,
      Eq b) => Relation_kind ->
                 Term_Rewriting.Term a b ->
                   Term_Rewriting.Term a b ->
                     Term_Rewriting.Term (a, Arith.Nat) b ->
                       Arith.Nat -> Arith.Nat;
compute_height Strict_TRS bl br = (\ _ -> Arith.suc);
compute_height (Weak_TRS (Just c)) bl br =
  (if Arith.less_eq_nat
        (Multiset.size_multiset (Term_Rewriting.funs_term_ms br))
        (Multiset.size_multiset (Term_Rewriting.funs_term_ms bl))
    then (\ l x ->
           (if Term_Rewriting.equal_term
                 (Term_Rewriting.map_term (lift x) (\ xa -> xa) bl) l
             then Quasi_Order.min c x else Quasi_Order.min c (Arith.suc x)))
    else (\ _ x -> Quasi_Order.min c (Arith.suc x)));
compute_height (Weak_TRS Nothing) bl br =
  (if Arith.less_eq_nat
        (Multiset.size_multiset (Term_Rewriting.funs_term_ms br))
        (Multiset.size_multiset (Term_Rewriting.funs_term_ms bl))
    then (\ l x ->
           (if Term_Rewriting.equal_term
                 (Term_Rewriting.map_term (lift x) (\ xa -> xa) bl) l
             then x else Arith.suc x))
    else (\ _ -> Arith.suc));

stackable_of_cm ::
  forall a b. Complexity.Complexity_measure a b -> [(a, Arith.Nat)];
stackable_of_cm (Complexity.Derivational_Complexity f) = f;
stackable_of_cm (Complexity.Runtime_Complexity c d) = c;

}
