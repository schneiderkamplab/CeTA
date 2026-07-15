{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Term(Term(..), equal_term, root, subst, ground, eval_term, args, eval_subst,
        is_Var, the_Var, vars_term_ms, map_term, rec_term, vars_term)
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
import qualified Term_More;
import qualified Set;
import qualified Collection_Order;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Multiset;
import qualified Fun;
import qualified List;
import qualified Arith;

data Term a b = Var b | Fun a [Term a b];

instance (Eq a, Eq b) => Eq (Term a b) where {
  a == b = equal_term a b;
};

equal_term :: forall a b. (Eq a, Eq b) => Term a b -> Term a b -> Bool;
equal_term (Var x1) (Fun x21 x22) = False;
equal_term (Fun x21 x22) (Var x1) = False;
equal_term (Fun x21 x22) (Fun y21 y22) = x21 == y21 && x22 == y22;
equal_term (Var x1) (Var y1) = x1 == y1;

root :: forall a b. Term a b -> Maybe (a, Arith.Nat);
root (Var x) = Nothing;
root (Fun f ts) = Just (f, List.size_list ts);

subst :: forall a b. (Eq a) => a -> Term b a -> a -> Term b a;
subst x t = Fun.fun_upd Var x t;

ground :: forall a b. Term a b -> Bool;
ground (Var x) = False;
ground (Fun f ts) = all ground ts;

eval_term :: forall a b c. (a -> [b] -> b) -> Term a c -> (c -> b) -> b;
eval_term i (Var x) alpha = alpha x;
eval_term i (Fun f ss) alpha = i f (map (\ s -> eval_term i s alpha) ss);

args :: forall a b. Term a b -> [Term a b];
args (Var x1) = [];
args (Fun x21 x22) = x22;

eval_subst ::
  forall a b c d. (a -> [b] -> b) -> (c -> Term a d) -> (d -> b) -> c -> b;
eval_subst i theta alpha = (\ x -> eval_term i (theta x) alpha);

is_Var :: forall a b. Term a b -> Bool;
is_Var (Var x1) = True;
is_Var (Fun x21 x22) = False;

the_Var :: forall a b. Term a b -> b;
the_Var (Var x1) = x1;

vars_term_ms :: forall a b. (Eq b) => Term a b -> Multiset.Multiset b;
vars_term_ms (Var x) = Multiset.add_mset x Multiset.zero_multiset;
vars_term_ms (Fun f ts) =
  Multiset.sum_mset (Multiset.mset (map vars_term_ms ts));

map_term :: forall a b c d. (a -> b) -> (c -> d) -> Term a c -> Term b d;
map_term f1 f2 (Var x1) = Var (f2 x1);
map_term f1 f2 (Fun x21 x22) = Fun (f1 x21) (map (map_term f1 f2) x22);

rec_term ::
  forall a b c. (a -> b) -> (c -> [(Term c a, b)] -> b) -> Term c a -> b;
rec_term f1 f2 (Var x1) = f1 x1;
rec_term f1 f2 (Fun x21 x22) =
  f2 x21 (map (\ term -> (term, rec_term f1 f2 term)) x22);

vars_term ::
  forall a b.
    (Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Set_Impl.Set_impl b) => Term a b -> Set.Set b;
vars_term t = List.set (Term_More.vars_term_list t);

}
