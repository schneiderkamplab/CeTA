{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Generalized_Usable_Rules(Cond_constraint(..), equal_cond_constraint,
                            Condition_type(..), compat_root, constraint_of,
                            disjoint_variant)
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
import qualified Missing_List;
import qualified Trs;
import qualified HOL;
import qualified Set;
import qualified Mapping_Impl;
import qualified Cardinality;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Collection_Order;
import qualified List;
import qualified Arith;
import qualified Term;

data Cond_constraint a b = CC_cond Bool (Term.Term a b, Term.Term a b)
  | CC_rewr (Term.Term a b) (Term.Term a b)
  | CC_impl [Cond_constraint a b] (Cond_constraint a b)
  | CC_all b (Cond_constraint a b);

instance (Eq a, Eq b) => Eq (Cond_constraint a b) where {
  a == b = equal_cond_constraint a b;
};

equal_cond_constraint ::
  forall a b.
    (Eq a, Eq b) => Cond_constraint a b -> Cond_constraint a b -> Bool;
equal_cond_constraint (CC_impl x31 x32) (CC_all x41 x42) = False;
equal_cond_constraint (CC_all x41 x42) (CC_impl x31 x32) = False;
equal_cond_constraint (CC_rewr x21 x22) (CC_all x41 x42) = False;
equal_cond_constraint (CC_all x41 x42) (CC_rewr x21 x22) = False;
equal_cond_constraint (CC_rewr x21 x22) (CC_impl x31 x32) = False;
equal_cond_constraint (CC_impl x31 x32) (CC_rewr x21 x22) = False;
equal_cond_constraint (CC_cond x11 x12) (CC_all x41 x42) = False;
equal_cond_constraint (CC_all x41 x42) (CC_cond x11 x12) = False;
equal_cond_constraint (CC_cond x11 x12) (CC_impl x31 x32) = False;
equal_cond_constraint (CC_impl x31 x32) (CC_cond x11 x12) = False;
equal_cond_constraint (CC_cond x11 x12) (CC_rewr x21 x22) = False;
equal_cond_constraint (CC_rewr x21 x22) (CC_cond x11 x12) = False;
equal_cond_constraint (CC_all x41 x42) (CC_all y41 y42) =
  x41 == y41 && equal_cond_constraint x42 y42;
equal_cond_constraint (CC_impl x31 x32) (CC_impl y31 y32) =
  x31 == y31 && equal_cond_constraint x32 y32;
equal_cond_constraint (CC_rewr x21 x22) (CC_rewr y21 y22) =
  Term.equal_term x21 y21 && Term.equal_term x22 y22;
equal_cond_constraint (CC_cond x11 x12) (CC_cond y11 y12) =
  x11 == y11 && x12 == y12;

data Condition_type = Bound | Strict | Non_Strict;

compat_root :: forall a b c. (Eq a) => Term.Term a b -> Term.Term a c -> Bool;
compat_root uu (Term.Var uv) = False;
compat_root (Term.Var uw) (Term.Fun v va) = False;
compat_root (Term.Fun vb vc) (Term.Fun v va) =
  Term.root (Term.Fun vb vc) == Term.root (Term.Fun v va);

condition_of ::
  forall a b.
    a -> Condition_type ->
           (Term.Term a b, Term.Term a b) -> Cond_constraint a b;
condition_of c Bound (s, uu) = CC_cond False (s, Term.Fun c []);
condition_of c Strict st = CC_cond True st;
condition_of c Non_Strict st = CC_cond False st;

constraint_of ::
  forall a b.
    a -> Condition_type ->
           [(Term.Term a b, Term.Term a b)] -> Arith.Nat -> Cond_constraint a b;
constraint_of c ctype uvs bef =
  CC_impl
    (map (\ i ->
           CC_rewr (snd (List.nth uvs i)) (fst (List.nth uvs (Arith.suc i))))
      (List.upt Arith.zero_nat
        (Arith.minus_nat (List.size_list uvs) Arith.one_nat)))
    (condition_of c ctype (List.nth uvs bef));

disjoint_variant ::
  forall a b.
    (Eq a, Cardinality.Card_UNIV b, Collection_Eq.Ceq b,
      Collection_Order.Cproper_interval b, Eq b, Mapping_Impl.Mapping_impl b,
      Set_Impl.Set_impl b) => [(Term.Term a b, Term.Term a b)] ->
                                [(Term.Term a b, Term.Term a b)] -> Bool;
disjoint_variant sts uvs =
  Arith.equal_nat (List.size_list sts) (List.size_list uvs) &&
    let {
      d = Arith.minus_nat (List.size_list sts) Arith.one_nat;
    } in (if Arith.less_nat d (List.size_list sts)
           then List.all_interval
                  (\ i ->
                    Trs.eq_rule_mod_vars (List.nth sts i) (List.nth uvs i))
                  Arith.zero_nat d
           else True) &&
      Missing_List.is_partition (map Trs.vars_rule uvs);

}
