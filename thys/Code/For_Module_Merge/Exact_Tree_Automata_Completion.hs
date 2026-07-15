{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Exact_Tree_Automata_Completion(star, growing, funas_ta, map_r_states,
                                  reachable_states, ground_instances_ta)
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
import qualified Phantom_Type;
import qualified HOL;
import qualified Sum_Type;
import qualified Term_More;
import qualified Product_Type;
import qualified List;
import qualified Complete_Lattices;
import qualified Tree_Automata;
import qualified Arith;
import qualified Cardinality;
import qualified Collection_Enum;
import qualified Set;
import qualified Set_Impl;
import qualified Compare;
import qualified Collection_Order;
import qualified Collection_Eq;
import qualified Container_Setup;
import qualified Term;

star :: forall a b. a -> Term.Term a b -> Term.Term a b;
star c (Term.Var x) = Term.Fun c [];
star c (Term.Fun f ts) = Term.Fun f (map (star c) ts);

growing_rule ::
  forall a b.
    (Eq a, Collection_Eq.Ceq b, Collection_Order.Ccompare b, Eq b,
      Set_Impl.Set_impl b) => (Term.Term a b, Term.Term a b) -> Bool;
growing_rule (l, r) =
  Set.ball (Term.vars_term r)
    (\ x ->
      Set.ball (Term_More.var_poss l)
        (\ p ->
          (if Term.equal_term (Term.Var x) (Term_More.subt_at l p)
            then Arith.less_eq_nat (List.size_list p) Arith.one_nat
            else True)));

growing ::
  forall a b.
    (Compare.Compare a, Eq a, Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Compare.Compare b, Eq b,
      Set_Impl.Set_impl b) => Set.Set (Term.Term a b, Term.Term a b) -> Bool;
growing r = Set.ball r growing_rule;

funas_ta_rule ::
  forall a b.
    (Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Set_Impl.Set_impl b) => Tree_Automata.Ta_rule a b ->
                                Set.Set (b, Arith.Nat);
funas_ta_rule r =
  Set.insert
    (Tree_Automata.r_root r, List.size_list (Tree_Automata.r_lhs_states r))
    Set.bot_set;

funas_ta ::
  forall a b.
    (Collection_Order.Ccompare a, Eq a, Cardinality.Finite_UNIV b,
      Collection_Enum.Cenum b, Collection_Eq.Ceq b,
      Collection_Order.Cproper_interval b, Eq b,
      Set_Impl.Set_impl b) => Tree_Automata.Ta_ext a b () ->
                                Set.Set (b, Arith.Nat);
funas_ta a =
  Complete_Lattices.sup_set
    (Set.image funas_ta_rule (Tree_Automata.ta_rules a));

sig_rules ::
  forall a b.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Eq a,
      Collection_Order.Ccompare b,
      Eq b) => Set.Set (a, Arith.Nat) ->
                 b -> Set.Set (Tree_Automata.Ta_rule b a);
sig_rules f c =
  Set.image (\ (fa, n) -> Tree_Automata.TA_rule fa (List.replicate n c) c) f;

map_r_states ::
  forall a b c.
    (a -> b) -> Tree_Automata.Ta_rule a c -> Tree_Automata.Ta_rule b c;
map_r_states f r =
  Tree_Automata.TA_rule (Tree_Automata.r_root r)
    (map f (Tree_Automata.r_lhs_states r)) (f (Tree_Automata.r_rhs r));

reachable_states ::
  forall a b c.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Eq a,
      Set_Impl.Set_impl a, Collection_Order.Ccompare b,
      Eq b) => Set.Set (Tree_Automata.Ta_rule a b) ->
                 Term.Term (Sum_Type.Sum b a) c -> Set.Set a;
reachable_states delta (Term.Fun (Sum_Type.Inr q) []) =
  Set.insert q Set.bot_set;
reachable_states delta (Term.Fun (Sum_Type.Inl f) ts) =
  Set.image Tree_Automata.r_rhs
    (Set.filtera
      (\ r ->
        Tree_Automata.r_root r == f &&
          Arith.equal_nat (List.size_list (Tree_Automata.r_lhs_states r))
            (List.size_list ts) &&
            let {
              d = Arith.minus_nat (List.size_list ts) Arith.one_nat;
            } in (if Arith.less_nat d (List.size_list ts)
                   then List.all_interval
                          (\ i ->
                            Set.member
                              (List.nth (Tree_Automata.r_lhs_states r) i)
                              (reachable_states delta (List.nth ts i)))
                          Arith.zero_nat d
                   else True))
      delta);
reachable_states delta (Term.Var v) = Set.bot_set;
reachable_states delta (Term.Fun (Sum_Type.Inr va) (vb : vc)) = Set.bot_set;

ground_instances_rules ::
  forall a b.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Compare.Compare a, Eq a,
      Compare.Compare b,
      Eq b) => Set.Set (a, Arith.Nat) ->
                 a -> Term.Term a b ->
                        Set.Set (Tree_Automata.Ta_rule (Term.Term a b) a);
ground_instances_rules f c (Term.Var x) = sig_rules f (Term.Fun c []);
ground_instances_rules fa c (Term.Fun f ts) =
  Set.sup_set
    (Set.insert
      (Tree_Automata.TA_rule f (map (star c) ts) (star c (Term.Fun f ts)))
      (Set_Impl.set_empty
        (Phantom_Type.of_phantom Container_Setup.set_impl_ta_rule)))
    (Complete_Lattices.sup_set
      (Set.image (ground_instances_rules fa c) (List.set ts)));

ground_instances_ta ::
  forall a b.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Compare.Compare a, Eq a,
      Compare.Compare b,
      Eq b) => Set.Set (a, Arith.Nat) ->
                 a -> Term.Term a b ->
                        Tree_Automata.Ta_ext (Term.Term a b) a ();
ground_instances_ta f c t =
  Tree_Automata.Ta_ext
    (Set.insert (star c t)
      (Set_Impl.set_empty
        (Phantom_Type.of_phantom Container_Setup.set_impl_term)))
    (ground_instances_rules f c t)
    (Set_Impl.set_empty
      (Phantom_Type.of_phantom
        (Set_Impl.set_impl_prod ::
          Phantom_Type.Phantom (Term.Term a b, Term.Term a b)
            Set_Impl.Set_impla)))
    ();

}
