{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Tree_Automata_Det_Impl(sym_parts, ps_rules_nil_impl, ps_rules_cons_impl,
                          ps_states_nil_impl, ps_states_cons_impl)
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
import qualified List;
import qualified Phantom_Type;
import qualified HOL;
import qualified Complete_Lattices;
import qualified Cardinality;
import qualified Collection_Enum;
import qualified Product_Type;
import qualified Tree_Automata;
import qualified Set;
import qualified Container_Setup;
import qualified Collection_Order;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Arith;

sym_parts ::
  forall a b.
    (Collection_Order.Ccompare a, Eq a, Collection_Eq.Ceq b,
      Collection_Order.Ccompare b, Eq b,
      Set_Impl.Set_impl b) => Set.Set (Tree_Automata.Ta_rule a b) ->
                                Set.Set
                                  (b, (Arith.Nat,
Set.Set (Tree_Automata.Ta_rule a b)));
sym_parts rules =
  Set.image
    (\ (f, n) ->
      (f, (n, Set.filtera (\ r -> Tree_Automata.r_sym r == (f, n)) rules)))
    (Set.image Tree_Automata.r_sym rules);

list_inter ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Set_Impl.Set_impl a) => [Set.Set a] -> Set.Set a;
list_inter [] = Set.top_set;
list_inter [x] = x;
list_inter (x : v : va) = Set.inf_set x (list_inter (v : va));

rhs_eps_cl_memo ::
  forall a b c.
    (Collection_Order.Ccompare a, Eq a, Cardinality.Finite_UNIV b,
      Collection_Enum.Cenum b, Collection_Eq.Ceq b,
      Collection_Order.Cproper_interval b, Set_Impl.Set_impl b,
      Collection_Order.Ccompare c,
      Eq c) => (a -> Set.Set b) ->
                 Set.Set (Tree_Automata.Ta_rule a c) -> Set.Set b;
rhs_eps_cl_memo memo rules =
  Complete_Lattices.sup_set (Set.image (memo . Tree_Automata.r_rhs) rules);

ps_rules_nil_impl ::
  forall a b c.
    (Collection_Order.Ccompare a, Eq a, Cardinality.Finite_UNIV b,
      Collection_Enum.Cenum b, Collection_Eq.Ceq b,
      Collection_Order.Cproper_interval b, Eq b, Set_Impl.Set_impl b,
      Collection_Eq.Ceq c, Collection_Order.Ccompare c, Eq c,
      Set_Impl.Set_impl c) => (a -> Set.Set b) ->
                                Set.Set (Tree_Automata.Ta_rule a c) ->
                                  Set.Set (Tree_Automata.Ta_rule (Set.Set b) c);
ps_rules_nil_impl meps rules =
  let {
    rsz = Set.filtera (\ r -> null (Tree_Automata.r_lhs_states r)) rules;
  } in Set.image
         (\ f ->
           Tree_Automata.TA_rule f []
             (rhs_eps_cl_memo meps
               (Set.filtera (\ r -> Tree_Automata.r_root r == f) rsz)))
         (Set.image Tree_Automata.r_root rsz);

ps_rules_cons_impl ::
  forall a b c d.
    (Cardinality.Card_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Eq a, Set_Impl.Set_impl a,
      Collection_Eq.Ceq b, Collection_Order.Ccompare b, Eq b,
      Collection_Order.Ccompare c,
      Eq c) => (a -> Set.Set a) ->
                 Set.Set
                   (b, (Arith.Nat, Set.Set (Tree_Automata.Ta_rule a c))) ->
                   d -> Set.Set (Set.Set a) ->
                          Set.Set (Tree_Automata.Ta_rule (Set.Set a) b);
ps_rules_cons_impl meps parts rules q =
  let {
    lhs_nth =
      (\ (n, rs) ->
        map (\ i ->
              Set.filtera
                (\ x ->
                  not (Collection_Eq.set_eq (snd x)
                        (Set_Impl.set_empty
                          (Phantom_Type.of_phantom
                            Container_Setup.set_impl_ta_rule))))
                (Set.image
                  (\ p ->
                    (p, Set.filtera
                          (\ r ->
                            Set.member
                              (List.nth (Tree_Automata.r_lhs_states r) i) p)
                          rs))
                  q))
          (List.upt Arith.zero_nat n));
  } in Complete_Lattices.sup_set
         (Set.image
           (\ (f, nrs) ->
             Set.filtera (\ r -> not (Set.is_empty (Tree_Automata.r_rhs r)))
               (Set.image
                 (\ rs ->
                   Tree_Automata.TA_rule f (map fst rs)
                     (rhs_eps_cl_memo meps (list_inter (map snd rs))))
                 (List.listset (lhs_nth nrs))))
           parts);

ps_states_nil_impl ::
  forall a b c.
    (Collection_Order.Ccompare a, Eq a, Cardinality.Finite_UNIV b,
      Collection_Enum.Cenum b, Collection_Eq.Ceq b,
      Collection_Order.Cproper_interval b, Set_Impl.Set_impl b,
      Collection_Eq.Ceq c, Collection_Order.Ccompare c, Eq c,
      Set_Impl.Set_impl c) => (a -> Set.Set b) ->
                                Set.Set (Tree_Automata.Ta_rule a c) ->
                                  Set.Set (Set.Set b);
ps_states_nil_impl meps rules =
  let {
    rsz = Set.filtera (\ r -> null (Tree_Automata.r_lhs_states r)) rules;
  } in Set.image
         (\ f ->
           rhs_eps_cl_memo meps
             (Set.filtera (\ r -> Tree_Automata.r_root r == f) rsz))
         (Set.image Tree_Automata.r_root rsz);

ps_states_cons_impl ::
  forall a b c d e.
    (Cardinality.Finite_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Eq a, Set_Impl.Set_impl a,
      Cardinality.Card_UNIV b, Collection_Enum.Cenum b, Collection_Eq.Ceq b,
      Collection_Order.Cproper_interval b, Set_Impl.Set_impl b,
      Collection_Eq.Ceq c, Collection_Order.Ccompare c,
      Collection_Order.Ccompare d,
      Eq d) => (a -> Set.Set b) ->
                 Set.Set
                   (c, (Arith.Nat, Set.Set (Tree_Automata.Ta_rule a d))) ->
                   e -> Set.Set (Set.Set a) -> Set.Set (Set.Set b);
ps_states_cons_impl meps parts rules q =
  let {
    lhs_nth_in_Q =
      (\ (n, rs) ->
        map (\ i ->
              Set.minus_set
                (Set.image
                  (\ p ->
                    Set.filtera
                      (\ r ->
                        Set.member (List.nth (Tree_Automata.r_lhs_states r) i)
                          p)
                      rs)
                  q)
                (Set.insert
                  (Set_Impl.set_empty
                    (Phantom_Type.of_phantom Container_Setup.set_impl_ta_rule))
                  (Set_Impl.set_empty
                    (Phantom_Type.of_phantom Set_Impl.set_impl_set))))
          (List.upt Arith.zero_nat n));
  } in Complete_Lattices.sup_set
         (Set.image
           (\ (_, nrs) ->
             Set.minus_set
               (Set.image (\ rs -> rhs_eps_cl_memo meps (list_inter rs))
                 (List.listset (lhs_nth_in_Q nrs)))
               (Set.insert Set.bot_set
                 (Set_Impl.set_empty
                   (Phantom_Type.of_phantom Set_Impl.set_impl_set))))
           parts);

}
