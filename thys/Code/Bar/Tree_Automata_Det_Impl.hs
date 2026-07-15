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
import qualified Phantom_Type;
import qualified HOL;
import qualified Complete_Lattices;
import qualified Term_Rewriting;
import qualified Arith;

sym_parts ::
  forall a b.
    (Arith.Ccompare a, Eq a, Arith.Ceq b, Arith.Ccompare b, Eq b,
      Arith.Set_impl b) => Arith.Set (Term_Rewriting.Ta_rule a b) ->
                             Arith.Set
                               (b, (Arith.Nat,
                                     Arith.Set (Term_Rewriting.Ta_rule a b)));
sym_parts rules =
  Arith.image
    (\ (f, n) ->
      (f, (n, Arith.filtera (\ r -> Term_Rewriting.r_sym r == (f, n)) rules)))
    (Arith.image Term_Rewriting.r_sym rules);

list_inter ::
  forall a.
    (Arith.Ceq a, Arith.Ccompare a,
      Arith.Set_impl a) => [Arith.Set a] -> Arith.Set a;
list_inter [] = Arith.top_set;
list_inter [x] = x;
list_inter (x : v : va) = Arith.inf_set x (list_inter (v : va));

rhs_eps_cl_memo ::
  forall a b c.
    (Arith.Ccompare a, Eq a, Arith.Finite_UNIV b, Arith.Cenum b, Arith.Ceq b,
      Arith.Cproper_interval b, Arith.Set_impl b, Arith.Ccompare c,
      Eq c) => (a -> Arith.Set b) ->
                 Arith.Set (Term_Rewriting.Ta_rule a c) -> Arith.Set b;
rhs_eps_cl_memo memo rules =
  Complete_Lattices.sup_set (Arith.image (memo . Term_Rewriting.r_rhs) rules);

ps_rules_nil_impl ::
  forall a b c.
    (Arith.Ccompare a, Eq a, Arith.Finite_UNIV b, Arith.Cenum b, Arith.Ceq b,
      Arith.Cproper_interval b, Eq b, Arith.Set_impl b, Arith.Ceq c,
      Arith.Ccompare c, Eq c,
      Arith.Set_impl c) => (a -> Arith.Set b) ->
                             Arith.Set (Term_Rewriting.Ta_rule a c) ->
                               Arith.Set
                                 (Term_Rewriting.Ta_rule (Arith.Set b) c);
ps_rules_nil_impl meps rules =
  let {
    rsz = Arith.filtera (\ r -> null (Term_Rewriting.r_lhs_states r)) rules;
  } in Arith.image
         (\ f ->
           Term_Rewriting.TA_rule f []
             (rhs_eps_cl_memo meps
               (Arith.filtera (\ r -> Term_Rewriting.r_root r == f) rsz)))
         (Arith.image Term_Rewriting.r_root rsz);

ps_rules_cons_impl ::
  forall a b c d.
    (Arith.Card_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Eq a, Arith.Set_impl a, Arith.Ceq b, Arith.Ccompare b, Eq b,
      Arith.Ccompare c,
      Eq c) => (a -> Arith.Set a) ->
                 Arith.Set
                   (b, (Arith.Nat, Arith.Set (Term_Rewriting.Ta_rule a c))) ->
                   d -> Arith.Set (Arith.Set a) ->
                          Arith.Set (Term_Rewriting.Ta_rule (Arith.Set a) b);
ps_rules_cons_impl meps parts rules q =
  let {
    lhs_nth =
      (\ (n, rs) ->
        map (\ i ->
              Arith.filtera
                (\ x ->
                  not (Arith.set_eq (snd x)
                        (Arith.set_empty
                          (Phantom_Type.of_phantom
                            Term_Rewriting.set_impl_ta_rule))))
                (Arith.image
                  (\ p ->
                    (p, Arith.filtera
                          (\ r ->
                            Arith.member
                              (Arith.nth (Term_Rewriting.r_lhs_states r) i) p)
                          rs))
                  q))
          (Arith.upt Arith.zero_nat n));
  } in Complete_Lattices.sup_set
         (Arith.image
           (\ (f, nrs) ->
             Arith.filtera
               (\ r -> not (Arith.is_empty (Term_Rewriting.r_rhs r)))
               (Arith.image
                 (\ rs ->
                   Term_Rewriting.TA_rule f (map fst rs)
                     (rhs_eps_cl_memo meps (list_inter (map snd rs))))
                 (Arith.listset (lhs_nth nrs))))
           parts);

ps_states_nil_impl ::
  forall a b c.
    (Arith.Ccompare a, Eq a, Arith.Finite_UNIV b, Arith.Cenum b, Arith.Ceq b,
      Arith.Cproper_interval b, Arith.Set_impl b, Arith.Ceq c, Arith.Ccompare c,
      Eq c,
      Arith.Set_impl c) => (a -> Arith.Set b) ->
                             Arith.Set (Term_Rewriting.Ta_rule a c) ->
                               Arith.Set (Arith.Set b);
ps_states_nil_impl meps rules =
  let {
    rsz = Arith.filtera (\ r -> null (Term_Rewriting.r_lhs_states r)) rules;
  } in Arith.image
         (\ f ->
           rhs_eps_cl_memo meps
             (Arith.filtera (\ r -> Term_Rewriting.r_root r == f) rsz))
         (Arith.image Term_Rewriting.r_root rsz);

ps_states_cons_impl ::
  forall a b c d e.
    (Arith.Finite_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Eq a, Arith.Set_impl a, Arith.Card_UNIV b, Arith.Cenum b, Arith.Ceq b,
      Arith.Cproper_interval b, Arith.Set_impl b, Arith.Ceq c, Arith.Ccompare c,
      Arith.Ccompare d,
      Eq d) => (a -> Arith.Set b) ->
                 Arith.Set
                   (c, (Arith.Nat, Arith.Set (Term_Rewriting.Ta_rule a d))) ->
                   e -> Arith.Set (Arith.Set a) -> Arith.Set (Arith.Set b);
ps_states_cons_impl meps parts rules q =
  let {
    lhs_nth_in_Q =
      (\ (n, rs) ->
        map (\ i ->
              Arith.minus_set
                (Arith.image
                  (\ p ->
                    Arith.filtera
                      (\ r ->
                        Arith.member
                          (Arith.nth (Term_Rewriting.r_lhs_states r) i) p)
                      rs)
                  q)
                (Arith.insert
                  (Arith.set_empty
                    (Phantom_Type.of_phantom Term_Rewriting.set_impl_ta_rule))
                  (Arith.set_empty
                    (Phantom_Type.of_phantom Arith.set_impl_set))))
          (Arith.upt Arith.zero_nat n));
  } in Complete_Lattices.sup_set
         (Arith.image
           (\ (_, nrs) ->
             Arith.minus_set
               (Arith.image (\ rs -> rhs_eps_cl_memo meps (list_inter rs))
                 (Arith.listset (lhs_nth_in_Q nrs)))
               (Arith.insert Arith.bot_set
                 (Arith.set_empty
                   (Phantom_Type.of_phantom Arith.set_impl_set))))
           parts);

}
