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
import qualified Complete_Lattices;
import qualified Compare;
import qualified Arith;
import qualified Term_Rewriting;

star :: forall a b. a -> Term_Rewriting.Term a b -> Term_Rewriting.Term a b;
star c (Term_Rewriting.Var x) = Term_Rewriting.Fun c [];
star c (Term_Rewriting.Fun f ts) = Term_Rewriting.Fun f (map (star c) ts);

growing_rule ::
  forall a b.
    (Eq a, Arith.Ceq b, Arith.Ccompare b, Eq b,
      Arith.Set_impl b) => (Term_Rewriting.Term a b, Term_Rewriting.Term a b) ->
                             Bool;
growing_rule (l, r) =
  Arith.ball (Term_Rewriting.vars_term r)
    (\ x ->
      Arith.ball (Term_Rewriting.var_poss l)
        (\ p ->
          (if Term_Rewriting.equal_term (Term_Rewriting.Var x)
                (Term_Rewriting.subt_at l p)
            then Arith.less_eq_nat (Arith.size_list p) Arith.one_nat
            else True)));

growing ::
  forall a b.
    (Compare.Compare a, Eq a, Arith.Ceq b, Arith.Ccompare b, Compare.Compare b,
      Eq b,
      Arith.Set_impl b) => Arith.Set
                             (Term_Rewriting.Term a b,
                               Term_Rewriting.Term a b) ->
                             Bool;
growing r = Arith.ball r growing_rule;

funas_ta_rule ::
  forall a b.
    (Arith.Ceq b, Arith.Ccompare b,
      Arith.Set_impl b) => Term_Rewriting.Ta_rule a b ->
                             Arith.Set (b, Arith.Nat);
funas_ta_rule r =
  Arith.insert
    (Term_Rewriting.r_root r, Arith.size_list (Term_Rewriting.r_lhs_states r))
    Arith.bot_set;

funas_ta ::
  forall a b.
    (Arith.Ccompare a, Eq a, Arith.Finite_UNIV b, Arith.Cenum b, Arith.Ceq b,
      Arith.Cproper_interval b, Eq b,
      Arith.Set_impl b) => Term_Rewriting.Ta_ext a b () ->
                             Arith.Set (b, Arith.Nat);
funas_ta a =
  Complete_Lattices.sup_set
    (Arith.image funas_ta_rule (Term_Rewriting.ta_rules a));

sig_rules ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Eq a, Arith.Ccompare b,
      Eq b) => Arith.Set (a, Arith.Nat) ->
                 b -> Arith.Set (Term_Rewriting.Ta_rule b a);
sig_rules f c =
  Arith.image (\ (fa, n) -> Term_Rewriting.TA_rule fa (Arith.replicate n c) c)
    f;

map_r_states ::
  forall a b c.
    (a -> b) -> Term_Rewriting.Ta_rule a c -> Term_Rewriting.Ta_rule b c;
map_r_states f r =
  Term_Rewriting.TA_rule (Term_Rewriting.r_root r)
    (map f (Term_Rewriting.r_lhs_states r)) (f (Term_Rewriting.r_rhs r));

reachable_states ::
  forall a b c.
    (Arith.Ceq a, Arith.Ccompare a, Eq a, Arith.Set_impl a, Arith.Ccompare b,
      Eq b) => Arith.Set (Term_Rewriting.Ta_rule a b) ->
                 Term_Rewriting.Term (Sum_Type.Sum b a) c -> Arith.Set a;
reachable_states delta (Term_Rewriting.Fun (Sum_Type.Inr q) []) =
  Arith.insert q Arith.bot_set;
reachable_states delta (Term_Rewriting.Fun (Sum_Type.Inl f) ts) =
  Arith.image Term_Rewriting.r_rhs
    (Arith.filtera
      (\ r ->
        Term_Rewriting.r_root r == f &&
          Arith.equal_nat (Arith.size_list (Term_Rewriting.r_lhs_states r))
            (Arith.size_list ts) &&
            let {
              d = Arith.minus_nat (Arith.size_list ts) Arith.one_nat;
            } in (if Arith.less_nat d (Arith.size_list ts)
                   then Arith.all_interval
                          (\ i ->
                            Arith.member
                              (Arith.nth (Term_Rewriting.r_lhs_states r) i)
                              (reachable_states delta (Arith.nth ts i)))
                          Arith.zero_nat d
                   else True))
      delta);
reachable_states delta (Term_Rewriting.Var v) = Arith.bot_set;
reachable_states delta (Term_Rewriting.Fun (Sum_Type.Inr va) (vb : vc)) =
  Arith.bot_set;

ground_instances_rules ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Compare.Compare a, Eq a, Compare.Compare b,
      Eq b) => Arith.Set (a, Arith.Nat) ->
                 a -> Term_Rewriting.Term a b ->
                        Arith.Set
                          (Term_Rewriting.Ta_rule (Term_Rewriting.Term a b) a);
ground_instances_rules f c (Term_Rewriting.Var x) =
  sig_rules f (Term_Rewriting.Fun c []);
ground_instances_rules fa c (Term_Rewriting.Fun f ts) =
  Arith.sup_set
    (Arith.insert
      (Term_Rewriting.TA_rule f (map (star c) ts)
        (star c (Term_Rewriting.Fun f ts)))
      (Arith.set_empty
        (Phantom_Type.of_phantom Term_Rewriting.set_impl_ta_rule)))
    (Complete_Lattices.sup_set
      (Arith.image (ground_instances_rules fa c) (Arith.set ts)));

ground_instances_ta ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Compare.Compare a, Eq a, Compare.Compare b,
      Eq b) => Arith.Set (a, Arith.Nat) ->
                 a -> Term_Rewriting.Term a b ->
                        Term_Rewriting.Ta_ext (Term_Rewriting.Term a b) a ();
ground_instances_ta f c t =
  Term_Rewriting.Ta_ext
    (Arith.insert (star c t)
      (Arith.set_empty (Phantom_Type.of_phantom Term_Rewriting.set_impl_term)))
    (ground_instances_rules f c t)
    (Arith.set_empty
      (Phantom_Type.of_phantom
        (Arith.set_impl_prod ::
          Phantom_Type.Phantom
            (Term_Rewriting.Term a b, Term_Rewriting.Term a b)
            Arith.Set_impla)))
    ();

}
