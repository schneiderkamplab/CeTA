{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module AC_Dependency_Pair_Problem_Impl(Ac_dpp, ac_dpp_rbt_impl) where {

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
import qualified HOL;
import qualified AC_Dependency_Pair_Problem_Spec;
import qualified Compare_Order_Instances;
import qualified Rule_Map;
import qualified Product_Lexorder;
import qualified Term_Rewriting;
import qualified RBT;
import qualified Arith;
import qualified Compare;

newtype Ac_dpp b a = AC_DPP
  ([(Term_Rewriting.Term b a, Term_Rewriting.Term b a)],
    ([(Term_Rewriting.Term b a, Term_Rewriting.Term b a)],
      ([(Term_Rewriting.Term b a, Term_Rewriting.Term b a)],
        ([(Term_Rewriting.Term b a, Term_Rewriting.Term b a)],
          ([(Term_Rewriting.Term b a, Term_Rewriting.Term b a)],
            RBT.Rbt (b, Arith.Nat)
              [((), (Term_Rewriting.Term b a, Term_Rewriting.Term b a))])))));

impl_of ::
  forall b a.
    (Compare.Compare_order b) => Ac_dpp b a ->
                                   ([(Term_Rewriting.Term b a,
                                       Term_Rewriting.Term b a)],
                                     ([(Term_Rewriting.Term b a,
 Term_Rewriting.Term b a)],
                                       ([(Term_Rewriting.Term b a,
   Term_Rewriting.Term b a)],
 ([(Term_Rewriting.Term b a, Term_Rewriting.Term b a)],
   ([(Term_Rewriting.Term b a, Term_Rewriting.Term b a)],
     RBT.Rbt (b, Arith.Nat)
       [((), (Term_Rewriting.Term b a, Term_Rewriting.Term b a))])))));
impl_of (AC_DPP x) = x;

e_impl ::
  forall a b.
    ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
      ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
        ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
          ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
            ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
              RBT.Rbt (a, Arith.Nat)
                [((), (Term_Rewriting.Term a b,
                        Term_Rewriting.Term a b))]))))) ->
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
e_impl (p, (pw, (r, (rw, (e, uu))))) = e;

e :: forall a b.
       (Compare.Compare_order a) => Ac_dpp a b ->
                                      [(Term_Rewriting.Term a b,
 Term_Rewriting.Term a b)];
e xa = e_impl (impl_of xa);

p_impl ::
  forall a b.
    ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
      ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
        ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
          ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
            ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
              RBT.Rbt (a, Arith.Nat)
                [((), (Term_Rewriting.Term a b,
                        Term_Rewriting.Term a b))]))))) ->
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
p_impl (p, (pw, (r, (rw, (e, uu))))) = p;

p :: forall a b.
       (Compare.Compare_order a) => Ac_dpp a b ->
                                      [(Term_Rewriting.Term a b,
 Term_Rewriting.Term a b)];
p xa = p_impl (impl_of xa);

r_impl ::
  forall a b.
    ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
      ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
        ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
          ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
            ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
              RBT.Rbt (a, Arith.Nat)
                [((), (Term_Rewriting.Term a b,
                        Term_Rewriting.Term a b))]))))) ->
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
r_impl (p, (pw, (r, (rw, (e, uu))))) = r;

r :: forall a b.
       (Compare.Compare_order a) => Ac_dpp a b ->
                                      [(Term_Rewriting.Term a b,
 Term_Rewriting.Term a b)];
r xa = r_impl (impl_of xa);

pw_impl ::
  forall a b.
    ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
      ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
        ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
          ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
            ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
              RBT.Rbt (a, Arith.Nat)
                [((), (Term_Rewriting.Term a b,
                        Term_Rewriting.Term a b))]))))) ->
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
pw_impl (p, (pw, (r, (rw, (e, uu))))) = pw;

pw :: forall a b.
        (Compare.Compare_order a) => Ac_dpp a b ->
                                       [(Term_Rewriting.Term a b,
  Term_Rewriting.Term a b)];
pw xa = pw_impl (impl_of xa);

rw_impl ::
  forall a b.
    ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
      ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
        ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
          ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
            ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
              RBT.Rbt (a, Arith.Nat)
                [((), (Term_Rewriting.Term a b,
                        Term_Rewriting.Term a b))]))))) ->
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
rw_impl (p, (pw, (r, (rw, (e, uu))))) = rw;

rw :: forall a b.
        (Compare.Compare_order a) => Ac_dpp a b ->
                                       [(Term_Rewriting.Term a b,
  Term_Rewriting.Term a b)];
rw xa = rw_impl (impl_of xa);

mk_impl ::
  forall a b.
    (Compare.Compare_order a, Eq a,
      Eq b) => [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                   [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                     [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                       [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                         ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
                           ([(Term_Rewriting.Term a b,
                               Term_Rewriting.Term a b)],
                             ([(Term_Rewriting.Term a b,
                                 Term_Rewriting.Term a b)],
                               ([(Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b)],
                                 ([(Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b)],
                                   RBT.Rbt (a, Arith.Nat)
                                     [((),
(Term_Rewriting.Term a b, Term_Rewriting.Term a b))])))));
mk_impl p pw r rw e =
  (p, (pw, (r, (rw, (e, Rule_Map.insert_rules () (r ++ rw ++ e) RBT.empty)))));

mk :: forall a b.
        (Compare.Compare_order a, Eq a,
          Eq b) => [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                     [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                       [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                         [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                           [(Term_Rewriting.Term a b,
                              Term_Rewriting.Term a b)] ->
                             Ac_dpp a b;
mk xc xd xe xf xg = AC_DPP (mk_impl xc xd xe xf xg);

pairs_impl ::
  forall a b.
    ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
      ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
        ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
          ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
            ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
              RBT.Rbt (a, Arith.Nat)
                [((), (Term_Rewriting.Term a b,
                        Term_Rewriting.Term a b))]))))) ->
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
pairs_impl (p, (pw, (r, (rw, (e, uu))))) = p ++ pw;

pairs ::
  forall a b.
    (Compare.Compare_order a) => Ac_dpp a b ->
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)];
pairs xa = pairs_impl (impl_of xa);

rules_impl ::
  forall a b.
    ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
      ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
        ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
          ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
            ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
              RBT.Rbt (a, Arith.Nat)
                [((), (Term_Rewriting.Term a b,
                        Term_Rewriting.Term a b))]))))) ->
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
rules_impl (p, (pw, (r, (rw, (e, uu))))) = r ++ rw;

rules ::
  forall a b.
    (Compare.Compare_order a) => Ac_dpp a b ->
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)];
rules xa = rules_impl (impl_of xa);

ac_dpp_impl ::
  forall a b.
    (Compare.Compare_order a, Eq a, Compare.Compare b,
      Eq b) => ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
                 ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
                   ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
                     ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
                       ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
                         RBT.Rbt (a, Arith.Nat)
                           [((), (Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b))]))))) ->
                 (Arith.Set (Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                   (Arith.Set
                      (Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                     (Arith.Set
                        (Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                       (Arith.Set
                          (Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                         Arith.Set
                           (Term_Rewriting.Term a b,
                             Term_Rewriting.Term a b)))));
ac_dpp_impl (p, (pw, (r, (rw, (e, uu))))) =
  (Arith.set p, (Arith.set pw, (Arith.set r, (Arith.set rw, Arith.set e))));

ac_dpp ::
  forall a b.
    (Compare.Compare_order a, Eq a, Compare.Compare b,
      Eq b) => Ac_dpp a b ->
                 (Arith.Set (Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                   (Arith.Set
                      (Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                     (Arith.Set
                        (Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                       (Arith.Set
                          (Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                         Arith.Set
                           (Term_Rewriting.Term a b,
                             Term_Rewriting.Term a b)))));
ac_dpp xa = ac_dpp_impl (impl_of xa);

rules_map_impl ::
  forall a b.
    (Compare.Compare_order a) => ([(Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b)],
                                   ([(Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b)],
                                     ([(Term_Rewriting.Term a b,
 Term_Rewriting.Term a b)],
                                       ([(Term_Rewriting.Term a b,
   Term_Rewriting.Term a b)],
 ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
   RBT.Rbt (a, Arith.Nat)
     [((), (Term_Rewriting.Term a b, Term_Rewriting.Term a b))]))))) ->
                                   (a, Arith.Nat) ->
                                     [(Term_Rewriting.Term a b,
Term_Rewriting.Term a b)];
rules_map_impl (p, (pw, (r, (rw, (e, m))))) fn = (case RBT.lookup m fn of {
           Nothing -> [];
           Just a -> map snd a;
         });

rules_map ::
  forall a b.
    (Compare.Compare_order a) => Ac_dpp a b ->
                                   (a, Arith.Nat) ->
                                     [(Term_Rewriting.Term a b,
Term_Rewriting.Term a b)];
rules_map xa = rules_map_impl (impl_of xa);

eq_rules_non_collapsing ::
  forall a b. (Compare.Compare_order a) => Ac_dpp a b -> Bool;
eq_rules_non_collapsing d =
  let {
    t = all (\ (_, ra) -> not (Term_Rewriting.is_Var ra));
  } in t (r d) && t (rw d) && t (e d);

eq_rules_no_left_var ::
  forall a b. (Compare.Compare_order a) => Ac_dpp a b -> Bool;
eq_rules_no_left_var d = let {
                           t = all (\ (l, _) -> not (Term_Rewriting.is_Var l));
                         } in t (r d) && t (rw d) && t (e d);

delete_pairs_rules_impl ::
  forall a b.
    (Compare.Compare_order a, Eq a,
      Eq b) => ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
                 ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
                   ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
                     ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
                       ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
                         RBT.Rbt (a, Arith.Nat)
                           [((), (Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b))]))))) ->
                 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                   [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                     ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
                       ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
                         ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
                           ([(Term_Rewriting.Term a b,
                               Term_Rewriting.Term a b)],
                             ([(Term_Rewriting.Term a b,
                                 Term_Rewriting.Term a b)],
                               RBT.Rbt (a, Arith.Nat)
                                 [((), (Term_Rewriting.Term a b,
 Term_Rewriting.Term a b))])))));
delete_pairs_rules_impl (p, (pw, (r, (rw, (e, m))))) pd rd =
  (if null rd
    then (Missing_List.list_diff p pd,
           (Missing_List.list_diff pw pd, (r, (rw, (e, m)))))
    else mk_impl (Missing_List.list_diff p pd) (Missing_List.list_diff pw pd)
           (Missing_List.list_diff r rd) (Missing_List.list_diff rw rd) e);

delete_pairs_rules ::
  forall a b.
    (Compare.Compare_order a, Eq a,
      Eq b) => Ac_dpp a b ->
                 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                   [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                     Ac_dpp a b;
delete_pairs_rules xc xd xe =
  AC_DPP (delete_pairs_rules_impl (impl_of xc) xd xe);

reverse_rules_map ::
  forall a b.
    (Compare.Compare_order a,
      Eq a) => Ac_dpp a b ->
                 (a, Arith.Nat) ->
                   [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
reverse_rules_map d fn =
  concatMap
    (\ (l, ra) -> (if Term_Rewriting.root ra == Just fn then [(ra, l)] else []))
    (r d ++ rw d ++ e d);

intersect_pairs_impl ::
  forall a b.
    (Compare.Compare_order a, Eq a,
      Eq b) => ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
                 ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
                   ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
                     ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
                       ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
                         RBT.Rbt (a, Arith.Nat)
                           [((), (Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b))]))))) ->
                 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                   ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
                     ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
                       ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
                         ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
                           ([(Term_Rewriting.Term a b,
                               Term_Rewriting.Term a b)],
                             RBT.Rbt (a, Arith.Nat)
                               [((), (Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b))])))));
intersect_pairs_impl (p, (pw, (r, (rw, (e, m))))) pd =
  (Arith.inter_list_set p pd, (Arith.inter_list_set pw pd, (r, (rw, (e, m)))));

intersect_pairs ::
  forall a b.
    (Compare.Compare_order a, Eq a,
      Eq b) => Ac_dpp a b ->
                 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                   Ac_dpp a b;
intersect_pairs xb xc = AC_DPP (intersect_pairs_impl (impl_of xb) xc);

ac_dpp_rbt_impl ::
  forall a b.
    (Compare.Compare_order a, Eq a, Compare.Compare b,
      Eq b) => AC_Dependency_Pair_Problem_Spec.Ac_dpp_ops_ext (Ac_dpp a b) a b
                 ();
ac_dpp_rbt_impl =
  AC_Dependency_Pair_Problem_Spec.Ac_dpp_ops_ext ac_dpp p pw pairs r rw rules e
    mk rules_map reverse_rules_map delete_pairs_rules eq_rules_no_left_var
    eq_rules_non_collapsing intersect_pairs ();

}
