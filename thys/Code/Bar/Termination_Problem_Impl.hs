{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Termination_Problem_Impl(Tp, tp_rbt_impl) where {

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
import qualified Map_Choice;
import qualified Missing_List;
import qualified Compare_Order_Instances;
import qualified Termination_Problem_Spec;
import qualified Multimap;
import qualified Q_Restricted_Rewriting_Impl;
import qualified HOL;
import qualified Product_Lexorder;
import qualified Rule_Map;
import qualified Mapping;
import qualified Term_Rewriting;
import qualified RBT;
import qualified Arith;
import qualified Compare;

newtype Tp b a = TP
  (Bool,
    ([Term_Rewriting.Term b a],
      (Bool,
        ([(Term_Rewriting.Term b a, Term_Rewriting.Term b a)],
          ([(Term_Rewriting.Term b a, Term_Rewriting.Term b a)],
            (RBT.Rbt (b, Arith.Nat)
               [(Bool, (Term_Rewriting.Term b a, Term_Rewriting.Term b a))],
              Term_Rewriting.Term b a -> Bool))))));

impl_of ::
  forall b a.
    (Compare.Compare_order b,
      Compare.Compare_order a) => Tp b a ->
                                    (Bool,
                                      ([Term_Rewriting.Term b a],
(Bool,
  ([(Term_Rewriting.Term b a, Term_Rewriting.Term b a)],
    ([(Term_Rewriting.Term b a, Term_Rewriting.Term b a)],
      (RBT.Rbt (b, Arith.Nat)
         [(Bool, (Term_Rewriting.Term b a, Term_Rewriting.Term b a))],
        Term_Rewriting.Term b a -> Bool))))));
impl_of (TP x) = x;

q_impl ::
  forall a b.
    (Bool,
      ([Term_Rewriting.Term a b],
        (Bool,
          ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
            ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
              (RBT.Rbt (a, Arith.Nat)
                 [(Bool, (Term_Rewriting.Term a b, Term_Rewriting.Term a b))],
                Term_Rewriting.Term a b -> Bool)))))) ->
      [Term_Rewriting.Term a b];
q_impl (uu, (q, uv)) = q;

q :: forall a b.
       (Compare.Compare_order a,
         Compare.Compare_order b) => Tp a b -> [Term_Rewriting.Term a b];
q tp = q_impl (impl_of tp);

r_impl ::
  forall a b.
    (Compare.Compare_order a) => (Bool,
                                   ([Term_Rewriting.Term a b],
                                     (Bool,
                                       ([(Term_Rewriting.Term a b,
   Term_Rewriting.Term a b)],
 ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
   (RBT.Rbt (a, Arith.Nat)
      [(Bool, (Term_Rewriting.Term a b, Term_Rewriting.Term a b))],
     Term_Rewriting.Term a b -> Bool)))))) ->
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)];
r_impl (uu, (uv, (uw, (vR, (ux, (m, uy)))))) = vR ++ Rule_Map.rules_with id m;

r :: forall a b.
       (Compare.Compare_order a,
         Compare.Compare_order b) => Tp a b ->
                                       [(Term_Rewriting.Term a b,
  Term_Rewriting.Term a b)];
r tp = r_impl (impl_of tp);

rw_impl ::
  forall a b.
    (Compare.Compare_order a) => (Bool,
                                   ([Term_Rewriting.Term a b],
                                     (Bool,
                                       ([(Term_Rewriting.Term a b,
   Term_Rewriting.Term a b)],
 ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
   (RBT.Rbt (a, Arith.Nat)
      [(Bool, (Term_Rewriting.Term a b, Term_Rewriting.Term a b))],
     Term_Rewriting.Term a b -> Bool)))))) ->
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)];
rw_impl (uu, (uv, (uw, (ux, (vRw, (m, uy)))))) =
  vRw ++ Rule_Map.rules_with not m;

rw :: forall a b.
        (Compare.Compare_order a,
          Compare.Compare_order b) => Tp a b ->
[(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
rw tp = rw_impl (impl_of tp);

mk_impl ::
  forall a b.
    (Compare.Compare_order a, Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => Bool ->
                                   [Term_Rewriting.Term a b] ->
                                     [(Term_Rewriting.Term a b,
Term_Rewriting.Term a b)] ->
                                       [(Term_Rewriting.Term a b,
  Term_Rewriting.Term a b)] ->
 (Bool,
   ([Term_Rewriting.Term a b],
     (Bool,
       ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
         ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
           (RBT.Rbt (a, Arith.Nat)
              [(Bool, (Term_Rewriting.Term a b, Term_Rewriting.Term a b))],
             Term_Rewriting.Term a b -> Bool))))));
mk_impl nfs q r rw =
  (case Arith.partition (Term_Rewriting.is_Var . fst) r of {
    (vr, ra) ->
      (case Arith.partition (Term_Rewriting.is_Var . fst) rw of {
        (vrw, rwa) ->
          let {
            isnf = Term_Rewriting.is_NF_terms q;
          } in (nfs, (q, (Q_Restricted_Rewriting_Impl.is_NF_trs_subset isnf
                            (r ++ rw),
                           (vr, (vrw, (Rule_Map.insert_rules True ra
 (Rule_Map.insert_rules False rwa RBT.empty),
isnf))))));
      });
  });

mk :: forall a b.
        (Compare.Compare_order a, Eq a, Arith.Ccompare b,
          Compare.Compare_order b, Eq b,
          Mapping.Mapping_impl b) => Bool ->
                                       [Term_Rewriting.Term a b] ->
 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
   [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] -> Tp a b;
mk nfs q r rw = TP (mk_impl nfs q r rw);

nfs_impl ::
  forall a b.
    (Compare.Compare_order a) => (Bool,
                                   ([Term_Rewriting.Term a b],
                                     (Bool,
                                       ([(Term_Rewriting.Term a b,
   Term_Rewriting.Term a b)],
 ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
   (RBT.Rbt (a, Arith.Nat)
      [(Bool, (Term_Rewriting.Term a b, Term_Rewriting.Term a b))],
     Term_Rewriting.Term a b -> Bool)))))) ->
                                   Bool;
nfs_impl (nfs, uu) = nfs;

nfs ::
  forall a b.
    (Compare.Compare_order a, Compare.Compare_order b) => Tp a b -> Bool;
nfs tp = nfs_impl (impl_of tp);

rules_impl ::
  forall a b.
    (Compare.Compare_order a) => (Bool,
                                   ([Term_Rewriting.Term a b],
                                     (Bool,
                                       ([(Term_Rewriting.Term a b,
   Term_Rewriting.Term a b)],
 ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
   (RBT.Rbt (a, Arith.Nat)
      [(Bool, (Term_Rewriting.Term a b, Term_Rewriting.Term a b))],
     Term_Rewriting.Term a b -> Bool)))))) ->
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)];
rules_impl (uu, (uv, (uw, (vR, (vRw, (m, ux)))))) =
  vR ++ vRw ++ map snd (Multimap.values m);

rules ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare_order b) => Tp a b ->
                                    [(Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b)];
rules tp = rules_impl (impl_of tp);

is_QNF_impl ::
  forall a b.
    (Bool,
      ([Term_Rewriting.Term a b],
        (Bool,
          ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
            ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
              (RBT.Rbt (a, Arith.Nat)
                 [(Bool, (Term_Rewriting.Term a b, Term_Rewriting.Term a b))],
                Term_Rewriting.Term a b -> Bool)))))) ->
      Term_Rewriting.Term a b -> Bool;
is_QNF_impl (uu, (uv, (uw, (ux, (uy, (uz, isnf)))))) = isnf;

is_QNF ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare_order b) => Tp a b -> Term_Rewriting.Term a b -> Bool;
is_QNF tp = is_QNF_impl (impl_of tp);

q_empty_impl ::
  forall a b.
    (Bool,
      ([Term_Rewriting.Term a b],
        (Bool,
          ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
            ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
              (RBT.Rbt (a, Arith.Nat)
                 [(Bool, (Term_Rewriting.Term a b, Term_Rewriting.Term a b))],
                Term_Rewriting.Term a b -> Bool)))))) ->
      Bool;
q_empty_impl (uu, (q, uv)) = null q;

q_empty ::
  forall a b.
    (Compare.Compare_order a, Compare.Compare_order b) => Tp a b -> Bool;
q_empty tp = q_empty_impl (impl_of tp);

qreltrs_impl ::
  forall a b.
    (Compare.Compare_order a, Eq a, Compare.Compare b,
      Eq b) => (Bool,
                 ([Term_Rewriting.Term a b],
                   (Bool,
                     ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
                       ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
                         (RBT.Rbt (a, Arith.Nat)
                            [(Bool,
                               (Term_Rewriting.Term a b,
                                 Term_Rewriting.Term a b))],
                           Term_Rewriting.Term a b -> Bool)))))) ->
                 (Bool,
                   (Arith.Set (Term_Rewriting.Term a b),
                     (Arith.Set
                        (Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                       Arith.Set
                         (Term_Rewriting.Term a b, Term_Rewriting.Term a b))));
qreltrs_impl (nfs, (q, (uu, (vR, (vRw, (m, isnf)))))) =
  (nfs, (Arith.set q,
          (Arith.set (vR ++ Rule_Map.rules_with id m),
            Arith.set (vRw ++ Rule_Map.rules_with not m))));

qreltrs ::
  forall a b.
    (Compare.Compare_order a, Eq a, Compare.Compare_order b,
      Eq b) => Tp a b ->
                 (Bool,
                   (Arith.Set (Term_Rewriting.Term a b),
                     (Arith.Set
                        (Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                       Arith.Set
                         (Term_Rewriting.Term a b, Term_Rewriting.Term a b))));
qreltrs tp = qreltrs_impl (impl_of tp);

rules_map_impl ::
  forall a b.
    (Compare.Compare_order a) => (Bool,
                                   ([Term_Rewriting.Term a b],
                                     (Bool,
                                       ([(Term_Rewriting.Term a b,
   Term_Rewriting.Term a b)],
 ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
   (RBT.Rbt (a, Arith.Nat)
      [(Bool, (Term_Rewriting.Term a b, Term_Rewriting.Term a b))],
     Term_Rewriting.Term a b -> Bool)))))) ->
                                   (a, Arith.Nat) ->
                                     [(Term_Rewriting.Term a b,
Term_Rewriting.Term a b)];
rules_map_impl (uu, (uv, (uw, (ux, (uy, (m, uz)))))) fn =
  (case RBT.lookup m fn of {
    Nothing -> [];
    Just a -> map snd a;
  });

rules_map ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare_order b) => Tp a b ->
                                    (a, Arith.Nat) ->
                                      [(Term_Rewriting.Term a b,
 Term_Rewriting.Term a b)];
rules_map tp = rules_map_impl (impl_of tp);

delete_R_Rw_impl ::
  forall a b.
    (Compare.Compare_order a, Eq a,
      Eq b) => (Bool,
                 ([Term_Rewriting.Term a b],
                   (Bool,
                     ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
                       ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
                         (RBT.Rbt (a, Arith.Nat)
                            [(Bool,
                               (Term_Rewriting.Term a b,
                                 Term_Rewriting.Term a b))],
                           Term_Rewriting.Term a b -> Bool)))))) ->
                 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                   [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                     (Bool,
                       ([Term_Rewriting.Term a b],
                         (Bool,
                           ([(Term_Rewriting.Term a b,
                               Term_Rewriting.Term a b)],
                             ([(Term_Rewriting.Term a b,
                                 Term_Rewriting.Term a b)],
                               (RBT.Rbt (a, Arith.Nat)
                                  [(Bool,
                                     (Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b))],
                                 Term_Rewriting.Term a b -> Bool))))));
delete_R_Rw_impl (nfs, (q, (uu, (vR, (vRw, (m, isnf)))))) r rw =
  (case Arith.partition (Term_Rewriting.is_Var . fst) r of {
    (vr, ra) ->
      (case Arith.partition (Term_Rewriting.is_Var . fst) rw of {
        (vrw, rwa) ->
          let {
            vra = Missing_List.list_diff vR vr;
            vrwa = Missing_List.list_diff vRw vrw;
            ma = Rule_Map.delete_rules True ra
                   (Rule_Map.delete_rules False rwa m);
          } in (nfs, (q, (Q_Restricted_Rewriting_Impl.is_NF_trs_subset isnf
                            (vra ++ vrwa ++ map snd (Multimap.values ma)),
                           (vra, (vrwa, (ma, isnf))))));
      });
  });

delete_R_Rw ::
  forall a b.
    (Compare.Compare_order a, Eq a, Compare.Compare_order b,
      Eq b) => Tp a b ->
                 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                   [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                     Tp a b;
delete_R_Rw tp r rw = TP (delete_R_Rw_impl (impl_of tp) r rw);

split_rules_impl ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare_order b) => (Bool,
                                    ([Term_Rewriting.Term a b],
                                      (Bool,
([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
  ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
    (RBT.Rbt (a, Arith.Nat)
       [(Bool, (Term_Rewriting.Term a b, Term_Rewriting.Term a b))],
      Term_Rewriting.Term a b -> Bool)))))) ->
                                    [(Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b)] ->
                                      ([(Term_Rewriting.Term a b,
  Term_Rewriting.Term a b)],
[(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]);
split_rules_impl tp rs = let {
                           m = Map_Choice.ceta_set_of rs;
                         } in Arith.partition m (rules_impl tp);

split_rules ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare_order b) => Tp a b ->
                                    [(Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b)] ->
                                      ([(Term_Rewriting.Term a b,
  Term_Rewriting.Term a b)],
[(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]);
split_rules tp = split_rules_impl (impl_of tp);

nFQ_subset_NF_rules_impl ::
  forall a b.
    (Bool,
      ([Term_Rewriting.Term a b],
        (Bool,
          ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
            ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
              (RBT.Rbt (a, Arith.Nat)
                 [(Bool, (Term_Rewriting.Term a b, Term_Rewriting.Term a b))],
                Term_Rewriting.Term a b -> Bool)))))) ->
      Bool;
nFQ_subset_NF_rules_impl (uu, (uv, (b, uw))) = b;

nFQ_subset_NF_rules ::
  forall a b.
    (Compare.Compare_order a, Compare.Compare_order b) => Tp a b -> Bool;
nFQ_subset_NF_rules tp = nFQ_subset_NF_rules_impl (impl_of tp);

tp_rbt_impl ::
  forall a b.
    (Compare.Compare_order a, Eq a, Arith.Ccompare b, Compare.Compare_order b,
      Eq b,
      Mapping.Mapping_impl b) => Termination_Problem_Spec.Tp_ops_ext (Tp a b) a
                                   b ();
tp_rbt_impl =
  Termination_Problem_Spec.Tp_ops_ext qreltrs q r rw rules q_empty is_QNF
    nFQ_subset_NF_rules rules_map delete_R_Rw split_rules mk nfs ();

}
