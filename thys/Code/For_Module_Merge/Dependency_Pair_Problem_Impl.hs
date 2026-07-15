{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Dependency_Pair_Problem_Impl(Dpp, dpp_rbt_impl) where {

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
import qualified Util;
import qualified Missing_List;
import qualified Option;
import qualified Compare_Order_Instances;
import qualified Compare_Instances;
import qualified Dependency_Pair_Problem_Spec;
import qualified Multimap;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Container_Setup;
import qualified Q_Restricted_Rewriting_Impl;
import qualified Product_Type;
import qualified Trs_Impl;
import qualified List;
import qualified HOL;
import qualified Product_Lexorder;
import qualified Rule_Map;
import qualified Set;
import qualified Mapping_Impl;
import qualified Collection_Order;
import qualified Term;
import qualified RBT;
import qualified Arith;
import qualified Compare;

newtype Dpp b a = DPP
  (Bool,
    (Bool,
      ([(Term.Term b a, Term.Term b a)],
        ([(Term.Term b a, Term.Term b a)],
          ([Term.Term b a],
            (Bool,
              (Bool,
                ([(Term.Term b a, Term.Term b a)],
                  ([(Term.Term b a, Term.Term b a)],
                    (RBT.Rbt (b, Arith.Nat)
                       [(Bool, (Term.Term b a, Term.Term b a))],
                      (RBT.Rbt (b, Arith.Nat)
                         [(Bool, (Term.Term b a, Term.Term b a))],
                        (Bool, Term.Term b a -> Bool))))))))))));

impl_of ::
  forall b a.
    (Compare.Compare_order b) => Dpp b a ->
                                   (Bool,
                                     (Bool,
                                       ([(Term.Term b a, Term.Term b a)],
 ([(Term.Term b a, Term.Term b a)],
   ([Term.Term b a],
     (Bool,
       (Bool,
         ([(Term.Term b a, Term.Term b a)],
           ([(Term.Term b a, Term.Term b a)],
             (RBT.Rbt (b, Arith.Nat) [(Bool, (Term.Term b a, Term.Term b a))],
               (RBT.Rbt (b, Arith.Nat) [(Bool, (Term.Term b a, Term.Term b a))],
                 (Bool, Term.Term b a -> Bool))))))))))));
impl_of (DPP x) = x;

m_impl ::
  forall a b.
    (Bool,
      (Bool,
        ([(Term.Term a b, Term.Term a b)],
          ([(Term.Term a b, Term.Term a b)],
            ([Term.Term a b],
              (Bool,
                (Bool,
                  ([(Term.Term a b, Term.Term a b)],
                    ([(Term.Term a b, Term.Term a b)],
                      (RBT.Rbt (a, Arith.Nat)
                         [(Bool, (Term.Term a b, Term.Term a b))],
                        (RBT.Rbt (a, Arith.Nat)
                           [(Bool, (Term.Term a b, Term.Term a b))],
                          (Bool, Term.Term a b -> Bool)))))))))))) ->
      Bool;
m_impl (uu, (mi, uv)) = mi;

m :: forall a b. (Compare.Compare_order a) => Dpp a b -> Bool;
m d = m_impl (impl_of d);

p_impl ::
  forall a b.
    (Bool,
      (Bool,
        ([(Term.Term a b, Term.Term a b)],
          ([(Term.Term a b, Term.Term a b)],
            ([Term.Term a b],
              (Bool,
                (Bool,
                  ([(Term.Term a b, Term.Term a b)],
                    ([(Term.Term a b, Term.Term a b)],
                      (RBT.Rbt (a, Arith.Nat)
                         [(Bool, (Term.Term a b, Term.Term a b))],
                        (RBT.Rbt (a, Arith.Nat)
                           [(Bool, (Term.Term a b, Term.Term a b))],
                          (Bool, Term.Term a b -> Bool)))))))))))) ->
      [(Term.Term a b, Term.Term a b)];
p_impl (uu, (uv, (p, uw))) = p;

p :: forall a b.
       (Compare.Compare_order a) => Dpp a b -> [(Term.Term a b, Term.Term a b)];
p d = p_impl (impl_of d);

q_impl ::
  forall a b.
    (Bool,
      (Bool,
        ([(Term.Term a b, Term.Term a b)],
          ([(Term.Term a b, Term.Term a b)],
            ([Term.Term a b],
              (Bool,
                (Bool,
                  ([(Term.Term a b, Term.Term a b)],
                    ([(Term.Term a b, Term.Term a b)],
                      (RBT.Rbt (a, Arith.Nat)
                         [(Bool, (Term.Term a b, Term.Term a b))],
                        (RBT.Rbt (a, Arith.Nat)
                           [(Bool, (Term.Term a b, Term.Term a b))],
                          (Bool, Term.Term a b -> Bool)))))))))))) ->
      [Term.Term a b];
q_impl (uu, (uv, (uw, (ux, (q, uy))))) = q;

q :: forall a b. (Compare.Compare_order a) => Dpp a b -> [Term.Term a b];
q d = q_impl (impl_of d);

r_impl ::
  forall a b.
    (Compare.Compare_order a) => (Bool,
                                   (Bool,
                                     ([(Term.Term a b, Term.Term a b)],
                                       ([(Term.Term a b, Term.Term a b)],
 ([Term.Term a b],
   (Bool,
     (Bool,
       ([(Term.Term a b, Term.Term a b)],
         ([(Term.Term a b, Term.Term a b)],
           (RBT.Rbt (a, Arith.Nat) [(Bool, (Term.Term a b, Term.Term a b))],
             (RBT.Rbt (a, Arith.Nat) [(Bool, (Term.Term a b, Term.Term a b))],
               (Bool, Term.Term a b -> Bool)))))))))))) ->
                                   [(Term.Term a b, Term.Term a b)];
r_impl (uu, (uv, (uw, (ux, (uy, (uz, (va, (vr, (vb, (m, vc)))))))))) =
  vr ++ Rule_Map.rules_with id m;

r :: forall a b.
       (Compare.Compare_order a) => Dpp a b -> [(Term.Term a b, Term.Term a b)];
r d = r_impl (impl_of d);

pw_impl ::
  forall a b.
    (Bool,
      (Bool,
        ([(Term.Term a b, Term.Term a b)],
          ([(Term.Term a b, Term.Term a b)],
            ([Term.Term a b],
              (Bool,
                (Bool,
                  ([(Term.Term a b, Term.Term a b)],
                    ([(Term.Term a b, Term.Term a b)],
                      (RBT.Rbt (a, Arith.Nat)
                         [(Bool, (Term.Term a b, Term.Term a b))],
                        (RBT.Rbt (a, Arith.Nat)
                           [(Bool, (Term.Term a b, Term.Term a b))],
                          (Bool, Term.Term a b -> Bool)))))))))))) ->
      [(Term.Term a b, Term.Term a b)];
pw_impl (uu, (uv, (uw, (pw, ux)))) = pw;

pw :: forall a b.
        (Compare.Compare_order a) => Dpp a b ->
                                       [(Term.Term a b, Term.Term a b)];
pw d = pw_impl (impl_of d);

rw_impl ::
  forall a b.
    (Compare.Compare_order a) => (Bool,
                                   (Bool,
                                     ([(Term.Term a b, Term.Term a b)],
                                       ([(Term.Term a b, Term.Term a b)],
 ([Term.Term a b],
   (Bool,
     (Bool,
       ([(Term.Term a b, Term.Term a b)],
         ([(Term.Term a b, Term.Term a b)],
           (RBT.Rbt (a, Arith.Nat) [(Bool, (Term.Term a b, Term.Term a b))],
             (RBT.Rbt (a, Arith.Nat) [(Bool, (Term.Term a b, Term.Term a b))],
               (Bool, Term.Term a b -> Bool)))))))))))) ->
                                   [(Term.Term a b, Term.Term a b)];
rw_impl (uu, (uv, (uw, (ux, (uy, (uz, (va, (vb, (vrw, (m, vc)))))))))) =
  vrw ++ Rule_Map.rules_with not m;

rw :: forall a b.
        (Compare.Compare_order a) => Dpp a b ->
                                       [(Term.Term a b, Term.Term a b)];
rw d = rw_impl (impl_of d);

mk_impl ::
  forall a b.
    (Compare.Compare_order a, Eq a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b) => Bool ->
Bool ->
  [(Term.Term a b, Term.Term a b)] ->
    [(Term.Term a b, Term.Term a b)] ->
      [Term.Term a b] ->
        [(Term.Term a b, Term.Term a b)] ->
          [(Term.Term a b, Term.Term a b)] ->
            (Bool,
              (Bool,
                ([(Term.Term a b, Term.Term a b)],
                  ([(Term.Term a b, Term.Term a b)],
                    ([Term.Term a b],
                      (Bool,
                        (Bool,
                          ([(Term.Term a b, Term.Term a b)],
                            ([(Term.Term a b, Term.Term a b)],
                              (RBT.Rbt (a, Arith.Nat)
                                 [(Bool, (Term.Term a b, Term.Term a b))],
                                (RBT.Rbt (a, Arith.Nat)
                                   [(Bool, (Term.Term a b, Term.Term a b))],
                                  (Bool, Term.Term a b -> Bool))))))))))));
mk_impl nfs mi p pw q r rw =
  (case List.partition (Term.is_Var . fst) r of {
    (vr, ra) ->
      (case List.partition (Term.is_Var . fst) rw of {
        (vrw, rwa) ->
          let {
            rs = r ++ rw;
            isnf = Trs_Impl.is_NF_terms q;
          } in (nfs, (mi, (p, (pw, (q, (Q_Restricted_Rewriting_Impl.is_NF_trs_subset
  isnf rs,
 (all (\ rb -> not (Term.is_Var (snd rb))) rs,
   (vr, (vrw, (Rule_Map.insert_rules True ra
                 (Rule_Map.insert_rules False rwa RBT.empty),
                (Rule_Map.insert_rules True (Trs_Impl.reverse_rules r)
                   (Rule_Map.insert_rules False (Trs_Impl.reverse_rules rw)
                     RBT.empty),
                  (Q_Restricted_Rewriting_Impl.wwf_qtrs_impl isnf rs,
                    isnf))))))))))));
      });
  });

mk :: forall a b.
        (Compare.Compare_order a, Eq a, Collection_Order.Ccompare b, Eq b,
          Mapping_Impl.Mapping_impl b) => Bool ->
    Bool ->
      [(Term.Term a b, Term.Term a b)] ->
        [(Term.Term a b, Term.Term a b)] ->
          [Term.Term a b] ->
            [(Term.Term a b, Term.Term a b)] ->
              [(Term.Term a b, Term.Term a b)] -> Dpp a b;
mk nfs mi p pw q r rw = DPP (mk_impl nfs mi p pw q r rw);

nfs_impl ::
  forall a b.
    (Bool,
      (Bool,
        ([(Term.Term a b, Term.Term a b)],
          ([(Term.Term a b, Term.Term a b)],
            ([Term.Term a b],
              (Bool,
                (Bool,
                  ([(Term.Term a b, Term.Term a b)],
                    ([(Term.Term a b, Term.Term a b)],
                      (RBT.Rbt (a, Arith.Nat)
                         [(Bool, (Term.Term a b, Term.Term a b))],
                        (RBT.Rbt (a, Arith.Nat)
                           [(Bool, (Term.Term a b, Term.Term a b))],
                          (Bool, Term.Term a b -> Bool)))))))))))) ->
      Bool;
nfs_impl (nfs, uu) = nfs;

nfs :: forall a b. (Compare.Compare_order a) => Dpp a b -> Bool;
nfs d = nfs_impl (impl_of d);

dpp_impl ::
  forall a b.
    (Compare.Compare_order a, Eq a, Compare.Compare b,
      Eq b) => (Bool,
                 (Bool,
                   ([(Term.Term a b, Term.Term a b)],
                     ([(Term.Term a b, Term.Term a b)],
                       ([Term.Term a b],
                         (Bool,
                           (Bool,
                             ([(Term.Term a b, Term.Term a b)],
                               ([(Term.Term a b, Term.Term a b)],
                                 (RBT.Rbt (a, Arith.Nat)
                                    [(Bool, (Term.Term a b, Term.Term a b))],
                                   (RBT.Rbt (a, Arith.Nat)
                                      [(Bool, (Term.Term a b, Term.Term a b))],
                                     (Bool, Term.Term a b -> Bool)))))))))))) ->
                 (Bool,
                   (Bool,
                     (Set.Set (Term.Term a b, Term.Term a b),
                       (Set.Set (Term.Term a b, Term.Term a b),
                         (Set.Set (Term.Term a b),
                           (Set.Set (Term.Term a b, Term.Term a b),
                             Set.Set (Term.Term a b, Term.Term a b)))))));
dpp_impl (nfs, (mi, (p, (pw, (q, (uu, (uv, (vr, (vrw, (m, uw)))))))))) =
  (nfs, (mi, (List.set p,
               (List.set pw,
                 (List.set q,
                   (List.set (vr ++ Rule_Map.rules_with id m),
                     List.set (vrw ++ Rule_Map.rules_with not m)))))));

dpp ::
  forall a b.
    (Compare.Compare_order a, Eq a, Compare.Compare b,
      Eq b) => Dpp a b ->
                 (Bool,
                   (Bool,
                     (Set.Set (Term.Term a b, Term.Term a b),
                       (Set.Set (Term.Term a b, Term.Term a b),
                         (Set.Set (Term.Term a b),
                           (Set.Set (Term.Term a b, Term.Term a b),
                             Set.Set (Term.Term a b, Term.Term a b)))))));
dpp d = dpp_impl (impl_of d);

pairs_impl ::
  forall a b.
    (Bool,
      (Bool,
        ([(Term.Term a b, Term.Term a b)],
          ([(Term.Term a b, Term.Term a b)],
            ([Term.Term a b],
              (Bool,
                (Bool,
                  ([(Term.Term a b, Term.Term a b)],
                    ([(Term.Term a b, Term.Term a b)],
                      (RBT.Rbt (a, Arith.Nat)
                         [(Bool, (Term.Term a b, Term.Term a b))],
                        (RBT.Rbt (a, Arith.Nat)
                           [(Bool, (Term.Term a b, Term.Term a b))],
                          (Bool, Term.Term a b -> Bool)))))))))))) ->
      [(Term.Term a b, Term.Term a b)];
pairs_impl (uu, (uv, (p, (pw, uw)))) = p ++ pw;

pairs ::
  forall a b.
    (Compare.Compare_order a) => Dpp a b -> [(Term.Term a b, Term.Term a b)];
pairs d = pairs_impl (impl_of d);

rules_impl ::
  forall a b.
    (Compare.Compare_order a) => (Bool,
                                   (Bool,
                                     ([(Term.Term a b, Term.Term a b)],
                                       ([(Term.Term a b, Term.Term a b)],
 ([Term.Term a b],
   (Bool,
     (Bool,
       ([(Term.Term a b, Term.Term a b)],
         ([(Term.Term a b, Term.Term a b)],
           (RBT.Rbt (a, Arith.Nat) [(Bool, (Term.Term a b, Term.Term a b))],
             (RBT.Rbt (a, Arith.Nat) [(Bool, (Term.Term a b, Term.Term a b))],
               (Bool, Term.Term a b -> Bool)))))))))))) ->
                                   [(Term.Term a b, Term.Term a b)];
rules_impl (uu, (uv, (uw, (ux, (uy, (uz, (va, (vr, (vrw, (m, vb)))))))))) =
  vr ++ vrw ++ map snd (Multimap.values m);

rules ::
  forall a b.
    (Compare.Compare_order a) => Dpp a b -> [(Term.Term a b, Term.Term a b)];
rules d = rules_impl (impl_of d);

is_QNF_impl ::
  forall a b.
    (Bool,
      (Bool,
        ([(Term.Term a b, Term.Term a b)],
          ([(Term.Term a b, Term.Term a b)],
            ([Term.Term a b],
              (Bool,
                (Bool,
                  ([(Term.Term a b, Term.Term a b)],
                    ([(Term.Term a b, Term.Term a b)],
                      (RBT.Rbt (a, Arith.Nat)
                         [(Bool, (Term.Term a b, Term.Term a b))],
                        (RBT.Rbt (a, Arith.Nat)
                           [(Bool, (Term.Term a b, Term.Term a b))],
                          (Bool, Term.Term a b -> Bool)))))))))))) ->
      Term.Term a b -> Bool;
is_QNF_impl
  (uu, (uv, (uw, (ux, (uy, (uz, (va, (vb, (vc, (vd, (ve, (vf, isnf)))))))))))) =
  isnf;

is_QNF ::
  forall a b. (Compare.Compare_order a) => Dpp a b -> Term.Term a b -> Bool;
is_QNF d = is_QNF_impl (impl_of d);

q_empty_impl ::
  forall a b.
    (Bool,
      (Bool,
        ([(Term.Term a b, Term.Term a b)],
          ([(Term.Term a b, Term.Term a b)],
            ([Term.Term a b],
              (Bool,
                (Bool,
                  ([(Term.Term a b, Term.Term a b)],
                    ([(Term.Term a b, Term.Term a b)],
                      (RBT.Rbt (a, Arith.Nat)
                         [(Bool, (Term.Term a b, Term.Term a b))],
                        (RBT.Rbt (a, Arith.Nat)
                           [(Bool, (Term.Term a b, Term.Term a b))],
                          (Bool, Term.Term a b -> Bool)))))))))))) ->
      Bool;
q_empty_impl (uu, (uv, (uw, (ux, (q, uy))))) = null q;

q_empty :: forall a b. (Compare.Compare_order a) => Dpp a b -> Bool;
q_empty d = q_empty_impl (impl_of d);

wwf_rules_impl ::
  forall a b.
    (Bool,
      (Bool,
        ([(Term.Term a b, Term.Term a b)],
          ([(Term.Term a b, Term.Term a b)],
            ([Term.Term a b],
              (Bool,
                (Bool,
                  ([(Term.Term a b, Term.Term a b)],
                    ([(Term.Term a b, Term.Term a b)],
                      (RBT.Rbt (a, Arith.Nat)
                         [(Bool, (Term.Term a b, Term.Term a b))],
                        (RBT.Rbt (a, Arith.Nat)
                           [(Bool, (Term.Term a b, Term.Term a b))],
                          (Bool, Term.Term a b -> Bool)))))))))))) ->
      Bool;
wwf_rules_impl
  (uu, (uv, (uw, (ux, (uy, (uz, (va, (vb, (vc, (vd, (ve, (wwf, vf)))))))))))) =
  wwf;

wwf_rules :: forall a b. (Compare.Compare_order a) => Dpp a b -> Bool;
wwf_rules d = wwf_rules_impl (impl_of d);

rules_map_impl ::
  forall a b.
    (Compare.Compare_order a) => (Bool,
                                   (Bool,
                                     ([(Term.Term a b, Term.Term a b)],
                                       ([(Term.Term a b, Term.Term a b)],
 ([Term.Term a b],
   (Bool,
     (Bool,
       ([(Term.Term a b, Term.Term a b)],
         ([(Term.Term a b, Term.Term a b)],
           (RBT.Rbt (a, Arith.Nat) [(Bool, (Term.Term a b, Term.Term a b))],
             (RBT.Rbt (a, Arith.Nat) [(Bool, (Term.Term a b, Term.Term a b))],
               (Bool, Term.Term a b -> Bool)))))))))))) ->
                                   (a, Arith.Nat) ->
                                     [(Term.Term a b, Term.Term a b)];
rules_map_impl (uu, (uv, (uw, (ux, (uy, (uz, (va, (vb, (vc, (m, vd)))))))))) fn
  = (case RBT.lookup m fn of {
      Nothing -> [];
      Just a -> map snd a;
    });

rules_map ::
  forall a b.
    (Compare.Compare_order a) => Dpp a b ->
                                   (a, Arith.Nat) ->
                                     [(Term.Term a b, Term.Term a b)];
rules_map d = rules_map_impl (impl_of d);

delete_P_Pw_impl ::
  forall a b.
    (Eq a,
      Eq b) => (Bool,
                 (Bool,
                   ([(Term.Term a b, Term.Term a b)],
                     ([(Term.Term a b, Term.Term a b)],
                       ([Term.Term a b],
                         (Bool,
                           (Bool,
                             ([(Term.Term a b, Term.Term a b)],
                               ([(Term.Term a b, Term.Term a b)],
                                 (RBT.Rbt (a, Arith.Nat)
                                    [(Bool, (Term.Term a b, Term.Term a b))],
                                   (RBT.Rbt (a, Arith.Nat)
                                      [(Bool, (Term.Term a b, Term.Term a b))],
                                     (Bool, Term.Term a b -> Bool)))))))))))) ->
                 [(Term.Term a b, Term.Term a b)] ->
                   [(Term.Term a b, Term.Term a b)] ->
                     (Bool,
                       (Bool,
                         ([(Term.Term a b, Term.Term a b)],
                           ([(Term.Term a b, Term.Term a b)],
                             ([Term.Term a b],
                               (Bool,
                                 (Bool,
                                   ([(Term.Term a b, Term.Term a b)],
                                     ([(Term.Term a b, Term.Term a b)],
                                       (RBT.Rbt (a, Arith.Nat)
  [(Bool, (Term.Term a b, Term.Term a b))],
 (RBT.Rbt (a, Arith.Nat) [(Bool, (Term.Term a b, Term.Term a b))],
   (Bool, Term.Term a b -> Bool))))))))))));
delete_P_Pw_impl (nfs, (mi, (p, (pw, rest)))) pd pwd =
  (nfs, (mi, (Missing_List.list_diff p pd,
               (Missing_List.list_diff pw pwd, rest))));

delete_P_Pw ::
  forall a b.
    (Compare.Compare_order a, Eq a,
      Eq b) => Dpp a b ->
                 [(Term.Term a b, Term.Term a b)] ->
                   [(Term.Term a b, Term.Term a b)] -> Dpp a b;
delete_P_Pw d p pw = DPP (delete_P_Pw_impl (impl_of d) p pw);

delete_R_Rw_impl ::
  forall a b.
    (Compare.Compare_order a, Eq a,
      Eq b) => (Bool,
                 (Bool,
                   ([(Term.Term a b, Term.Term a b)],
                     ([(Term.Term a b, Term.Term a b)],
                       ([Term.Term a b],
                         (Bool,
                           (Bool,
                             ([(Term.Term a b, Term.Term a b)],
                               ([(Term.Term a b, Term.Term a b)],
                                 (RBT.Rbt (a, Arith.Nat)
                                    [(Bool, (Term.Term a b, Term.Term a b))],
                                   (RBT.Rbt (a, Arith.Nat)
                                      [(Bool, (Term.Term a b, Term.Term a b))],
                                     (Bool, Term.Term a b -> Bool)))))))))))) ->
                 [(Term.Term a b, Term.Term a b)] ->
                   [(Term.Term a b, Term.Term a b)] ->
                     (Bool,
                       (Bool,
                         ([(Term.Term a b, Term.Term a b)],
                           ([(Term.Term a b, Term.Term a b)],
                             ([Term.Term a b],
                               (Bool,
                                 (Bool,
                                   ([(Term.Term a b, Term.Term a b)],
                                     ([(Term.Term a b, Term.Term a b)],
                                       (RBT.Rbt (a, Arith.Nat)
  [(Bool, (Term.Term a b, Term.Term a b))],
 (RBT.Rbt (a, Arith.Nat) [(Bool, (Term.Term a b, Term.Term a b))],
   (Bool, Term.Term a b -> Bool))))))))))));
delete_R_Rw_impl d r rw =
  (case d of {
    (nfs, (mi, (p, (pw, (q, (nfq, (nc, (vR,
 (vRw, (m, (rm, (wwf, isnf))))))))))))
      -> (case List.partition (Term.is_Var . fst) r of {
           (vr, ra) ->
             (case List.partition (Term.is_Var . fst) rw of {
               (vrw, rwa) ->
                 let {
                   vra = Missing_List.list_diff vR vr;
                   vrwa = Missing_List.list_diff vRw vrw;
                   ma = Rule_Map.delete_rules True ra
                          (Rule_Map.delete_rules False rwa m);
                   rma = Rule_Map.delete_rules True (Trs_Impl.reverse_rules r)
                           (Rule_Map.delete_rules False
                             (Trs_Impl.reverse_rules rw) rm);
                   rs = vra ++ vrwa ++ map snd (Multimap.values ma);
                 } in (nfs, (mi, (p, (pw, (q,
    (nfq || Q_Restricted_Rewriting_Impl.is_NF_trs_subset isnf rs,
      (nc || all (\ rb -> not (Term.is_Var (snd rb))) rs,
        (vra, (vrwa,
                (ma, (rma, (wwf ||
                              Q_Restricted_Rewriting_Impl.wwf_qtrs_impl isnf rs,
                             isnf))))))))))));
             });
         });
  });

delete_R_Rw ::
  forall a b.
    (Compare.Compare_order a, Eq a,
      Eq b) => Dpp a b ->
                 [(Term.Term a b, Term.Term a b)] ->
                   [(Term.Term a b, Term.Term a b)] -> Dpp a b;
delete_R_Rw d r rw = DPP (delete_R_Rw_impl (impl_of d) r rw);

split_pairs_impl ::
  forall a b.
    (Eq a,
      Eq b) => (Bool,
                 (Bool,
                   ([(Term.Term a b, Term.Term a b)],
                     ([(Term.Term a b, Term.Term a b)],
                       ([Term.Term a b],
                         (Bool,
                           (Bool,
                             ([(Term.Term a b, Term.Term a b)],
                               ([(Term.Term a b, Term.Term a b)],
                                 (RBT.Rbt (a, Arith.Nat)
                                    [(Bool, (Term.Term a b, Term.Term a b))],
                                   (RBT.Rbt (a, Arith.Nat)
                                      [(Bool, (Term.Term a b, Term.Term a b))],
                                     (Bool, Term.Term a b -> Bool)))))))))))) ->
                 [(Term.Term a b, Term.Term a b)] ->
                   ([(Term.Term a b, Term.Term a b)],
                     [(Term.Term a b, Term.Term a b)]);
split_pairs_impl d ps = List.partition (List.member ps) (pairs_impl d);

split_pairs ::
  forall a b.
    (Compare.Compare_order a, Eq a,
      Eq b) => Dpp a b ->
                 [(Term.Term a b, Term.Term a b)] ->
                   ([(Term.Term a b, Term.Term a b)],
                     [(Term.Term a b, Term.Term a b)]);
split_pairs d = split_pairs_impl (impl_of d);

split_rules_impl ::
  forall a b.
    (Compare.Compare_order a, Eq a,
      Eq b) => (Bool,
                 (Bool,
                   ([(Term.Term a b, Term.Term a b)],
                     ([(Term.Term a b, Term.Term a b)],
                       ([Term.Term a b],
                         (Bool,
                           (Bool,
                             ([(Term.Term a b, Term.Term a b)],
                               ([(Term.Term a b, Term.Term a b)],
                                 (RBT.Rbt (a, Arith.Nat)
                                    [(Bool, (Term.Term a b, Term.Term a b))],
                                   (RBT.Rbt (a, Arith.Nat)
                                      [(Bool, (Term.Term a b, Term.Term a b))],
                                     (Bool, Term.Term a b -> Bool)))))))))))) ->
                 [(Term.Term a b, Term.Term a b)] ->
                   ([(Term.Term a b, Term.Term a b)],
                     [(Term.Term a b, Term.Term a b)]);
split_rules_impl d rs = List.partition (List.member rs) (rules_impl d);

split_rules ::
  forall a b.
    (Compare.Compare_order a, Eq a,
      Eq b) => Dpp a b ->
                 [(Term.Term a b, Term.Term a b)] ->
                   ([(Term.Term a b, Term.Term a b)],
                     [(Term.Term a b, Term.Term a b)]);
split_rules d = split_rules_impl (impl_of d);

rules_non_collapsing_impl ::
  forall a b.
    (Bool,
      (Bool,
        ([(Term.Term a b, Term.Term a b)],
          ([(Term.Term a b, Term.Term a b)],
            ([Term.Term a b],
              (Bool,
                (Bool,
                  ([(Term.Term a b, Term.Term a b)],
                    ([(Term.Term a b, Term.Term a b)],
                      (RBT.Rbt (a, Arith.Nat)
                         [(Bool, (Term.Term a b, Term.Term a b))],
                        (RBT.Rbt (a, Arith.Nat)
                           [(Bool, (Term.Term a b, Term.Term a b))],
                          (Bool, Term.Term a b -> Bool)))))))))))) ->
      Bool;
rules_non_collapsing_impl (uu, (uv, (uw, (ux, (uy, (uz, (nc, va))))))) = nc;

rules_non_collapsing ::
  forall a b. (Compare.Compare_order a) => Dpp a b -> Bool;
rules_non_collapsing d = rules_non_collapsing_impl (impl_of d);

nFQ_subset_NF_rules_impl ::
  forall a b.
    (Bool,
      (Bool,
        ([(Term.Term a b, Term.Term a b)],
          ([(Term.Term a b, Term.Term a b)],
            ([Term.Term a b],
              (Bool,
                (Bool,
                  ([(Term.Term a b, Term.Term a b)],
                    ([(Term.Term a b, Term.Term a b)],
                      (RBT.Rbt (a, Arith.Nat)
                         [(Bool, (Term.Term a b, Term.Term a b))],
                        (RBT.Rbt (a, Arith.Nat)
                           [(Bool, (Term.Term a b, Term.Term a b))],
                          (Bool, Term.Term a b -> Bool)))))))))))) ->
      Bool;
nFQ_subset_NF_rules_impl (uu, (uv, (uw, (ux, (uy, (b, uz)))))) = b;

nFQ_subset_NF_rules :: forall a b. (Compare.Compare_order a) => Dpp a b -> Bool;
nFQ_subset_NF_rules d = nFQ_subset_NF_rules_impl (impl_of d);

rules_no_left_var_impl ::
  forall a b.
    (Bool,
      (Bool,
        ([(Term.Term a b, Term.Term a b)],
          ([(Term.Term a b, Term.Term a b)],
            ([Term.Term a b],
              (Bool,
                (Bool,
                  ([(Term.Term a b, Term.Term a b)],
                    ([(Term.Term a b, Term.Term a b)],
                      (RBT.Rbt (a, Arith.Nat)
                         [(Bool, (Term.Term a b, Term.Term a b))],
                        (RBT.Rbt (a, Arith.Nat)
                           [(Bool, (Term.Term a b, Term.Term a b))],
                          (Bool, Term.Term a b -> Bool)))))))))))) ->
      Bool;
rules_no_left_var_impl (uu, (uv, (uw, (ux, (uy, (uz, (va, ([], ([], vb)))))))))
  = True;
rules_no_left_var_impl (v, (vb, (ve, (vg, (vi, (vk, (vm, (vq : vr, vp)))))))) =
  False;
rules_no_left_var_impl
  (v, (vb, (ve, (vg, (vi, (vk, (vm, (vo, (vs : vt, vr))))))))) = False;

rules_no_left_var :: forall a b. (Compare.Compare_order a) => Dpp a b -> Bool;
rules_no_left_var d = rules_no_left_var_impl (impl_of d);

reverse_rules_map_impl ::
  forall a b.
    (Compare.Compare_order a) => (Bool,
                                   (Bool,
                                     ([(Term.Term a b, Term.Term a b)],
                                       ([(Term.Term a b, Term.Term a b)],
 ([Term.Term a b],
   (Bool,
     (Bool,
       ([(Term.Term a b, Term.Term a b)],
         ([(Term.Term a b, Term.Term a b)],
           (RBT.Rbt (a, Arith.Nat) [(Bool, (Term.Term a b, Term.Term a b))],
             (RBT.Rbt (a, Arith.Nat) [(Bool, (Term.Term a b, Term.Term a b))],
               (Bool, Term.Term a b -> Bool)))))))))))) ->
                                   (a, Arith.Nat) ->
                                     [(Term.Term a b, Term.Term a b)];
reverse_rules_map_impl
  (uu, (uv, (uw, (ux, (uy, (uz, (va, (vb, (vc, (vd, (m, ve))))))))))) fn =
  (case RBT.lookup m fn of {
    Nothing -> [];
    Just a -> map snd a;
  });

reverse_rules_map ::
  forall a b.
    (Compare.Compare_order a) => Dpp a b ->
                                   (a, Arith.Nat) ->
                                     [(Term.Term a b, Term.Term a b)];
reverse_rules_map d = reverse_rules_map_impl (impl_of d);

intersect_rules_impl ::
  forall a b.
    (Compare.Compare_order a, Eq a,
      Eq b) => (Bool,
                 (Bool,
                   ([(Term.Term a b, Term.Term a b)],
                     ([(Term.Term a b, Term.Term a b)],
                       ([Term.Term a b],
                         (Bool,
                           (Bool,
                             ([(Term.Term a b, Term.Term a b)],
                               ([(Term.Term a b, Term.Term a b)],
                                 (RBT.Rbt (a, Arith.Nat)
                                    [(Bool, (Term.Term a b, Term.Term a b))],
                                   (RBT.Rbt (a, Arith.Nat)
                                      [(Bool, (Term.Term a b, Term.Term a b))],
                                     (Bool, Term.Term a b -> Bool)))))))))))) ->
                 [(Term.Term a b, Term.Term a b)] ->
                   (Bool,
                     (Bool,
                       ([(Term.Term a b, Term.Term a b)],
                         ([(Term.Term a b, Term.Term a b)],
                           ([Term.Term a b],
                             (Bool,
                               (Bool,
                                 ([(Term.Term a b, Term.Term a b)],
                                   ([(Term.Term a b, Term.Term a b)],
                                     (RBT.Rbt (a, Arith.Nat)
[(Bool, (Term.Term a b, Term.Term a b))],
                                       (RBT.Rbt (a, Arith.Nat)
  [(Bool, (Term.Term a b, Term.Term a b))],
 (Bool, Term.Term a b -> Bool))))))))))));
intersect_rules_impl d ri =
  (case d of {
    (nfs, (mi, (p, (pw, (q, (nfq, (nc, (vR,
 (vRw, (m, (rm, (wwf, isnf))))))))))))
      -> (case List.partition (Term.is_Var . fst) ri of {
           (vri, ria) ->
             let {
               vr = List.inter_list_set vR vri;
               vrw = List.inter_list_set vRw vri;
               ma = Rule_Map.intersect_rules ria m;
               rma = Rule_Map.intersect_rules (Trs_Impl.reverse_rules ri) rm;
               rs = vr ++ vrw ++ map snd (Multimap.values ma);
             } in (nfs, (mi, (p, (pw, (q,
(nfq || Q_Restricted_Rewriting_Impl.is_NF_trs_subset isnf rs,
  (nc || all (\ r -> not (Term.is_Var (snd r))) rs,
    (vr, (vrw, (ma, (rma, (wwf ||
                             Q_Restricted_Rewriting_Impl.wwf_qtrs_impl isnf rs,
                            isnf))))))))))));
         });
  });

intersect_rules ::
  forall a b.
    (Compare.Compare_order a, Eq a,
      Eq b) => Dpp a b -> [(Term.Term a b, Term.Term a b)] -> Dpp a b;
intersect_rules d rs = DPP (intersect_rules_impl (impl_of d) rs);

intersect_pairs_impl ::
  forall a b.
    (Eq a,
      Eq b) => (Bool,
                 (Bool,
                   ([(Term.Term a b, Term.Term a b)],
                     ([(Term.Term a b, Term.Term a b)],
                       ([Term.Term a b],
                         (Bool,
                           (Bool,
                             ([(Term.Term a b, Term.Term a b)],
                               ([(Term.Term a b, Term.Term a b)],
                                 (RBT.Rbt (a, Arith.Nat)
                                    [(Bool, (Term.Term a b, Term.Term a b))],
                                   (RBT.Rbt (a, Arith.Nat)
                                      [(Bool, (Term.Term a b, Term.Term a b))],
                                     (Bool, Term.Term a b -> Bool)))))))))))) ->
                 [(Term.Term a b, Term.Term a b)] ->
                   (Bool,
                     (Bool,
                       ([(Term.Term a b, Term.Term a b)],
                         ([(Term.Term a b, Term.Term a b)],
                           ([Term.Term a b],
                             (Bool,
                               (Bool,
                                 ([(Term.Term a b, Term.Term a b)],
                                   ([(Term.Term a b, Term.Term a b)],
                                     (RBT.Rbt (a, Arith.Nat)
[(Bool, (Term.Term a b, Term.Term a b))],
                                       (RBT.Rbt (a, Arith.Nat)
  [(Bool, (Term.Term a b, Term.Term a b))],
 (Bool, Term.Term a b -> Bool))))))))))));
intersect_pairs_impl (nfs, (mi, (p, (pw, rest)))) ps =
  (nfs, (mi, (List.inter_list_set p ps, (List.inter_list_set pw ps, rest))));

intersect_pairs ::
  forall a b.
    (Compare.Compare_order a, Eq a,
      Eq b) => Dpp a b -> [(Term.Term a b, Term.Term a b)] -> Dpp a b;
intersect_pairs d ps = DPP (intersect_pairs_impl (impl_of d) ps);

replace_pair_impl ::
  forall a b.
    (Eq a,
      Eq b) => (Bool,
                 (Bool,
                   ([(Term.Term a b, Term.Term a b)],
                     ([(Term.Term a b, Term.Term a b)],
                       ([Term.Term a b],
                         (Bool,
                           (Bool,
                             ([(Term.Term a b, Term.Term a b)],
                               ([(Term.Term a b, Term.Term a b)],
                                 (RBT.Rbt (a, Arith.Nat)
                                    [(Bool, (Term.Term a b, Term.Term a b))],
                                   (RBT.Rbt (a, Arith.Nat)
                                      [(Bool, (Term.Term a b, Term.Term a b))],
                                     (Bool, Term.Term a b -> Bool)))))))))))) ->
                 (Term.Term a b, Term.Term a b) ->
                   [(Term.Term a b, Term.Term a b)] ->
                     (Bool,
                       (Bool,
                         ([(Term.Term a b, Term.Term a b)],
                           ([(Term.Term a b, Term.Term a b)],
                             ([Term.Term a b],
                               (Bool,
                                 (Bool,
                                   ([(Term.Term a b, Term.Term a b)],
                                     ([(Term.Term a b, Term.Term a b)],
                                       (RBT.Rbt (a, Arith.Nat)
  [(Bool, (Term.Term a b, Term.Term a b))],
 (RBT.Rbt (a, Arith.Nat) [(Bool, (Term.Term a b, Term.Term a b))],
   (Bool, Term.Term a b -> Bool))))))))))));
replace_pair_impl (nfs, (mi, (p, (pw, rest)))) pair ps =
  (nfs, (mi, (Util.replace_impl pair ps p,
               (Util.replace_impl pair ps pw, rest))));

replace_pair ::
  forall a b.
    (Compare.Compare_order a, Eq a,
      Eq b) => Dpp a b ->
                 (Term.Term a b, Term.Term a b) ->
                   [(Term.Term a b, Term.Term a b)] -> Dpp a b;
replace_pair d pair ps = DPP (replace_pair_impl (impl_of d) pair ps);

dpp_rbt_impl ::
  forall a b.
    (Compare.Compare_order a, Eq a, Collection_Order.Ccompare b,
      Compare.Compare b, Eq b,
      Mapping_Impl.Mapping_impl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext
(Dpp a b) a b ();
dpp_rbt_impl =
  Dependency_Pair_Problem_Spec.Dpp_ops_ext dpp p pw pairs q r rw rules q_empty
    rules_no_left_var rules_non_collapsing is_QNF nFQ_subset_NF_rules rules_map
    reverse_rules_map intersect_pairs replace_pair intersect_rules delete_P_Pw
    delete_R_Rw split_pairs split_rules mk m nfs wwf_rules ();

}
