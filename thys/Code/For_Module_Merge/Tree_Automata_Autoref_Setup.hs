{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Tree_Automata_Autoref_Setup(comparator_ta_rule, compare_ta_rule, compare_res,
                               ta_det_impl, ta_eps_impl, ta_idx_impl,
                               memo_rtrancl, ta_make_code, ta_final_impl,
                               ta_rules_impl, ta_eps_cl_impl, ta_eps_icl_impl,
                               subst_apply_term, ta_rhs_states_impl,
                               union_image_rs_code)
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
import qualified RBT_Comparator_Impl;
import qualified SetIteratorOperations;
import qualified RBT_add;
import qualified Compare_Instances;
import qualified Term;
import qualified Transitive_Closure_RBT_Impl;
import qualified Product_Type;
import qualified Autoref_Bindings_HOL;
import qualified Impl_List_Set;
import qualified Gen_Set;
import qualified Foldi;
import qualified HOL;
import qualified RBT_Impl;
import qualified RBT;
import qualified Arith;
import qualified Tree_Automata_Det_Container;
import qualified Option;
import qualified RBT_Set2;
import qualified RBT_Mapping2;
import qualified DList_Set;
import qualified Set;
import qualified Set_Impl;
import qualified Collection_Order;
import qualified Collection_Eq;
import qualified Intf_Comp;
import qualified Comparator;
import qualified Quasi_Order;
import qualified Tree_Automata;
import qualified Compare;
import qualified Orderings;

comparator_ta_rule ::
  forall a b.
    (a -> a -> Comparator.Order) ->
      (b -> b -> Comparator.Order) ->
        Tree_Automata.Ta_rule a b ->
          Tree_Automata.Ta_rule a b -> Comparator.Order;
comparator_ta_rule comp_q comp_f (Tree_Automata.TA_rule x xa xb)
  (Tree_Automata.TA_rule y ya yb) =
  (case comp_f x y of {
    Comparator.Eqa -> (case Compare_Instances.comparator_list comp_q xa ya of {
                        Comparator.Eqa -> comp_q xb yb;
                        Comparator.Lt -> Comparator.Lt;
                        Comparator.Gt -> Comparator.Gt;
                      });
    Comparator.Lt -> Comparator.Lt;
    Comparator.Gt -> Comparator.Gt;
  });

compare_ta_rule ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => Tree_Automata.Ta_rule a b ->
                              Tree_Automata.Ta_rule a b -> Comparator.Order;
compare_ta_rule = comparator_ta_rule Compare.compare Compare.compare;

less_eq_ta_rule ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => Tree_Automata.Ta_rule a b ->
                              Tree_Automata.Ta_rule a b -> Bool;
less_eq_ta_rule = Comparator.le_of_comp compare_ta_rule;

less_ta_rule ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => Tree_Automata.Ta_rule a b ->
                              Tree_Automata.Ta_rule a b -> Bool;
less_ta_rule = Comparator.lt_of_comp compare_ta_rule;

instance (Compare.Compare a,
           Compare.Compare b) => Orderings.Ord (Tree_Automata.Ta_rule a
         b) where {
  less_eq = less_eq_ta_rule;
  less = less_ta_rule;
};

instance (Compare.Compare a,
           Compare.Compare b) => Quasi_Order.Quasi_order (Tree_Automata.Ta_rule
                   a b) where {
};

instance (Compare.Compare a,
           Compare.Compare b) => Quasi_Order.Weak_order (Tree_Automata.Ta_rule a
                  b) where {
};

instance (Compare.Compare a,
           Compare.Compare b) => Orderings.Preorder (Tree_Automata.Ta_rule a
              b) where {
};

instance (Compare.Compare a,
           Compare.Compare b) => Orderings.Order (Tree_Automata.Ta_rule a
           b) where {
};

instance (Compare.Compare a,
           Compare.Compare b) => Orderings.Linorder (Tree_Automata.Ta_rule a
              b) where {
};

comp_res_of_order :: Comparator.Order -> Intf_Comp.Comp_res;
comp_res_of_order Comparator.Eqa = Intf_Comp.EQUAL;
comp_res_of_order Comparator.Lt = Intf_Comp.LESS;
comp_res_of_order Comparator.Gt = Intf_Comp.GREATER;

compare_res :: forall a. (Compare.Compare a) => a -> a -> Intf_Comp.Comp_res;
compare_res x y = comp_res_of_order (Compare.compare x y);

ta_det_impl :: forall a b c d e f g. (a, (b, (c, (d, (e, (f, g)))))) -> f;
ta_det_impl (f, (r, (e, (rhs, (idx, (det, x)))))) = det;

ta_eps_impl ::
  forall a b c d e f g h. (a, (b, (c, (d, (e, (f, (g, h))))))) -> c;
ta_eps_impl (f, (r, (e, (rhs, (idx, (det, (efcl, eicl))))))) = e;

ta_idx_impl ::
  forall a b c d e f g h. (a, (b, (c, (d, (e, (f, (g, h))))))) -> e;
ta_idx_impl (f, (r, (e, (rhs, (idx, (det, (efcl, eicl))))))) = idx;

memo_rtrancl ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Eq a,
      Set_Impl.Set_impl a) => Set.Set (a, a) -> a -> Set.Set a;
memo_rtrancl (Set.Set_Monad xs) =
  Tree_Automata_Det_Container.memo_list_rtrancl_set xs;
memo_rtrancl (Set.DList_set dxs) =
  (case (Collection_Eq.ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "memo_rtrancl DList_set: ceq = None"
        (\ _ -> memo_rtrancl (Set.DList_set dxs));
    Just _ ->
      Tree_Automata_Det_Container.memo_list_rtrancl_set
        (DList_Set.list_of_dlist dxs);
  });
memo_rtrancl (Set.RBT_set rbt) =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "memo_rtrancl RBT_set: ccompare = None"
        (\ _ -> memo_rtrancl (Set.RBT_set rbt));
    Just _ ->
      Tree_Automata_Det_Container.memo_list_rtrancl_set (RBT_Set2.keys rbt);
  });

ta_idx_rhs_init_code ::
  forall a b c.
    (Compare.Compare a, Compare.Compare b,
      Compare.Compare c) => Bool ->
                              RBT_Impl.Rbt (Tree_Automata.Ta_rule a b) () ->
                                (a -> RBT_Impl.Rbt c ()) ->
                                  (RBT_Impl.Rbt (b, Arith.Nat)
                                     (RBT_Impl.Rbt ([a], a) ()),
                                    (Bool, RBT_Impl.Rbt c ()));
ta_idx_rhs_init_code det rs efcl =
  (SetIteratorOperations.map_iterator_dom . RBT_add.rm_iterateoi) rs
    (\ _ -> True)
    (\ x (a, (aa, ba)) ->
      (case x of {
        Tree_Automata.TA_rule xg xh xi ->
          let {
            y = List.size_list xh;
          } in (case RBT_Comparator_Impl.rbt_comp_lookup
                       Compare_Instances.compare_prod a (xg, y)
                 of {
                 Nothing ->
                   (RBT_Comparator_Impl.rbt_comp_insert
                      Compare_Instances.compare_prod (xg, y)
                      (RBT_Comparator_Impl.rbt_comp_insert
                        Compare_Instances.compare_prod (xh, xi) ()
                        RBT_Impl.Empty)
                      a,
                     (aa, RBT_Comparator_Impl.rbt_comp_union_with_key
                            Compare.compare (\ _ _ rv -> rv) (efcl xi) ba));
                 Just xj ->
                   (RBT_Comparator_Impl.rbt_comp_insert
                      Compare_Instances.compare_prod (xg, y)
                      (RBT_Comparator_Impl.rbt_comp_insert
                        Compare_Instances.compare_prod (xh, xi) () xj)
                      a,
                     ((if aa
                        then Gen_Set.gen_ball
                               (SetIteratorOperations.map_iterator_dom .
                                 RBT_add.rm_iterateoi)
                               xj (\ (xk, _) ->
                                    not (Autoref_Bindings_HOL.list_eq
  (Intf_Comp.comp2eq compare_res) xh xk))
                        else False),
                       RBT_Comparator_Impl.rbt_comp_union_with_key
                         Compare.compare (\ _ _ rv -> rv) (efcl xi) ba));
               });
      }))
    (RBT_Impl.Empty, (det, RBT_Impl.Empty));

ta_make_code ::
  forall a b c.
    (Compare.Compare a, Compare.Compare_order b,
      Compare.Compare c) => RBT_Impl.Rbt a () ->
                              RBT_Impl.Rbt (Tree_Automata.Ta_rule b c) () ->
                                [(b, b)] ->
                                  (RBT_Impl.Rbt a (),
                                    (RBT_Impl.Rbt (Tree_Automata.Ta_rule b c)
                                       (),
                                      ([(b, b)],
(RBT_Impl.Rbt b (),
  (RBT_Impl.Rbt (c, Arith.Nat) (RBT_Impl.Rbt ([b], b) ()),
    (Bool, (b -> RBT_Impl.Rbt b (), b -> RBT_Impl.Rbt b ())))))));
ta_make_code f r e =
  (case ta_idx_rhs_init_code (Autoref_Bindings_HOL.is_Nil e) r
          (\ xi ->
            RBT.impl_of (Transitive_Closure_RBT_Impl.memo_rbt_rtrancl e xi))
    of {
    (a, (aa, ba)) ->
      (f, (r, (e, (ba, (a, (aa, ((\ s ->
                                   RBT.impl_of
                                     (Transitive_Closure_RBT_Impl.memo_rbt_rtrancl
                                       e s)),
                                  (\ s ->
                                    RBT.impl_of
                                      (Transitive_Closure_RBT_Impl.memo_rbt_rtrancl
(Gen_Set.gen_image Foldi.foldli []
  (Impl_List_Set.glist_insert
    (Autoref_Bindings_HOL.prod_eq (Intf_Comp.comp2eq compare_res)
      (Intf_Comp.comp2eq compare_res)))
  (\ xc -> (snd xc, fst xc)) e)
s)))))))));
  });

ta_final_impl ::
  forall a b c d e f g h. (a, (b, (c, (d, (e, (f, (g, h))))))) -> a;
ta_final_impl (f, (r, (e, (rhs, (idx, (det, (efcl, eicl))))))) = f;

ta_rules_impl ::
  forall a b c d e f g h. (a, (b, (c, (d, (e, (f, (g, h))))))) -> b;
ta_rules_impl (f, (r, (e, (rhs, (idx, (det, (efcl, eicl))))))) = r;

ta_eps_cl_impl ::
  forall a b c d e f g h i. (a, (b, (c, (d, (e, (f, (g -> h, i))))))) -> g -> h;
ta_eps_cl_impl (f, (r, (e, (rhs, (idx, (det, (efcl, eicl))))))) q = efcl q;

ta_eps_icl_impl ::
  forall a b c d e f g h i. (a, (b, (c, (d, (e, (f, (g, h -> i))))))) -> h -> i;
ta_eps_icl_impl (f, (r, (e, (rhs, (idx, (det, (efcl, eicl))))))) q = eicl q;

subst_apply_term ::
  forall a b c. Term.Term a b -> (b -> Term.Term a c) -> Term.Term a c;
subst_apply_term = Term.eval_term Term.Fun;

ta_rhs_states_impl ::
  forall a b c d e f g h. (a, (b, (c, (d, (e, (f, (g, h))))))) -> d;
ta_rhs_states_impl (f, (r, (e, (rhs, (idx, (det, (efcl, eicl))))))) = rhs;

union_image_rs_code ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => RBT_Impl.Rbt a () ->
                              (a -> RBT_Impl.Rbt b ()) -> RBT_Impl.Rbt b ();
union_image_rs_code s f =
  (SetIteratorOperations.map_iterator_dom . RBT_add.rm_iterateoi) s
    (\ _ -> True)
    (\ x ->
      RBT_Comparator_Impl.rbt_comp_union_with_key Compare.compare
        (\ _ _ rv -> rv) (f x))
    RBT_Impl.Empty;

}
