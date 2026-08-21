{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Tree_Automata_Containment_Impl(ta_lang_containment_impl) where {

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
import qualified Transitive_Closure_RBT_Impl;
import qualified SetIteratorOperations;
import qualified Autoref_Bindings_HOL;
import qualified Impl_List_Set;
import qualified Refine_Transfer;
import qualified RBT_add;
import qualified Gen_Set;
import qualified Foldi;
import qualified HOL;
import qualified Tree_Automata_Containment;
import qualified Intf_Comp;
import qualified Comparator;
import qualified Refine_Det;
import qualified RBT;
import qualified Compare;
import qualified Term_Rewriting;
import qualified Arith;

key_of_entry :: forall a b c d. (Arith.Rbt a b, Arith.Rbt c d) -> ([a], [c]);
key_of_entry (aa, a) = (Arith.keys aa, Arith.keys a);

ta_lang_containment_impl ::
  forall a b c.
    (Compare.Compare_order a,
      Compare.Compare_order b) => (Arith.Rbt a (),
                                    (Arith.Rbt (Term_Rewriting.Ta_rule a b) (),
                                      ([(a, a)],
(Arith.Rbt a (),
  (Arith.Rbt (b, Arith.Nat) (Arith.Rbt ([a], a) ()),
    (Bool, (a -> Arith.Rbt a (), a -> Arith.Rbt a ()))))))) ->
                                    (Arith.Rbt a (),
                                      (Arith.Rbt (Term_Rewriting.Ta_rule a b)
 (),
([(a, a)],
  (Arith.Rbt a (),
    (Arith.Rbt (b, Arith.Nat) (Arith.Rbt ([a], a) ()),
      (Bool, (a -> Arith.Rbt a (), a -> Arith.Rbt a ()))))))) ->
                                      Tree_Automata_Containment.Xoption
(Term_Rewriting.Term b c);
ta_lang_containment_impl a b =
  Refine_Transfer.the_res
    (let {
       x = Arith.Empty;
       _ = Term_Rewriting.ta_final_impl a;
       _ = Term_Rewriting.ta_final_impl b;
       xc = Gen_Set.gen_image
              (SetIteratorOperations.map_iterator_dom . RBT_add.rm_iterateoi) []
              (Impl_List_Set.glist_insert
                (Autoref_Bindings_HOL.prod_eq
                  (Intf_Comp.comp2eq Term_Rewriting.compare_res)
                  Arith.equal_nat))
              Term_Rewriting.r_sym (Term_Rewriting.ta_rules_impl a);
     } in Refine_Det.dbind
            (Refine_Det.dWHILET
              (\ xb -> Tree_Automata_Containment.is_busy (snd xb))
              (\ (aa, _) ->
                Refine_Det.dbind
                  (Foldi.foldli xc
                    (\ ab ->
                      (case ab of {
                        Refine_Det.DSUCCEEDi -> False;
                        Refine_Det.DFAILi -> False;
                        Refine_Det.DRETURN xe ->
                          Tree_Automata_Containment.is_busy (snd xe);
                      }))
                    (\ xa s ->
                      Refine_Det.dbind s
                        (\ sigma ->
                          (case xa of {
                            (aaa, ba) ->
                              (case sigma of {
                                (ab, bb) ->
                                  Foldi.foldli
                                    (Arith.product_lists
                                      (Arith.replicate ba (Arith.entries aa)))
                                    (\ ac ->
                                      (case ac of {
Refine_Det.DSUCCEEDi -> False;
Refine_Det.DFAILi -> False;
Refine_Det.DRETURN xg -> Tree_Automata_Containment.is_busy (snd xg);
                                      }))
                                    (\ xb sa ->
                                      Refine_Det.dbind sa
(\ (ac, bc) ->
  let {
    xh = map ((fst . id) . fst) xb;
    xi = let {
           y = (\ sb ->
                 RBT.impl_of
                   (Transitive_Closure_RBT_Impl.memo_rbt_rtrancl
                     (Term_Rewriting.ta_eps_impl a) sb));
         } in (\ xaa xba ->
                Term_Rewriting.union_image_rs_code
                  (Gen_Set.gen_filter
                    (SetIteratorOperations.map_iterator_dom .
                      RBT_add.rm_iterateoi)
                    Arith.Empty
                    (\ k ->
                      Arith.rbt_comp_insert Term_Rewriting.compare_ta_rule k ())
                    (\ xca ->
                      Intf_Comp.comp2eq Term_Rewriting.compare_res
                        (Term_Rewriting.r_root xca) xba &&
                        Arith.list_all2
                          (\ k sb ->
                            (case Arith.rbt_comp_lookup Compare.compare sb k of
                              {
                              Nothing -> False;
                              Just _ -> True;
                            }))
                          (Term_Rewriting.r_lhs_states xca) xaa)
                    (Term_Rewriting.ta_rules_impl a))
                  (y . Term_Rewriting.r_rhs))
           xh
           aaa;
  } in (if Gen_Set.gen_isEmpty
             (Gen_Set.gen_ball
               (SetIteratorOperations.map_iterator_dom . RBT_add.rm_iterateoi))
             xi
         then Refine_Det.DRETURN (ac, bc)
         else let {
                xj = map ((snd . id) . fst) xb;
                xk = let {
                       y = (\ sb ->
                             RBT.impl_of
                               (Transitive_Closure_RBT_Impl.memo_rbt_rtrancl
                                 (Term_Rewriting.ta_eps_impl b) sb));
                     } in (\ xaa xba ->
                            Term_Rewriting.union_image_rs_code
                              (Gen_Set.gen_filter
                                (SetIteratorOperations.map_iterator_dom .
                                  RBT_add.rm_iterateoi)
                                Arith.Empty
                                (\ k ->
                                  Arith.rbt_comp_insert
                                    Term_Rewriting.compare_ta_rule k ())
                                (\ xca ->
                                  Intf_Comp.comp2eq Term_Rewriting.compare_res
                                    (Term_Rewriting.r_root xca) xba &&
                                    Arith.list_all2
                                      (\ k sb ->
(case Arith.rbt_comp_lookup Compare.compare sb k of {
  Nothing -> False;
  Just _ -> True;
}))
                                      (Term_Rewriting.r_lhs_states xca) xaa)
                                (Term_Rewriting.ta_rules_impl b))
                              (y . Term_Rewriting.r_rhs))
                       xj
                       aaa;
                xl = Term_Rewriting.Fun aaa (map snd xb);
              } in (if (case Arith.rbt_lookup
                               (Intf_Comp.comp2lt
                                 (\ ad bd ->
                                   Term_Rewriting.compare_res (key_of_entry ad)
                                     (key_of_entry bd)))
                               (Arith.mapa (\ _ _ -> ()) ac) (id (xi, xk))
                         of {
                         Nothing -> False;
                         Just _ -> True;
                       })
                     then Refine_Det.DRETURN (ac, bc)
                     else (if id (\ (xja, xka) ->
                                   not (Gen_Set.gen_disjoint
 (SetIteratorOperations.map_iterator_dom . RBT_add.rm_iterateoi)
 (\ k sb -> (case Arith.rbt_comp_lookup Compare.compare sb k of {
              Nothing -> False;
              Just _ -> True;
            }))
 xja (Term_Rewriting.ta_final_impl a)) &&
                                     Gen_Set.gen_disjoint
                                       (SetIteratorOperations.map_iterator_dom .
 RBT_add.rm_iterateoi)
                                       (\ k sb ->
 (case Arith.rbt_comp_lookup Compare.compare sb k of {
   Nothing -> False;
   Just _ -> True;
 }))
                                       xka (Term_Rewriting.ta_final_impl b))
                                (id (xi, xk))
                            then Refine_Det.DRETURN
                                   (Arith.rbt_insert
                                      (Intf_Comp.comp2lt
(\ ad bd -> Term_Rewriting.compare_res (key_of_entry ad) (key_of_entry bd)))
                                      (id (xi, xk)) xl ac,
                                     Tree_Automata_Containment.Done
                                       (Tree_Automata_Containment.XSome xl))
                            else Refine_Det.DRETURN
                                   (Arith.rbt_insert
                                      (Intf_Comp.comp2lt
(\ ad bd -> Term_Rewriting.compare_res (key_of_entry ad) (key_of_entry bd)))
                                      (id (xi, xk)) xl ac,
                                     Tree_Automata_Containment.Changed))))))
                                    (Refine_Det.DRETURN (ab, bb));
                              });
                          })))
                    (Refine_Det.DRETURN
                      (aa, Tree_Automata_Containment.Unchanged)))
                  (\ xe ->
                    Refine_Det.DRETURN
                      (case xe of {
                        (_, Tree_Automata_Containment.Done _) -> xe;
                        (_, Tree_Automata_Containment.Changed) -> xe;
                        (xf, Tree_Automata_Containment.Unchanged) ->
                          (xf, Tree_Automata_Containment.Done
                                 Tree_Automata_Containment.XNone);
                      })))
              (x, Tree_Automata_Containment.Changed))
            (\ xd ->
              Refine_Det.DRETURN
                (Tree_Automata_Containment.map_xoption Term_Rewriting.adapt_vars
                  (Tree_Automata_Containment.status_result (snd xd)))));

}
