{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Tree_Automata_Wit_Impl(Ta_code, det, make_ls, check_comcoh_wit_ls)
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
import qualified RBTSetImpl;
import qualified Compare_Order_Instances;
import qualified RBT;
import qualified Product_Lexorder;
import qualified Term_Impl;
import qualified Gen_Map;
import qualified Foldi;
import qualified Param_HOL;
import qualified Util;
import qualified Sum_Type;
import qualified Option_Monad;
import qualified Autoref_Bindings_HOL;
import qualified Impl_List_Set;
import qualified Intf_Comp;
import qualified Gen_Set;
import qualified While_Combinator;
import qualified List;
import qualified Subterm_and_Context;
import qualified Product_Type;
import qualified Option;
import qualified Compare_Instances;
import qualified SetIteratorOperations;
import qualified RBT_Comparator_Impl;
import qualified RBT_add;
import qualified Comparator;
import qualified HOL;
import qualified Term;
import qualified Tree_Automata_Autoref_Setup;
import qualified Tree_Automata;
import qualified RBT_Impl;
import qualified Arith;
import qualified Compare;

newtype Ta_code b a = Abs_ta_code
  (RBT_Impl.Rbt b (),
    (RBT_Impl.Rbt (Tree_Automata.Ta_rule b a) (),
      ([(b, b)],
        (RBT_Impl.Rbt b (),
          (RBT_Impl.Rbt (a, Arith.Nat) (RBT_Impl.Rbt ([b], b) ()),
            (Bool, (b -> RBT_Impl.Rbt b (), b -> RBT_Impl.Rbt b ())))))));

map2 :: forall a b c. (a -> b -> c) -> [a] -> [b] -> [c];
map2 f [] ys = [];
map2 f (v : va) [] = [];
map2 f (x : xs) (y : ys) = f x y : map2 f xs ys;

rep_ta_code ::
  forall b a.
    (Compare.Compare_order b,
      Compare.Compare_order a) => Ta_code b a ->
                                    (RBT_Impl.Rbt b (),
                                      (RBT_Impl.Rbt (Tree_Automata.Ta_rule b a)
 (),
([(b, b)],
  (RBT_Impl.Rbt b (),
    (RBT_Impl.Rbt (a, Arith.Nat) (RBT_Impl.Rbt ([b], b) ()),
      (Bool, (b -> RBT_Impl.Rbt b (), b -> RBT_Impl.Rbt b ())))))));
rep_ta_code (Abs_ta_code x) = x;

det ::
  forall a b.
    (Compare.Compare_order a, Compare.Compare_order b) => Ta_code a b -> Bool;
det x = Tree_Automata_Autoref_Setup.ta_det_impl (rep_ta_code x);

ta_res_args_aux_code ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare_order b) => (RBT_Impl.Rbt a (),
                                    (RBT_Impl.Rbt (Tree_Automata.Ta_rule a b)
                                       (),
                                      ([(a, a)],
(RBT_Impl.Rbt a (),
  (RBT_Impl.Rbt (b, Arith.Nat) (RBT_Impl.Rbt ([a], a) ()),
    (Bool, (a -> RBT_Impl.Rbt a (), a -> RBT_Impl.Rbt a ()))))))) ->
                                    b -> [RBT_Impl.Rbt a ()] ->
   RBT_Impl.Rbt a ();
ta_res_args_aux_code =
  (\ x xa xb ->
    (case RBT_Comparator_Impl.rbt_comp_lookup Compare_Instances.compare_prod
            (Tree_Automata_Autoref_Setup.ta_idx_impl x) (xa, List.size_list xb)
      of {
      Nothing -> RBT_Impl.Empty;
      Just xc ->
        Tree_Automata_Autoref_Setup.union_image_rs_code xc
          (\ (xd, xe) ->
            (if List.list_all2
                  (\ xf s ->
                    (case RBT_Comparator_Impl.rbt_comp_lookup Compare.compare s
                            xf
                      of {
                      Nothing -> False;
                      Just _ -> True;
                    }))
                  xd xb
              then Tree_Automata_Autoref_Setup.ta_eps_cl_impl x xe
              else RBT_Impl.Empty));
    }));

ta_res_code ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare_order b) => (RBT_Impl.Rbt a (),
                                    (RBT_Impl.Rbt (Tree_Automata.Ta_rule a b)
                                       (),
                                      ([(a, a)],
(RBT_Impl.Rbt a (),
  (RBT_Impl.Rbt (b, Arith.Nat) (RBT_Impl.Rbt ([a], a) ()),
    (Bool, (a -> RBT_Impl.Rbt a (), a -> RBT_Impl.Rbt a ()))))))) ->
                                    Term.Term b a -> RBT_Impl.Rbt a ();
ta_res_code =
  (\ x xa ->
    Term.rec_term (\ xb xc -> Tree_Automata_Autoref_Setup.ta_eps_cl_impl xc xb)
      (\ xb xc xd -> let {
                       a = map (\ xe -> snd xe xd) xc;
                     } in ta_res_args_aux_code xd xb a)
      xa x);

set_App_code ::
  forall a.
    (Compare.Compare a) => RBT_Impl.Rbt [a] () ->
                             RBT_Impl.Rbt [a] () -> RBT_Impl.Rbt [a] ();
set_App_code x xs =
  (SetIteratorOperations.map_iterator_dom . RBT_add.rm_iterateoi) x
    (\ _ -> True)
    (\ xa ->
      (SetIteratorOperations.map_iterator_dom . RBT_add.rm_iterateoi) xs
        (\ _ -> True)
        (\ xaa ->
          RBT_Comparator_Impl.rbt_comp_insert Compare_Instances.compare_list
            (xa ++ xaa) ()))
    RBT_Impl.Empty;

map_add2_code ::
  forall a b c.
    (Compare.Compare a,
      Compare.Compare b) => RBT_Impl.Rbt a (RBT_Impl.Rbt b c) ->
                              RBT_Impl.Rbt a (RBT_Impl.Rbt b c) ->
                                RBT_Impl.Rbt a (RBT_Impl.Rbt b c);
map_add2_code m1 m2 =
  RBT_add.rm_iterateoi m2 (\ _ -> True)
    (\ x sigma ->
      (case x of {
        (a, b) ->
          (case RBT_Comparator_Impl.rbt_comp_lookup Compare.compare sigma a of {
            Nothing ->
              RBT_Comparator_Impl.rbt_comp_insert Compare.compare a b sigma;
            Just xc ->
              RBT_Comparator_Impl.rbt_comp_insert Compare.compare a
                (RBT_Comparator_Impl.rbt_comp_union_with_key Compare.compare
                  (\ _ _ rv -> rv) xc b)
                sigma;
          });
      }))
    m1;

update_all_code ::
  forall a b.
    (Compare.Compare a) => RBT_Impl.Rbt a b ->
                             RBT_Impl.Rbt a () -> b -> RBT_Impl.Rbt a b;
update_all_code m s v =
  (SetIteratorOperations.map_iterator_dom . RBT_add.rm_iterateoi) s
    (\ _ -> True)
    (\ x -> RBT_Comparator_Impl.rbt_comp_insert Compare.compare x v) m;

prs_wits_code ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare_order b) => (RBT_Impl.Rbt a (),
                                    (RBT_Impl.Rbt (Tree_Automata.Ta_rule a b)
                                       (),
                                      ([(a, a)],
(RBT_Impl.Rbt a (),
  (RBT_Impl.Rbt (b, Arith.Nat) (RBT_Impl.Rbt ([a], a) ()),
    (Bool, (a -> RBT_Impl.Rbt a (), a -> RBT_Impl.Rbt a ()))))))) ->
                                    RBT_Impl.Rbt a
                                      (Subterm_and_Context.Actxt b
(Term.Term b a));
prs_wits_code tAi =
  let {
    x = update_all_code RBT_Impl.Empty
          (Tree_Automata_Autoref_Setup.union_image_rs_code
            (Tree_Automata_Autoref_Setup.ta_final_impl tAi)
            (Tree_Automata_Autoref_Setup.ta_eps_icl_impl tAi))
          Subterm_and_Context.Hole;
    xa = (False, (Tree_Automata_Autoref_Setup.ta_rules_impl tAi, x));
  } in (case While_Combinator.while (\ (xb, (_, _)) -> not xb)
               (\ (_, (aa, ba)) ->
                 (SetIteratorOperations.map_iterator_dom . RBT_add.rm_iterateoi)
                   aa (\ _ -> True)
                   (\ xc (ab, (ac, bc)) ->
                     (case RBT_Comparator_Impl.rbt_comp_lookup Compare.compare
                             bc (Tree_Automata.r_rhs xc)
                       of {
                       Nothing ->
                         (ab, (RBT_Comparator_Impl.rbt_comp_insert
                                 Tree_Automata_Autoref_Setup.compare_ta_rule xc
                                 () ac,
                                bc));
                       Just xd ->
                         (False,
                           (ac, (case xc of {
                                  Tree_Automata.TA_rule xj xk _ ->
                                    List.rec_list (\ _ xn _ _ _ -> xn)
                                      (\ xm xn xo xp xq xr xs xt ->
let {
  y_b = update_all_code xq
          (Tree_Automata_Autoref_Setup.ta_eps_icl_impl xp (Term.the_Var xm))
          (Subterm_and_Context.actxt_compose xr
            (Subterm_and_Context.More xs xt Subterm_and_Context.Hole xn));
} in xo xp y_b xr xs (xt ++ [xm]))
                                      (map Term.Var xk) tAi bc xd xj [];
                                })));
                     }))
                   (True, (RBT_Impl.Empty, ba)))
               xa
         of {
         (_, (_, ba)) -> ba;
       });

next_res_wit_code ::
  forall a b c.
    (Compare.Compare a,
      Compare.Compare b) => RBT_Impl.Rbt (Tree_Automata.Ta_rule a b) () ->
                              RBT_Impl.Rbt a (Term.Term b c) ->
                                Maybe (a, Term.Term b c);
next_res_wit_code r m =
  (SetIteratorOperations.map_iterator_dom . RBT_add.rm_iterateoi) r
    Autoref_Bindings_HOL.is_None
    (\ x _ ->
      (case x of {
        Tree_Automata.TA_rule xb xc xd ->
          Option.bind
            (Option_Monad.mapM
              (RBT_Comparator_Impl.rbt_comp_lookup Compare.compare m) xc)
            (\ xe -> Just (xd, Term.Fun xb xe));
      }))
    Nothing;

res_wits_code ::
  forall a b c.
    (Compare.Compare_order a,
      Compare.Compare_order b) => (RBT_Impl.Rbt a (),
                                    (RBT_Impl.Rbt (Tree_Automata.Ta_rule a b)
                                       (),
                                      ([(a, a)],
(RBT_Impl.Rbt a (),
  (RBT_Impl.Rbt (b, Arith.Nat) (RBT_Impl.Rbt ([a], a) ()),
    (Bool, (a -> RBT_Impl.Rbt a (), a -> RBT_Impl.Rbt a ()))))))) ->
                                    RBT_Impl.Rbt a (Term.Term b c);
res_wits_code tAi =
  let {
    x = (Tree_Automata_Autoref_Setup.ta_rules_impl tAi, RBT_Impl.Empty);
  } in (case While_Combinator.while
               (\ (xb, _) ->
                 not (Gen_Set.gen_isEmpty
                       (Gen_Set.gen_ball
                         (SetIteratorOperations.map_iterator_dom .
                           RBT_add.rm_iterateoi))
                       xb))
               (\ (a, b) ->
                 (case next_res_wit_code a b of {
                   Nothing -> (RBT_Impl.Empty, b);
                   Just (aa, ba) ->
                     let {
                       xd = Tree_Automata_Autoref_Setup.ta_eps_cl_impl tAi aa;
                       xe = update_all_code b xd ba;
                       xf = Gen_Set.gen_filter
                              (SetIteratorOperations.map_iterator_dom .
                                RBT_add.rm_iterateoi)
                              RBT_Impl.Empty
                              (\ k ->
                                RBT_Comparator_Impl.rbt_comp_insert
                                  Tree_Automata_Autoref_Setup.compare_ta_rule k
                                  ())
                              (\ xf ->
                                not (case RBT_Comparator_Impl.rbt_comp_lookup
    Compare.compare xd (Tree_Automata.r_rhs xf)
                                      of {
                                      Nothing -> False;
                                      Just _ -> True;
                                    }))
                              a;
                     } in (xf, xe);
                 }))
               x
         of {
         (_, b) -> b;
       });

ta_match_var_ref_code ::
  forall a b c.
    (Compare.Compare_order a, Compare.Compare_order b,
      Compare.Compare c) => (RBT_Impl.Rbt a (),
                              (RBT_Impl.Rbt (Tree_Automata.Ta_rule a b) (),
                                ([(a, a)],
                                  (RBT_Impl.Rbt a (),
                                    (RBT_Impl.Rbt (b, Arith.Nat)
                                       (RBT_Impl.Rbt ([a], a) ()),
                                      (Bool,
(a -> RBT_Impl.Rbt a (), a -> RBT_Impl.Rbt a ()))))))) ->
                              RBT_Impl.Rbt a () ->
                                c -> RBT_Impl.Rbt a () ->
                                       RBT_Impl.Rbt [(c, a)] ();
ta_match_var_ref_code ta qsig x q =
  (SetIteratorOperations.map_iterator_dom . RBT_add.rm_iterateoi) qsig
    (\ _ -> True)
    (\ xa sigma ->
      (if not (Gen_Set.gen_disjoint
                (SetIteratorOperations.map_iterator_dom . RBT_add.rm_iterateoi)
                (\ k s ->
                  (case RBT_Comparator_Impl.rbt_comp_lookup Compare.compare s k
                    of {
                    Nothing -> False;
                    Just _ -> True;
                  }))
                (Tree_Automata_Autoref_Setup.ta_eps_cl_impl ta xa) q)
        then RBT_Comparator_Impl.rbt_comp_insert Compare_Instances.compare_list
               [(x, xa)] () sigma
        else sigma))
    RBT_Impl.Empty;

concat_listset_code ::
  forall a. (Compare.Compare a) => [RBT_Impl.Rbt [a] ()] -> RBT_Impl.Rbt [a] ();
concat_listset_code =
  List.rec_list
    (RBT_Comparator_Impl.rbt_comp_insert Compare_Instances.compare_list [] ()
      RBT_Impl.Empty)
    (\ x _ -> set_App_code x);

ta_match_code ::
  forall a b c.
    (Compare.Compare_order a, Compare.Compare_order b,
      Compare.Compare c) => (RBT_Impl.Rbt a (),
                              (RBT_Impl.Rbt (Tree_Automata.Ta_rule a b) (),
                                ([(a, a)],
                                  (RBT_Impl.Rbt a (),
                                    (RBT_Impl.Rbt (b, Arith.Nat)
                                       (RBT_Impl.Rbt ([a], a) ()),
                                      (Bool,
(a -> RBT_Impl.Rbt a (), a -> RBT_Impl.Rbt a ()))))))) ->
                              RBT_Impl.Rbt a () ->
                                Term.Term b c ->
                                  RBT_Impl.Rbt a () -> RBT_Impl.Rbt [(c, a)] ();
ta_match_code a b (Term.Fun c d) e =
  (case RBT_Comparator_Impl.rbt_comp_lookup Compare_Instances.compare_prod
          (Tree_Automata_Autoref_Setup.ta_idx_impl a) (c, List.size_list d)
    of {
    Nothing -> RBT_Impl.Empty;
    Just xe ->
      Tree_Automata_Autoref_Setup.union_image_rs_code xe
        (\ (xf, xg) ->
          (if not (Gen_Set.gen_disjoint
                    (SetIteratorOperations.map_iterator_dom .
                      RBT_add.rm_iterateoi)
                    (\ k s ->
                      (case RBT_Comparator_Impl.rbt_comp_lookup Compare.compare
                              s k
                        of {
                        Nothing -> False;
                        Just _ -> True;
                      }))
                    (Tree_Automata_Autoref_Setup.ta_eps_cl_impl a xg) e)
            then concat_listset_code
                   (map2 (\ t q ->
                           ta_match_code a b t
                             (RBT_Comparator_Impl.rbt_comp_insert
                               Compare.compare q () RBT_Impl.Empty))
                     d xf)
            else RBT_Impl.Empty));
  });
ta_match_code ta qsig (Term.Var x) q = ta_match_var_ref_code ta qsig x q;

ta_make_ls_code ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare_order b) => [a] ->
                                    [Tree_Automata.Ta_rule a b] ->
                                      [(a, a)] ->
(RBT_Impl.Rbt a (),
  (RBT_Impl.Rbt (Tree_Automata.Ta_rule a b) (),
    ([(a, a)],
      (RBT_Impl.Rbt a (),
        (RBT_Impl.Rbt (b, Arith.Nat) (RBT_Impl.Rbt ([a], a) ()),
          (Bool, (a -> RBT_Impl.Rbt a (), a -> RBT_Impl.Rbt a ())))))));
ta_make_ls_code =
  (\ x xa xb ->
    Tree_Automata_Autoref_Setup.ta_make_code
      (Gen_Set.gen_set RBT_Impl.Empty
        (\ k -> RBT_Comparator_Impl.rbt_comp_insert Compare.compare k ()) x)
      (Gen_Set.gen_set RBT_Impl.Empty
        (\ k ->
          RBT_Comparator_Impl.rbt_comp_insert
            Tree_Automata_Autoref_Setup.compare_ta_rule k ())
        xa)
      (Gen_Set.gen_set []
        (Impl_List_Set.glist_insert
          (Autoref_Bindings_HOL.prod_eq
            (Intf_Comp.comp2eq Tree_Automata_Autoref_Setup.compare_res)
            (Intf_Comp.comp2eq Tree_Automata_Autoref_Setup.compare_res)))
        xb));

make_ls ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare_order b) => [a] ->
                                    [Tree_Automata.Ta_rule a b] ->
                                      [(a, a)] -> Ta_code a b;
make_ls x xa xb = Abs_ta_code (ta_make_ls_code x xa xb);

update_all2_code ::
  forall a b c.
    (Compare.Compare a,
      Compare.Compare b) => RBT_Impl.Rbt a (RBT_Impl.Rbt b c) ->
                              RBT_Impl.Rbt a () ->
                                RBT_Impl.Rbt b () ->
                                  c -> RBT_Impl.Rbt a (RBT_Impl.Rbt b c);
update_all2_code m s1 s2 v =
  (SetIteratorOperations.map_iterator_dom . RBT_add.rm_iterateoi) s1
    (\ _ -> True)
    (\ x sigma ->
      let {
        xa = update_all_code
               (case RBT_Comparator_Impl.rbt_comp_lookup Compare.compare sigma x
                 of {
                 Nothing -> RBT_Impl.Empty;
                 Just a -> id a;
               })
               s2 v;
      } in RBT_Comparator_Impl.rbt_comp_insert Compare.compare x xa sigma)
    m;

is_coh_final_code ::
  forall a b c d e.
    (Compare.Compare a) => RBT_Impl.Rbt a () ->
                             RBT_Impl.Rbt a
                               (RBT_Impl.Rbt a
                                 (Term.Term b c, Term.Term d e)) ->
                               Maybe (Term.Term b c, Term.Term d e);
is_coh_final_code fin rel =
  RBT_add.rm_iterateoi rel Autoref_Bindings_HOL.is_None
    (\ x _ ->
      (case x of {
        (a, b) ->
          (if (case RBT_Comparator_Impl.rbt_comp_lookup Compare.compare fin a of
                {
                Nothing -> False;
                Just _ -> True;
              })
            then RBT_add.rm_iterateoi b Autoref_Bindings_HOL.is_None
                   (\ xa _ ->
                     (case xa of {
                       (aa, (ab, bb)) ->
                         (if (case RBT_Comparator_Impl.rbt_comp_lookup
                                     Compare.compare fin aa
                               of {
                               Nothing -> False;
                               Just _ -> True;
                             })
                           then Nothing else Just (ab, bb));
                     }))
                   Nothing
            else Nothing);
      }))
    Nothing;

ta_only_res_wits_code ::
  forall a b c d.
    (Compare.Compare_order a,
      Compare.Compare_order b) => (RBT_Impl.Rbt a (),
                                    (RBT_Impl.Rbt (Tree_Automata.Ta_rule a b)
                                       (),
                                      ([(a, a)],
(RBT_Impl.Rbt a (),
  (RBT_Impl.Rbt (b, Arith.Nat) (RBT_Impl.Rbt ([a], a) ()),
    (Bool, (a -> RBT_Impl.Rbt a (), a -> RBT_Impl.Rbt a ()))))))) ->
                                    RBT_Impl.Rbt a (Term.Term c d) ->
                                      (RBT_Impl.Rbt a (),
(RBT_Impl.Rbt (Tree_Automata.Ta_rule a b) (),
  ([(a, a)],
    (RBT_Impl.Rbt a (),
      (RBT_Impl.Rbt (b, Arith.Nat) (RBT_Impl.Rbt ([a], a) ()),
        (Bool, (a -> RBT_Impl.Rbt a (), a -> RBT_Impl.Rbt a ())))))));
ta_only_res_wits_code a b =
  let {
    y = Gen_Set.gen_filter
          (SetIteratorOperations.map_iterator_dom . RBT_add.rm_iterateoi)
          RBT_Impl.Empty
          (\ k -> RBT_Comparator_Impl.rbt_comp_insert Compare.compare k ())
          (\ xb ->
            not (Autoref_Bindings_HOL.is_None
                  (RBT_Comparator_Impl.rbt_comp_lookup Compare.compare b xb)))
          (Tree_Automata_Autoref_Setup.ta_final_impl a);
    y_a = Gen_Set.gen_filter
            (SetIteratorOperations.map_iterator_dom . RBT_add.rm_iterateoi)
            RBT_Impl.Empty
            (\ k ->
              RBT_Comparator_Impl.rbt_comp_insert
                Tree_Automata_Autoref_Setup.compare_ta_rule k ())
            (\ xb ->
              Param_HOL.list_all_rec
                (\ xc ->
                  not (Autoref_Bindings_HOL.is_None
                        (RBT_Comparator_Impl.rbt_comp_lookup Compare.compare b
                          xc)))
                (Tree_Automata.r_lhs_states xb))
            (Tree_Automata_Autoref_Setup.ta_rules_impl a);
    aa = filter
           (\ xb ->
             not (Autoref_Bindings_HOL.is_None
                   (RBT_Comparator_Impl.rbt_comp_lookup Compare.compare b
                     (fst xb))))
           (Tree_Automata_Autoref_Setup.ta_eps_impl a);
  } in Tree_Automata_Autoref_Setup.ta_make_code y y_a aa;

ta_only_prs_wits_code ::
  forall a b c d e.
    (Compare.Compare_order a,
      Compare.Compare_order b) => (RBT_Impl.Rbt a (),
                                    (RBT_Impl.Rbt (Tree_Automata.Ta_rule a b)
                                       (),
                                      ([(a, a)],
(RBT_Impl.Rbt a (),
  (RBT_Impl.Rbt (b, Arith.Nat) (RBT_Impl.Rbt ([a], a) ()),
    (Bool, (a -> RBT_Impl.Rbt a (), a -> RBT_Impl.Rbt a ()))))))) ->
                                    RBT_Impl.Rbt a
                                      (Subterm_and_Context.Actxt c
(Term.Term d e)) ->
                                      (RBT_Impl.Rbt a (),
(RBT_Impl.Rbt (Tree_Automata.Ta_rule a b) (),
  ([(a, a)],
    (RBT_Impl.Rbt a (),
      (RBT_Impl.Rbt (b, Arith.Nat) (RBT_Impl.Rbt ([a], a) ()),
        (Bool, (a -> RBT_Impl.Rbt a (), a -> RBT_Impl.Rbt a ())))))));
ta_only_prs_wits_code a b =
  let {
    y = Gen_Set.gen_filter
          (SetIteratorOperations.map_iterator_dom . RBT_add.rm_iterateoi)
          RBT_Impl.Empty
          (\ k -> RBT_Comparator_Impl.rbt_comp_insert Compare.compare k ())
          (\ xb ->
            not (Autoref_Bindings_HOL.is_None
                  (RBT_Comparator_Impl.rbt_comp_lookup Compare.compare b xb)))
          (Tree_Automata_Autoref_Setup.ta_final_impl a);
    y_a = Gen_Set.gen_filter
            (SetIteratorOperations.map_iterator_dom . RBT_add.rm_iterateoi)
            RBT_Impl.Empty
            (\ k ->
              RBT_Comparator_Impl.rbt_comp_insert
                Tree_Automata_Autoref_Setup.compare_ta_rule k ())
            (\ xb ->
              not (Autoref_Bindings_HOL.is_None
                    (RBT_Comparator_Impl.rbt_comp_lookup Compare.compare b
                      (Tree_Automata.r_rhs xb))))
            (Tree_Automata_Autoref_Setup.ta_rules_impl a);
    aa = filter
           (\ xb ->
             not (Autoref_Bindings_HOL.is_None
                   (RBT_Comparator_Impl.rbt_comp_lookup Compare.compare b
                     (snd xb))))
           (Tree_Automata_Autoref_Setup.ta_eps_impl a);
  } in Tree_Automata_Autoref_Setup.ta_make_code y y_a aa;

trim_ta_wits_code ::
  forall a b c.
    (Compare.Compare_order a,
      Compare.Compare_order b) => (RBT_Impl.Rbt a (),
                                    (RBT_Impl.Rbt (Tree_Automata.Ta_rule a b)
                                       (),
                                      ([(a, a)],
(RBT_Impl.Rbt a (),
  (RBT_Impl.Rbt (b, Arith.Nat) (RBT_Impl.Rbt ([a], a) ()),
    (Bool, (a -> RBT_Impl.Rbt a (), a -> RBT_Impl.Rbt a ()))))))) ->
                                    ((RBT_Impl.Rbt a (),
                                       (RBT_Impl.Rbt (Tree_Automata.Ta_rule a b)
  (),
 ([(a, a)],
   (RBT_Impl.Rbt a (),
     (RBT_Impl.Rbt (b, Arith.Nat) (RBT_Impl.Rbt ([a], a) ()),
       (Bool, (a -> RBT_Impl.Rbt a (), a -> RBT_Impl.Rbt a ()))))))),
                                      (RBT_Impl.Rbt a (Term.Term b c),
RBT_Impl.Rbt a (Subterm_and_Context.Actxt b (Term.Term b a))));
trim_ta_wits_code tAi = let {
                          x = res_wits_code tAi;
                          xa = ta_only_res_wits_code tAi x;
                          xb = prs_wits_code xa;
                          xc = ta_only_prs_wits_code xa xb;
                        } in (xc, (x, xb));

is_compatible_code ::
  forall a b c.
    (Compare.Compare_order a, Compare.Compare_order b, Compare.Compare c,
      Eq c) => (RBT_Impl.Rbt a (),
                 (RBT_Impl.Rbt (Tree_Automata.Ta_rule a b) (),
                   ([(a, a)],
                     (RBT_Impl.Rbt a (),
                       (RBT_Impl.Rbt (b, Arith.Nat) (RBT_Impl.Rbt ([a], a) ()),
                         (Bool,
                           (a -> RBT_Impl.Rbt a (),
                             a -> RBT_Impl.Rbt a ()))))))) ->
                 RBT_Impl.Rbt (Term.Term b c, Term.Term b c) () ->
                   Sum_Type.Sum (a, (Term.Term b a, Term.Term b a))
                     (RBT_Impl.Rbt a
                       (RBT_Impl.Rbt a (Term.Term b a, Term.Term b a)));
is_compatible_code ta r =
  (SetIteratorOperations.map_iterator_dom . RBT_add.rm_iterateoi) r
    Param_HOL.is_Inr
    (\ x sigma ->
      (case x of {
        (a, b) ->
          let {
            xa = ta_match_code ta
                   (Tree_Automata_Autoref_Setup.ta_rhs_states_impl ta) a
                   (Tree_Automata_Autoref_Setup.ta_rhs_states_impl ta);
          } in (SetIteratorOperations.map_iterator_dom . RBT_add.rm_iterateoi)
                 xa Param_HOL.is_Inr
                 (\ xb sigmaa ->
                   let {
                     xc = Term.map_term (\ xg -> xg) (Util.fun_of xb) a;
                     xd = ta_res_code ta xc;
                   } in (if Gen_Set.gen_isEmpty
                              (Gen_Set.gen_ball
                                (SetIteratorOperations.map_iterator_dom .
                                  RBT_add.rm_iterateoi))
                              xd
                          then sigmaa
                          else let {
                                 xe = Term.map_term (\ xg -> xg)
(Util.fun_of xb) b;
                                 xf = ta_res_code ta xe;
                               } in (if Gen_Set.gen_isEmpty
  (Gen_Set.gen_ball
    (SetIteratorOperations.map_iterator_dom . RBT_add.rm_iterateoi))
  xf
                                      then let {
     xg = Gen_Set.gen_pick
            (SetIteratorOperations.map_iterator_dom . RBT_add.rm_iterateoi) xd;
   } in Sum_Type.Inl (xg, (xc, xe))
                                      else let {
     aa = update_all2_code (Sum_Type.projr sigmaa) xd xf (xc, xe);
   } in Sum_Type.Inr aa)))
                 sigma;
      }))
    (Sum_Type.Inr RBT_Impl.Empty);

rule_filter_opt_code ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare_order b) => (RBT_Impl.Rbt a (),
                                    (RBT_Impl.Rbt (Tree_Automata.Ta_rule a b)
                                       (),
                                      ([(a, a)],
(RBT_Impl.Rbt a (),
  (RBT_Impl.Rbt (b, Arith.Nat) (RBT_Impl.Rbt ([a], a) ()),
    (Bool, (a -> RBT_Impl.Rbt a (), a -> RBT_Impl.Rbt a ()))))))) ->
                                    b -> [a] -> RBT_Impl.Rbt a ();
rule_filter_opt_code a b c =
  (case RBT_Comparator_Impl.rbt_comp_lookup Compare_Instances.compare_prod
          (Tree_Automata_Autoref_Setup.ta_idx_impl a) (b, List.size_list c)
    of {
    Nothing -> RBT_Impl.Empty;
    Just xc ->
      Gen_Set.gen_image
        (SetIteratorOperations.map_iterator_dom . RBT_add.rm_iterateoi)
        RBT_Impl.Empty
        (\ k -> RBT_Comparator_Impl.rbt_comp_insert Compare.compare k ()) snd
        (Gen_Set.gen_filter
          (SetIteratorOperations.map_iterator_dom . RBT_add.rm_iterateoi)
          RBT_Impl.Empty
          (\ k ->
            RBT_Comparator_Impl.rbt_comp_insert Compare_Instances.compare_prod k
              ())
          (\ (xd, _) ->
            Autoref_Bindings_HOL.list_eq
              (Intf_Comp.comp2eq Tree_Automata_Autoref_Setup.compare_res) xd c)
          xc);
  });

ta_check_comcoh_code ::
  forall a b c d.
    (Compare.Compare_order a, Compare.Compare_order b, Compare.Compare c,
      Eq c) => (RBT_Impl.Rbt a (),
                 (RBT_Impl.Rbt (Tree_Automata.Ta_rule a b) (),
                   ([(a, a)],
                     (RBT_Impl.Rbt a (),
                       (RBT_Impl.Rbt (b, Arith.Nat) (RBT_Impl.Rbt ([a], a) ()),
                         (Bool,
                           (a -> RBT_Impl.Rbt a (),
                             a -> RBT_Impl.Rbt a ()))))))) ->
                 RBT_Impl.Rbt (Term.Term b c, Term.Term b c) () ->
                   Maybe (Term.Term b d, Term.Term b d);
ta_check_comcoh_code ta r =
  (case trim_ta_wits_code ta of {
    (a, (aa, ba)) ->
      let {
        xa = is_compatible_code a r;
        xb = (\ xf xg ->
               Tree_Automata_Autoref_Setup.subst_apply_term
                 (Subterm_and_Context.intp_actxt Term.Fun
                   (Option.the
                     (RBT_Comparator_Impl.rbt_comp_lookup Compare.compare ba
                       xf))
                   xg)
                 (\ xh ->
                   Option.the
                     (RBT_Comparator_Impl.rbt_comp_lookup Compare.compare aa
                       xh)));
      } in (case xa of {
             Sum_Type.Inl (ab, (ac, bc)) -> Just (xb ab ac, xb ab bc);
             Sum_Type.Inr ra ->
               (case (case While_Combinator.while
                             (\ ab ->
                               (case ab of {
                                 (Sum_Type.Inl _, _) -> False;
                                 (Sum_Type.Inr xj, _) ->
                                   not (Gen_Map.gen_isEmpty
 (Gen_Map.gen_ball RBT_add.rm_iterateoi) xj);
                               }))
                             (\ (ab, bb) ->
                               let {
                                 xd = (SetIteratorOperations.map_iterator_dom .
RBT_add.rm_iterateoi)
(Tree_Automata_Autoref_Setup.ta_rules_impl a) Param_HOL.is_Inr
(\ xd sigma ->
  (case xd of {
    Tree_Automata.TA_rule xe y z ->
      Foldi.foldli (List.upt Arith.zero_nat (List.size_list y)) Param_HOL.is_Inr
        (\ xf s ->
          let {
            xg = List.nth y xf;
          } in (case RBT_Comparator_Impl.rbt_comp_lookup Compare.compare
                       (Sum_Type.projr ab) xg
                 of {
                 Nothing -> s;
                 Just xh ->
                   RBT_add.rm_iterateoi xh Param_HOL.is_Inr
                     (\ xi sigmaa ->
                       (case xi of {
                         (ac, (ad, bd)) ->
                           let {
                             xj = map Term.Var (List.take xf y);
                             xk = map Term.Var (List.drop (Arith.suc xf) y);
                             xl = Term.Fun xe (xj ++ ad : xk);
                             xm = Term.Fun xe (xj ++ bd : xk);
                             xn = List.list_update y xf ac;
                             xo = rule_filter_opt_code a xe xn;
                           } in (if Gen_Set.gen_isEmpty
                                      (Gen_Set.gen_ball
(SetIteratorOperations.map_iterator_dom . RBT_add.rm_iterateoi))
                                      xo
                                  then Sum_Type.Inl (z, (xl, xm))
                                  else let {
 xp = Gen_Set.gen_filter
        (SetIteratorOperations.map_iterator_dom . RBT_add.rm_iterateoi)
        RBT_Impl.Empty
        (\ k -> RBT_Comparator_Impl.rbt_comp_insert Compare.compare k ())
        (\ xv ->
          Autoref_Bindings_HOL.is_None
            (Option.bind
              (RBT_Comparator_Impl.rbt_comp_lookup Compare.compare bb z)
              (\ xw ->
                RBT_Comparator_Impl.rbt_comp_lookup Compare.compare xw xv)))
        xo;
                                       } in
 (if Gen_Set.gen_isEmpty
       (Gen_Set.gen_ball
         (SetIteratorOperations.map_iterator_dom . RBT_add.rm_iterateoi))
       xp
   then sigmaa
   else Sum_Type.Inr
          (update_all2_code (Sum_Type.projr sigmaa)
            (RBT_Comparator_Impl.rbt_comp_insert Compare.compare z ()
              RBT_Impl.Empty)
            xp (xl, xm))));
                       }))
                     s;
               }))
        sigma;
  }))
(Sum_Type.Inr RBT_Impl.Empty);
                               } in (if Param_HOL.is_Inr xd
                                      then (xd,
     map_add2_code bb (Sum_Type.projr xd))
                                      else (xd, bb)))
                             (Sum_Type.Inr ra, ra)
                       of {
                       (ab, bb) ->
                         (if Param_HOL.is_Inr ab then Sum_Type.Inr bb else ab);
                     })
                 of {
                 Sum_Type.Inl (ab, (ac, bc)) -> Just (xb ab ac, xb ab bc);
                 Sum_Type.Inr raa ->
                   (case is_coh_final_code
                           (Tree_Automata_Autoref_Setup.ta_final_impl a) raa
                     of {
                     Nothing -> Nothing;
                     Just (ab, bb) ->
                       Just (Tree_Automata_Autoref_Setup.subst_apply_term ab
                               (\ xj ->
                                 Option.the
                                   (RBT_Comparator_Impl.rbt_comp_lookup
                                     Compare.compare aa xj)),
                              Tree_Automata_Autoref_Setup.subst_apply_term bb
                                (\ xj ->
                                  Option.the
                                    (RBT_Comparator_Impl.rbt_comp_lookup
                                      Compare.compare aa xj)));
                   });
               });
           });
  });

check_comcoh_wit ::
  forall a b c.
    (Compare.Compare_order a, Compare.Compare_order b, Compare.Compare_order c,
      Eq c) => Ta_code a b ->
                 RBT.Rbt (Term.Term b c, Term.Term b c) () ->
                   Maybe (Term.Term b c, Term.Term b c);
check_comcoh_wit x xa = ta_check_comcoh_code (rep_ta_code x) (RBT.impl_of xa);

check_comcoh_wit_ls ::
  forall a b c.
    (Compare.Compare_order a, Compare.Compare_order b, Compare.Compare_order c,
      Eq c) => Ta_code a b ->
                 [(Term.Term b c, Term.Term b c)] ->
                   Maybe (Term.Term b c, Term.Term b c);
check_comcoh_wit_ls ta r =
  check_comcoh_wit ta (RBTSetImpl.g_from_list_dflt_basic_oops_rm_basic_ops r);

}
