{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Gabow_SCC_RBT(scc_decomp) where {

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
import qualified Impl_List_Set;
import qualified Gen_Set;
import qualified Foldi;
import qualified Quasi_Order;
import qualified Autoref_Bindings_HOL;
import qualified Digraph_Impl;
import qualified Gabow_Skeleton;
import qualified Impl_Array_Stack;
import qualified While_Combinator;
import qualified HOL;
import qualified Arith;
import qualified Compare;

pop_tr ::
  forall a.
    (Compare.Compare_order a) => ((Array.Array a, Arith.Nat),
                                   ((Array.Array Arith.Nat, Arith.Nat),
                                     (Arith.Rbt a Arith.Int,
                                       (Array.Array (Arith.Nat, [a]),
 Arith.Nat)))) ->
                                   ((Array.Array a, Arith.Nat),
                                     ((Array.Array Arith.Nat, Arith.Nat),
                                       (Arith.Rbt a Arith.Int,
 (Array.Array (Arith.Nat, [a]), Arith.Nat))));
pop_tr s =
  (case s of {
    (a, (aa, (ab, bb))) ->
      let {
        x = Arith.minus_nat (Impl_Array_Stack.as_length aa) Arith.one_nat;
        xa = (case While_Combinator.while
                     (\ (xe, _) ->
                       Arith.less_nat xe
                         (if Arith.equal_nat (Arith.plus_nat x Arith.one_nat)
                               (Impl_Array_Stack.as_length aa)
                           then Impl_Array_Stack.as_length a
                           else Impl_Array_Stack.as_get aa
                                  (Arith.plus_nat x Arith.one_nat)))
                     (\ (ac, bc) ->
                       (Arith.suc ac,
                         Arith.rbt_inserta (Impl_Array_Stack.as_get a ac)
                           (Arith.uminus_int Arith.one_int) bc))
                     (Impl_Array_Stack.as_get aa x, ab)
               of {
               (_, bc) -> bc;
             });
        xb = Impl_Array_Stack.as_take (Impl_Array_Stack.as_top aa) a;
        xc = Impl_Array_Stack.as_pop aa;
      } in (xb, (xc, (xa, bb)));
  });

idx_of_tr ::
  forall a.
    (Compare.Compare_order a) => a -> ((Array.Array a, Arith.Nat),
((Array.Array Arith.Nat, Arith.Nat),
  (Arith.Rbt a Arith.Int, (Array.Array (Arith.Nat, [a]), Arith.Nat)))) ->
Arith.Nat;
idx_of_tr s v =
  (case v of {
    (_, (aa, (ab, _))) ->
      let {
        x = (case Arith.rbt_lookupa ab s of {
              Just i ->
                (if Arith.less_eq_int Arith.zero_int i then Arith.nat i
                  else error "undefined");
            });
        xa = Gabow_Skeleton.find_max_nat (Impl_Array_Stack.as_length aa)
               (\ j -> Arith.less_eq_nat (Impl_Array_Stack.as_get aa j) x);
      } in xa;
  });

push_code ::
  forall a b.
    (Compare.Compare_order a) => Digraph_Impl.Gen_g_impl_ext (a -> Bool)
                                   (a -> [a]) [a] b ->
                                   a -> ((Array.Array a, Arith.Nat),
  ((Array.Array Arith.Nat, Arith.Nat),
    (Arith.Rbt a Arith.Int, (Array.Array (Arith.Nat, [a]), Arith.Nat)))) ->
  ((Array.Array a, Arith.Nat),
    ((Array.Array Arith.Nat, Arith.Nat),
      (Arith.Rbt a Arith.Int, (Array.Array (Arith.Nat, [a]), Arith.Nat))));
push_code g_impl =
  (\ x (xa, (xb, (xc, xd))) ->
    let {
      _ = Gabow_Skeleton.stat_newnode ();
      y_a = Impl_Array_Stack.as_length xa;
      y_b = Impl_Array_Stack.as_push xa x;
      y_c = Impl_Array_Stack.as_push xb y_a;
      y_d = Arith.rbt_inserta x (Arith.int_of_nat y_a) xc;
      y_e = (if Autoref_Bindings_HOL.is_Nil (Digraph_Impl.gi_E g_impl x) then xd
              else Impl_Array_Stack.as_push xd
                     (y_a, Digraph_Impl.gi_E g_impl x));
    } in (y_b, (y_c, (y_d, y_e))));

edges_to_adj_fun ::
  forall a. (Compare.Compare_order a, Eq a) => [(a, a)] -> a -> [a];
edges_to_adj_fun e =
  Map_Choice.precompute_fun
    (\ a ->
      Arith.remdups
        (concatMap (\ ea -> (if fst ea == a then [snd ea] else [])) e))
    (Arith.remdups (map fst e ++ map snd e));

create_graph_impl ::
  forall a.
    (Compare.Compare_order a,
      Eq a) => [(a, a)] ->
                 Digraph_Impl.Gen_g_impl_ext (a -> Bool) (a -> [a]) [a] ();
create_graph_impl e =
  Digraph_Impl.Gen_g_impl_ext (Arith.membera (map fst e ++ map snd e))
    (edges_to_adj_fun e) (Arith.remdups (map fst e ++ map snd e)) ();

select_edge_tr ::
  forall a.
    (Eq a,
      Quasi_Order.Linorder a) => ((Array.Array a, Arith.Nat),
                                   ((Array.Array Arith.Nat, Arith.Nat),
                                     (Arith.Rbt a Arith.Int,
                                       (Array.Array (Arith.Nat, [a]),
 Arith.Nat)))) ->
                                   (Maybe a,
                                     ((Array.Array a, Arith.Nat),
                                       ((Array.Array Arith.Nat, Arith.Nat),
 (Arith.Rbt a Arith.Int, (Array.Array (Arith.Nat, [a]), Arith.Nat)))));
select_edge_tr s =
  (case s of {
    (a, (aa, (ab, bb))) ->
      (if Impl_Array_Stack.as_is_empty bb then (Nothing, (a, (aa, (ab, bb))))
        else (case Impl_Array_Stack.as_top bb of {
               (ac, bc) ->
                 (if Arith.less_eq_nat
                       (Impl_Array_Stack.as_get aa
                         (Arith.minus_nat (Impl_Array_Stack.as_length aa)
                           Arith.one_nat))
                       ac
                   then let {
                          xa = Gen_Set.gen_pick (\ x -> Foldi.foldli (id x)) bc;
                          xb = Impl_List_Set.glist_delete (\ ad b -> ad == b) xa
                                 bc;
                          xc = (if Autoref_Bindings_HOL.is_Nil xb
                                 then Impl_Array_Stack.as_pop bb
                                 else Impl_Array_Stack.as_set bb
(Arith.minus_nat (Impl_Array_Stack.as_length bb) Arith.one_nat) (ac, xb));
                        } in (Just xa, (a, (aa, (ab, xc))))
                   else (Nothing, (a, (aa, (ab, bb)))));
             }));
  });

last_seg_tr ::
  forall a.
    (Quasi_Order.Linorder a) => ((Array.Array a, Arith.Nat),
                                  ((Array.Array Arith.Nat, Arith.Nat),
                                    (Arith.Rbt a Arith.Int,
                                      (Array.Array (Arith.Nat, [a]),
Arith.Nat)))) ->
                                  [a];
last_seg_tr s =
  (case s of {
    (a, (aa, (_, _))) ->
      (case While_Combinator.while
              (\ (xe, _) ->
                Arith.less_nat xe
                  (if Arith.equal_nat
                        (Arith.plus_nat
                          (Arith.minus_nat (Impl_Array_Stack.as_length aa)
                            Arith.one_nat)
                          Arith.one_nat)
                        (Impl_Array_Stack.as_length aa)
                    then Impl_Array_Stack.as_length a
                    else Impl_Array_Stack.as_get aa
                           (Arith.plus_nat
                             (Arith.minus_nat (Impl_Array_Stack.as_length aa)
                               Arith.one_nat)
                             Arith.one_nat)))
              (\ (ac, bc) -> let {
                               xa = Impl_Array_Stack.as_get a ac;
                             } in (Arith.suc ac, xa : bc))
              (Impl_Array_Stack.as_get aa
                 (Arith.minus_nat (Impl_Array_Stack.as_length aa)
                   Arith.one_nat),
                [])
        of {
        (_, bc) -> bc;
      });
  });

collapse_tr ::
  forall a.
    (Compare.Compare_order a) => a -> ((Array.Array a, Arith.Nat),
((Array.Array Arith.Nat, Arith.Nat),
  (Arith.Rbt a Arith.Int, (Array.Array (Arith.Nat, [a]), Arith.Nat)))) ->
((Array.Array a, Arith.Nat),
  ((Array.Array Arith.Nat, Arith.Nat),
    (Arith.Rbt a Arith.Int, (Array.Array (Arith.Nat, [a]), Arith.Nat))));
collapse_tr v s =
  (case s of {
    (a, (aa, (ab, bb))) ->
      let {
        x = idx_of_tr v (a, (aa, (ab, bb)));
        xa = Impl_Array_Stack.as_take (Arith.plus_nat x Arith.one_nat) aa;
      } in (a, (xa, (ab, bb)));
  });

compute_SCC_tr ::
  forall a b.
    (Compare.Compare_order a,
      Eq a) => Digraph_Impl.Gen_g_impl_ext (a -> Bool) (a -> [a]) [a] b ->
                 [[a]];
compute_SCC_tr g =
  let {
    _ = Gabow_Skeleton.stat_start ();
    xa = ([], Arith.Empty);
  } in (case Foldi.foldli (id (Digraph_Impl.gi_V0 g)) (\ _ -> True)
               (\ xb (a, b) ->
                 (if not (case Arith.rbt_lookupa b xb of {
                           Nothing -> False;
                           Just i ->
                             (if Arith.less_eq_int Arith.zero_int i then False
                               else True);
                         })
                   then let {
                          xc = (a, (Impl_Array_Stack.as_singleton xb,
                                     (Impl_Array_Stack.as_singleton
Arith.zero_nat,
                                       (Arith.rbt_inserta xb
  (Arith.int_of_nat Arith.zero_nat) b,
 (if Autoref_Bindings_HOL.is_Nil (Digraph_Impl.gi_E g xb)
   then Impl_Array_Stack.as_empty ()
   else Impl_Array_Stack.as_singleton
          (Arith.zero_nat, Digraph_Impl.gi_E g xb))))));
                        } in (case While_Combinator.while
                                     (\ (_, xf) ->
                                       not
 (Impl_Array_Stack.as_is_empty (case xf of {
                                 (xg, (_, (_, _))) -> xg;
                               })))
                                     (\ (aa, ba) ->
                                       (case select_edge_tr ba of {
 (Nothing, bb) -> let {
                    xf = last_seg_tr bb;
                    xg = pop_tr bb;
                    xh = xf : aa;
                  } in (xh, xg);
 (Just xf, bb) ->
   (if (case Arith.rbt_lookupa (case bb of {
                                 (_, (_, (xl, _))) -> xl;
                               })
               xf
         of {
         Nothing -> False;
         Just i -> (if Arith.less_eq_int Arith.zero_int i then True else False);
       })
     then let {
            ab = collapse_tr xf bb;
          } in (aa, ab)
     else (if not (case Arith.rbt_lookupa (case bb of {
    (_, (_, (xl, _))) -> xl;
  })
                          xf
                    of {
                    Nothing -> False;
                    Just i ->
                      (if Arith.less_eq_int Arith.zero_int i then False
                        else True);
                  })
            then (aa, push_code g xf bb) else (aa, bb)));
                                       }))
                                     xc
                               of {
                               (aa, (_, (_, (ad, _)))) -> (aa, ad);
                             })
                   else (a, b)))
               xa
         of {
         (a, _) -> let {
                     _ = Gabow_Skeleton.stat_stop ();
                   } in a;
       });

scc_decomp ::
  forall a.
    (Arith.Ceq a, Arith.Ccompare a, Compare.Compare_order a, Eq a,
      Arith.Set_impl a) => [(a, a)] -> [[a]];
scc_decomp e =
  let {
    ee = Arith.set e;
  } in filter (\ a -> (case a of {
                        [] -> True;
                        [v] -> Arith.member (v, v) ee;
                        _ : _ : _ -> True;
                      }))
         (compute_SCC_tr (create_graph_impl e));

}
