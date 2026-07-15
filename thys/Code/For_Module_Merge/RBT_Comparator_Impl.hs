{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  RBT_Comparator_Impl(rbt_comp_lookup, rbt_comp_delete, rbt_comp_minus,
                       rbt_comp_insert, rbt_comp_inter_with_key,
                       rbt_comp_union_with_key)
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
import qualified HOL;
import qualified Arith;
import qualified List;
import qualified Option;
import qualified Product_Type;
import qualified Comparator;
import qualified RBT_Impl;

rbt_comp_lookup ::
  forall a b. (a -> a -> Comparator.Order) -> RBT_Impl.Rbt a b -> a -> Maybe b;
rbt_comp_lookup c RBT_Impl.Empty k = Nothing;
rbt_comp_lookup c (RBT_Impl.Branch uu l x y r) k =
  (case c k x of {
    Comparator.Eqa -> Just y;
    Comparator.Lt -> rbt_comp_lookup c l k;
    Comparator.Gt -> rbt_comp_lookup c r k;
  });

filter_comp_minus ::
  forall a b c.
    (a -> a -> Comparator.Order) ->
      RBT_Impl.Rbt a b -> RBT_Impl.Rbt a c -> [(a, b)];
filter_comp_minus c t1 t2 =
  filter (\ (k, _) -> Option.is_none (rbt_comp_lookup c t2 k))
    (RBT_Impl.entries t1);

rbt_comp_del ::
  forall a b.
    (a -> a -> Comparator.Order) -> a -> RBT_Impl.Rbt a b -> RBT_Impl.Rbt a b;
rbt_comp_del c x RBT_Impl.Empty = RBT_Impl.Empty;
rbt_comp_del c x (RBT_Impl.Branch uu a y s b) =
  (case c x y of {
    Comparator.Eqa -> RBT_Impl.combine a b;
    Comparator.Lt -> rbt_comp_del_from_left c x a y s b;
    Comparator.Gt -> rbt_comp_del_from_right c x a y s b;
  });

rbt_comp_del_from_left ::
  forall a b.
    (a -> a -> Comparator.Order) ->
      a -> RBT_Impl.Rbt a b -> a -> b -> RBT_Impl.Rbt a b -> RBT_Impl.Rbt a b;
rbt_comp_del_from_left c x (RBT_Impl.Branch RBT_Impl.B lt z v rt) y s b =
  RBT_Impl.balance_left
    (rbt_comp_del c x (RBT_Impl.Branch RBT_Impl.B lt z v rt)) y s b;
rbt_comp_del_from_left c x RBT_Impl.Empty y s b =
  RBT_Impl.Branch RBT_Impl.R (rbt_comp_del c x RBT_Impl.Empty) y s b;
rbt_comp_del_from_left c x (RBT_Impl.Branch RBT_Impl.R va vb vc vd) y s b =
  RBT_Impl.Branch RBT_Impl.R
    (rbt_comp_del c x (RBT_Impl.Branch RBT_Impl.R va vb vc vd)) y s b;

rbt_comp_del_from_right ::
  forall a b.
    (a -> a -> Comparator.Order) ->
      a -> RBT_Impl.Rbt a b -> a -> b -> RBT_Impl.Rbt a b -> RBT_Impl.Rbt a b;
rbt_comp_del_from_right c x a y s (RBT_Impl.Branch RBT_Impl.B lt z v rt) =
  RBT_Impl.balance_right a y s
    (rbt_comp_del c x (RBT_Impl.Branch RBT_Impl.B lt z v rt));
rbt_comp_del_from_right c x a y s RBT_Impl.Empty =
  RBT_Impl.Branch RBT_Impl.R a y s (rbt_comp_del c x RBT_Impl.Empty);
rbt_comp_del_from_right c x a y s (RBT_Impl.Branch RBT_Impl.R va vb vc vd) =
  RBT_Impl.Branch RBT_Impl.R a y s
    (rbt_comp_del c x (RBT_Impl.Branch RBT_Impl.R va vb vc vd));

rbt_comp_delete ::
  forall a b.
    (a -> a -> Comparator.Order) -> a -> RBT_Impl.Rbt a b -> RBT_Impl.Rbt a b;
rbt_comp_delete c k t = RBT_Impl.paint RBT_Impl.B (rbt_comp_del c k t);

rbt_split_comp ::
  forall a b.
    (a -> a -> Comparator.Order) ->
      RBT_Impl.Rbt a b -> a -> (RBT_Impl.Rbt a b, (Maybe b, RBT_Impl.Rbt a b));
rbt_split_comp c RBT_Impl.Empty k = (RBT_Impl.Empty, (Nothing, RBT_Impl.Empty));
rbt_split_comp c (RBT_Impl.Branch uu l a b r) x =
  (case c x a of {
    Comparator.Eqa -> (l, (Just b, r));
    Comparator.Lt ->
      (case rbt_split_comp c l x of {
        (l1, (beta, l2)) -> (l1, (beta, RBT_Impl.rbt_join l2 a b r));
      });
    Comparator.Gt ->
      (case rbt_split_comp c r x of {
        (r1, (beta, r2)) -> (RBT_Impl.rbt_join l a b r1, (beta, r2));
      });
  });

comp_minus ::
  forall a b.
    (a -> a -> Comparator.Order) ->
      RBT_Impl.Rbt a b -> RBT_Impl.Rbt a b -> RBT_Impl.Rbt a b;
comp_minus c t1 t2 =
  (if RBT_Impl.small_rbt t2
    then RBT_Impl.fold (\ k _ -> rbt_comp_delete c k) t2 t1
    else (if RBT_Impl.small_rbt t1
           then RBT_Impl.rbtreeify (filter_comp_minus c t1 t2)
           else (case t2 of {
                  RBT_Impl.Empty -> t1;
                  RBT_Impl.Branch _ l2 a _ r2 ->
                    (case rbt_split_comp c t1 a of {
                      (l1, (_, r1)) ->
                        RBT_Impl.rbt_join2 (comp_minus c l1 l2)
                          (comp_minus c r1 r2);
                    });
                })));

rbt_comp_ins ::
  forall a b.
    (a -> a -> Comparator.Order) ->
      (a -> b -> b -> b) -> a -> b -> RBT_Impl.Rbt a b -> RBT_Impl.Rbt a b;
rbt_comp_ins c f k v RBT_Impl.Empty =
  RBT_Impl.Branch RBT_Impl.R RBT_Impl.Empty k v RBT_Impl.Empty;
rbt_comp_ins c f k v (RBT_Impl.Branch RBT_Impl.B l x y r) =
  (case c k x of {
    Comparator.Eqa -> RBT_Impl.Branch RBT_Impl.B l x (f k y v) r;
    Comparator.Lt -> RBT_Impl.balance (rbt_comp_ins c f k v l) x y r;
    Comparator.Gt -> RBT_Impl.balance l x y (rbt_comp_ins c f k v r);
  });
rbt_comp_ins c f k v (RBT_Impl.Branch RBT_Impl.R l x y r) =
  (case c k x of {
    Comparator.Eqa -> RBT_Impl.Branch RBT_Impl.R l x (f k y v) r;
    Comparator.Lt -> RBT_Impl.Branch RBT_Impl.R (rbt_comp_ins c f k v l) x y r;
    Comparator.Gt -> RBT_Impl.Branch RBT_Impl.R l x y (rbt_comp_ins c f k v r);
  });

rbt_comp_minus ::
  forall a b.
    (a -> a -> Comparator.Order) ->
      RBT_Impl.Rbt a b -> RBT_Impl.Rbt a b -> RBT_Impl.Rbt a b;
rbt_comp_minus c t1 t2 = RBT_Impl.paint RBT_Impl.B (comp_minus c t1 t2);

rbt_comp_insert_with_key ::
  forall a b.
    (a -> a -> Comparator.Order) ->
      (a -> b -> b -> b) -> a -> b -> RBT_Impl.Rbt a b -> RBT_Impl.Rbt a b;
rbt_comp_insert_with_key c f k v t =
  RBT_Impl.paint RBT_Impl.B (rbt_comp_ins c f k v t);

rbt_comp_insert ::
  forall a b.
    (a -> a -> Comparator.Order) ->
      a -> b -> RBT_Impl.Rbt a b -> RBT_Impl.Rbt a b;
rbt_comp_insert c = rbt_comp_insert_with_key c (\ _ _ nv -> nv);

map_filter_comp_inter ::
  forall a b c d.
    (a -> a -> Comparator.Order) ->
      (a -> b -> c -> d) -> RBT_Impl.Rbt a b -> RBT_Impl.Rbt a c -> [(a, d)];
map_filter_comp_inter c f t1 t2 =
  List.map_filter (\ (k, v) -> (case rbt_comp_lookup c t1 k of {
                                 Nothing -> Nothing;
                                 Just va -> Just (k, f k va v);
                               }))
    (RBT_Impl.entries t2);

rbt_comp_inter_swap_rec ::
  forall a b.
    (a -> a -> Comparator.Order) ->
      (a -> b -> b -> b) ->
        Bool -> RBT_Impl.Rbt a b -> RBT_Impl.Rbt a b -> RBT_Impl.Rbt a b;
rbt_comp_inter_swap_rec c f gamma t1 t2 =
  let {
    bh1 = RBT_Impl.bheight t1;
    bh2 = RBT_Impl.bheight t2;
  } in (case (if Arith.less_nat bh1 bh2 then (not gamma, (t1, (bh1, (t2, bh2))))
               else (gamma, (t2, (bh2, (t1, bh1)))))
         of {
         (gammaa, (t2a, (bh2a, (t1a, _)))) ->
           let {
             fa = (if gammaa then (\ k v va -> f k va v) else f);
           } in (if Arith.less_nat bh2a (Arith.nat_of_integer (4 :: Integer))
                  then RBT_Impl.rbtreeify (map_filter_comp_inter c fa t1a t2a)
                  else (case t1a of {
                         RBT_Impl.Empty -> RBT_Impl.Empty;
                         RBT_Impl.Branch _ l1 a b r1 ->
                           (case rbt_split_comp c t2a a of {
                             (l2, (beta, r2)) ->
                               let {
                                 l = rbt_comp_inter_swap_rec c f gammaa l1 l2;
                                 r = rbt_comp_inter_swap_rec c f gammaa r1 r2;
                               } in (case beta of {
                                      Nothing -> RBT_Impl.rbt_join2 l r;
                                      Just ba ->
RBT_Impl.rbt_join l a (fa a b ba) r;
                                    });
                           });
                       }));
       });

rbt_comp_inter_with_key ::
  forall a b.
    (a -> a -> Comparator.Order) ->
      (a -> b -> b -> b) ->
        RBT_Impl.Rbt a b -> RBT_Impl.Rbt a b -> RBT_Impl.Rbt a b;
rbt_comp_inter_with_key c f t1 t2 =
  RBT_Impl.paint RBT_Impl.B (rbt_comp_inter_swap_rec c f False t1 t2);

rbt_comp_union_swap_rec ::
  forall a b.
    (a -> a -> Comparator.Order) ->
      (a -> b -> b -> b) ->
        Bool -> RBT_Impl.Rbt a b -> RBT_Impl.Rbt a b -> RBT_Impl.Rbt a b;
rbt_comp_union_swap_rec c f gamma t1 t2 =
  let {
    bh1 = RBT_Impl.bheight t1;
    bh2 = RBT_Impl.bheight t2;
  } in (case (if Arith.less_nat bh1 bh2 then (not gamma, (t1, (bh1, (t2, bh2))))
               else (gamma, (t2, (bh2, (t1, bh1)))))
         of {
         (gammaa, (t2a, (bh2a, (t1a, _)))) ->
           let {
             fa = (if gammaa then (\ k v va -> f k va v) else f);
           } in (if Arith.less_nat bh2a (Arith.nat_of_integer (4 :: Integer))
                  then RBT_Impl.fold (rbt_comp_insert_with_key c fa) t2a t1a
                  else (case t1a of {
                         RBT_Impl.Empty -> t2a;
                         RBT_Impl.Branch _ l1 a b r1 ->
                           (case rbt_split_comp c t2a a of {
                             (l2, (beta, r2)) ->
                               RBT_Impl.rbt_join
                                 (rbt_comp_union_swap_rec c f gammaa l1 l2) a
                                 (case beta of {
                                   Nothing -> b;
                                   Just ca -> fa a b ca;
                                 })
                                 (rbt_comp_union_swap_rec c f gammaa r1 r2);
                           });
                       }));
       });

rbt_comp_union_with_key ::
  forall a b.
    (a -> a -> Comparator.Order) ->
      (a -> b -> b -> b) ->
        RBT_Impl.Rbt a b -> RBT_Impl.Rbt a b -> RBT_Impl.Rbt a b;
rbt_comp_union_with_key c f t1 t2 =
  RBT_Impl.paint RBT_Impl.B (rbt_comp_union_swap_rec c f False t1 t2);

}
