{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  RBT_Impl(Color(..), Rbt(..), fold, keys, paint, balance, bheight,
            balance_left, combine, entries, rbt_join, rbt_join2, rbtreeify,
            small_rbt, balance_right, rbt_union, rbt_delete, rbt_insert,
            rbt_lookup, rbt_bulkload)
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
import qualified Option;
import qualified Comparator;
import qualified Compare;
import qualified List;
import qualified Product_Type;
import qualified HOL;
import qualified Arith;

data Color = R | B;

data Rbt a b = Empty | Branch Color (Rbt a b) a b (Rbt a b);

fold :: forall a b c. (a -> b -> c -> c) -> Rbt a b -> c -> c;
fold f Empty x = x;
fold f (Branch c lt k v rt) x = fold f rt (f k v (fold f lt x));

gen_keys :: forall a b. [(a, Rbt a b)] -> Rbt a b -> [a];
gen_keys [] Empty = [];
gen_keys ((k, t) : kts) Empty = k : gen_keys kts t;
gen_keys kts (Branch c l k v r) = gen_keys ((k, r) : kts) l;

keys :: forall a b. Rbt a b -> [a];
keys = gen_keys [];

paint :: forall a b. Color -> Rbt a b -> Rbt a b;
paint c Empty = Empty;
paint c (Branch uu l k v r) = Branch c l k v r;

balance :: forall a b. Rbt a b -> a -> b -> Rbt a b -> Rbt a b;
balance (Branch R a w x b) s t (Branch R c y z d) =
  Branch R (Branch B a w x b) s t (Branch B c y z d);
balance (Branch R (Branch R a w x b) s t c) y z Empty =
  Branch R (Branch B a w x b) s t (Branch B c y z Empty);
balance (Branch R (Branch R a w x b) s t c) y z (Branch B va vb vc vd) =
  Branch R (Branch B a w x b) s t (Branch B c y z (Branch B va vb vc vd));
balance (Branch R Empty w x (Branch R b s t c)) y z Empty =
  Branch R (Branch B Empty w x b) s t (Branch B c y z Empty);
balance (Branch R (Branch B va vb vc vd) w x (Branch R b s t c)) y z Empty =
  Branch R (Branch B (Branch B va vb vc vd) w x b) s t (Branch B c y z Empty);
balance (Branch R Empty w x (Branch R b s t c)) y z (Branch B va vb vc vd) =
  Branch R (Branch B Empty w x b) s t (Branch B c y z (Branch B va vb vc vd));
balance (Branch R (Branch B ve vf vg vh) w x (Branch R b s t c)) y z
  (Branch B va vb vc vd) =
  Branch R (Branch B (Branch B ve vf vg vh) w x b) s t
    (Branch B c y z (Branch B va vb vc vd));
balance Empty w x (Branch R b s t (Branch R c y z d)) =
  Branch R (Branch B Empty w x b) s t (Branch B c y z d);
balance (Branch B va vb vc vd) w x (Branch R b s t (Branch R c y z d)) =
  Branch R (Branch B (Branch B va vb vc vd) w x b) s t (Branch B c y z d);
balance Empty w x (Branch R (Branch R b s t c) y z Empty) =
  Branch R (Branch B Empty w x b) s t (Branch B c y z Empty);
balance Empty w x (Branch R (Branch R b s t c) y z (Branch B va vb vc vd)) =
  Branch R (Branch B Empty w x b) s t (Branch B c y z (Branch B va vb vc vd));
balance (Branch B va vb vc vd) w x (Branch R (Branch R b s t c) y z Empty) =
  Branch R (Branch B (Branch B va vb vc vd) w x b) s t (Branch B c y z Empty);
balance (Branch B va vb vc vd) w x
  (Branch R (Branch R b s t c) y z (Branch B ve vf vg vh)) =
  Branch R (Branch B (Branch B va vb vc vd) w x b) s t
    (Branch B c y z (Branch B ve vf vg vh));
balance Empty s t Empty = Branch B Empty s t Empty;
balance Empty s t (Branch B va vb vc vd) =
  Branch B Empty s t (Branch B va vb vc vd);
balance Empty s t (Branch v Empty vb vc Empty) =
  Branch B Empty s t (Branch v Empty vb vc Empty);
balance Empty s t (Branch v (Branch B ve vf vg vh) vb vc Empty) =
  Branch B Empty s t (Branch v (Branch B ve vf vg vh) vb vc Empty);
balance Empty s t (Branch v Empty vb vc (Branch B vf vg vh vi)) =
  Branch B Empty s t (Branch v Empty vb vc (Branch B vf vg vh vi));
balance Empty s t (Branch v (Branch B ve vj vk vl) vb vc (Branch B vf vg vh vi))
  = Branch B Empty s t
      (Branch v (Branch B ve vj vk vl) vb vc (Branch B vf vg vh vi));
balance (Branch B va vb vc vd) s t Empty =
  Branch B (Branch B va vb vc vd) s t Empty;
balance (Branch B va vb vc vd) s t (Branch B ve vf vg vh) =
  Branch B (Branch B va vb vc vd) s t (Branch B ve vf vg vh);
balance (Branch B va vb vc vd) s t (Branch v Empty vf vg Empty) =
  Branch B (Branch B va vb vc vd) s t (Branch v Empty vf vg Empty);
balance (Branch B va vb vc vd) s t (Branch v (Branch B vi vj vk vl) vf vg Empty)
  = Branch B (Branch B va vb vc vd) s t
      (Branch v (Branch B vi vj vk vl) vf vg Empty);
balance (Branch B va vb vc vd) s t (Branch v Empty vf vg (Branch B vj vk vl vm))
  = Branch B (Branch B va vb vc vd) s t
      (Branch v Empty vf vg (Branch B vj vk vl vm));
balance (Branch B va vb vc vd) s t
  (Branch v (Branch B vi vn vo vp) vf vg (Branch B vj vk vl vm)) =
  Branch B (Branch B va vb vc vd) s t
    (Branch v (Branch B vi vn vo vp) vf vg (Branch B vj vk vl vm));
balance (Branch v Empty vb vc Empty) s t Empty =
  Branch B (Branch v Empty vb vc Empty) s t Empty;
balance (Branch v Empty vb vc (Branch B ve vf vg vh)) s t Empty =
  Branch B (Branch v Empty vb vc (Branch B ve vf vg vh)) s t Empty;
balance (Branch v (Branch B vf vg vh vi) vb vc Empty) s t Empty =
  Branch B (Branch v (Branch B vf vg vh vi) vb vc Empty) s t Empty;
balance (Branch v (Branch B vf vg vh vi) vb vc (Branch B ve vj vk vl)) s t Empty
  = Branch B (Branch v (Branch B vf vg vh vi) vb vc (Branch B ve vj vk vl)) s t
      Empty;
balance (Branch v Empty vf vg Empty) s t (Branch B va vb vc vd) =
  Branch B (Branch v Empty vf vg Empty) s t (Branch B va vb vc vd);
balance (Branch v Empty vf vg (Branch B vi vj vk vl)) s t (Branch B va vb vc vd)
  = Branch B (Branch v Empty vf vg (Branch B vi vj vk vl)) s t
      (Branch B va vb vc vd);
balance (Branch v (Branch B vj vk vl vm) vf vg Empty) s t (Branch B va vb vc vd)
  = Branch B (Branch v (Branch B vj vk vl vm) vf vg Empty) s t
      (Branch B va vb vc vd);
balance (Branch v (Branch B vj vk vl vm) vf vg (Branch B vi vn vo vp)) s t
  (Branch B va vb vc vd) =
  Branch B (Branch v (Branch B vj vk vl vm) vf vg (Branch B vi vn vo vp)) s t
    (Branch B va vb vc vd);

equal_color :: Color -> Color -> Bool;
equal_color R B = False;
equal_color B R = False;
equal_color B B = True;
equal_color R R = True;

bheight :: forall a b. Rbt a b -> Arith.Nat;
bheight Empty = Arith.zero_nat;
bheight (Branch c lt k v rt) =
  (if equal_color c B then Arith.suc (bheight lt) else bheight lt);

balance_left :: forall a b. Rbt a b -> a -> b -> Rbt a b -> Rbt a b;
balance_left (Branch R a k x b) s y c = Branch R (Branch B a k x b) s y c;
balance_left Empty k x (Branch B a s y b) =
  balance Empty k x (Branch R a s y b);
balance_left (Branch B va vb vc vd) k x (Branch B a s y b) =
  balance (Branch B va vb vc vd) k x (Branch R a s y b);
balance_left Empty k x (Branch R (Branch B a s y b) t z c) =
  Branch R (Branch B Empty k x a) s y (balance b t z (paint R c));
balance_left (Branch B va vb vc vd) k x (Branch R (Branch B a s y b) t z c) =
  Branch R (Branch B (Branch B va vb vc vd) k x a) s y
    (balance b t z (paint R c));
balance_left Empty k x Empty = Empty;
balance_left Empty k x (Branch R Empty vb vc vd) = Empty;
balance_left Empty k x (Branch R (Branch R ve vf vg vh) vb vc vd) = Empty;
balance_left (Branch B va vb vc vd) k x Empty = Empty;
balance_left (Branch B va vb vc vd) k x (Branch R Empty vf vg vh) = Empty;
balance_left (Branch B va vb vc vd) k x
  (Branch R (Branch R vi vj vk vl) vf vg vh) = Empty;

combine :: forall a b. Rbt a b -> Rbt a b -> Rbt a b;
combine Empty x = x;
combine (Branch v va vb vc vd) Empty = Branch v va vb vc vd;
combine (Branch R a k x b) (Branch R c s y d) =
  (case combine b c of {
    Empty -> Branch R a k x (Branch R Empty s y d);
    Branch R b2 t z c2 -> Branch R (Branch R a k x b2) t z (Branch R c2 s y d);
    Branch B b2 t z c2 -> Branch R a k x (Branch R (Branch B b2 t z c2) s y d);
  });
combine (Branch B a k x b) (Branch B c s y d) =
  (case combine b c of {
    Empty -> balance_left a k x (Branch B Empty s y d);
    Branch R b2 t z c2 -> Branch R (Branch B a k x b2) t z (Branch B c2 s y d);
    Branch B b2 t z c2 ->
      balance_left a k x (Branch B (Branch B b2 t z c2) s y d);
  });
combine (Branch B va vb vc vd) (Branch R b k x c) =
  Branch R (combine (Branch B va vb vc vd) b) k x c;
combine (Branch R a k x b) (Branch B va vb vc vd) =
  Branch R a k x (combine b (Branch B va vb vc vd));

gen_entries :: forall a b. [((a, b), Rbt a b)] -> Rbt a b -> [(a, b)];
gen_entries [] Empty = [];
gen_entries ((kv, t) : kvts) Empty = kv : gen_entries kvts t;
gen_entries kvts (Branch c l k v r) = gen_entries (((k, v), r) : kvts) l;

entries :: forall a b. Rbt a b -> [(a, b)];
entries = gen_entries [];

flip_rbt :: forall a b. Rbt a b -> Rbt a b -> Bool;
flip_rbt t1 t2 = Arith.less_nat (bheight t2) (bheight t1);

rbt_baliR :: forall a b. Rbt a b -> a -> b -> Rbt a b -> Rbt a b;
rbt_baliR t1 ab bb (Branch R t2 aa ba (Branch R t3 a b t4)) =
  Branch R (Branch B t1 ab bb t2) aa ba (Branch B t3 a b t4);
rbt_baliR t1 ab bb (Branch R (Branch R t2 aa ba t3) a b Empty) =
  Branch R (Branch B t1 ab bb t2) aa ba (Branch B t3 a b Empty);
rbt_baliR t1 ab bb (Branch R (Branch R t2 aa ba t3) a b (Branch B va vb vc vd))
  = Branch R (Branch B t1 ab bb t2) aa ba
      (Branch B t3 a b (Branch B va vb vc vd));
rbt_baliR t1 a b Empty = Branch B t1 a b Empty;
rbt_baliR t1 a b (Branch B va vb vc vd) =
  Branch B t1 a b (Branch B va vb vc vd);
rbt_baliR t1 a b (Branch v Empty vb vc Empty) =
  Branch B t1 a b (Branch v Empty vb vc Empty);
rbt_baliR t1 a b (Branch v (Branch B ve vf vg vh) vb vc Empty) =
  Branch B t1 a b (Branch v (Branch B ve vf vg vh) vb vc Empty);
rbt_baliR t1 a b (Branch v Empty vb vc (Branch B vf vg vh vi)) =
  Branch B t1 a b (Branch v Empty vb vc (Branch B vf vg vh vi));
rbt_baliR t1 a b (Branch v (Branch B ve vj vk vl) vb vc (Branch B vf vg vh vi))
  = Branch B t1 a b
      (Branch v (Branch B ve vj vk vl) vb vc (Branch B vf vg vh vi));

rbt_joinR :: forall a b. Rbt a b -> a -> b -> Rbt a b -> Rbt a b;
rbt_joinR l a b r =
  (if Arith.less_eq_nat (bheight l) (bheight r) then Branch R l a b r
    else (case l of {
           Branch R la ab ba ra -> Branch R la ab ba (rbt_joinR ra a b r);
           Branch B la ab ba ra -> rbt_baliR la ab ba (rbt_joinR ra a b r);
         }));

rbt_baliL :: forall a b. Rbt a b -> a -> b -> Rbt a b -> Rbt a b;
rbt_baliL (Branch R (Branch R t1 ab bb t2) aa ba t3) a b t4 =
  Branch R (Branch B t1 ab bb t2) aa ba (Branch B t3 a b t4);
rbt_baliL (Branch R Empty ab bb (Branch R t2 aa ba t3)) a b t4 =
  Branch R (Branch B Empty ab bb t2) aa ba (Branch B t3 a b t4);
rbt_baliL (Branch R (Branch B va vb vc vd) ab bb (Branch R t2 aa ba t3)) a b t4
  = Branch R (Branch B (Branch B va vb vc vd) ab bb t2) aa ba
      (Branch B t3 a b t4);
rbt_baliL Empty a b t2 = Branch B Empty a b t2;
rbt_baliL (Branch B va vb vc vd) a b t2 =
  Branch B (Branch B va vb vc vd) a b t2;
rbt_baliL (Branch v Empty vb vc Empty) a b t2 =
  Branch B (Branch v Empty vb vc Empty) a b t2;
rbt_baliL (Branch v Empty vb vc (Branch B ve vf vg vh)) a b t2 =
  Branch B (Branch v Empty vb vc (Branch B ve vf vg vh)) a b t2;
rbt_baliL (Branch v (Branch B vf vg vh vi) vb vc Empty) a b t2 =
  Branch B (Branch v (Branch B vf vg vh vi) vb vc Empty) a b t2;
rbt_baliL (Branch v (Branch B vf vg vh vi) vb vc (Branch B ve vj vk vl)) a b t2
  = Branch B (Branch v (Branch B vf vg vh vi) vb vc (Branch B ve vj vk vl)) a b
      t2;

rbt_joinL :: forall a b. Rbt a b -> a -> b -> Rbt a b -> Rbt a b;
rbt_joinL l a b r =
  (if Arith.less_eq_nat (bheight r) (bheight l) then Branch R l a b r
    else (case r of {
           Branch R la ab ba ra -> Branch R (rbt_joinL l a b la) ab ba ra;
           Branch B la ab ba ra -> rbt_baliL (rbt_joinL l a b la) ab ba ra;
         }));

rbt_join :: forall a b. Rbt a b -> a -> b -> Rbt a b -> Rbt a b;
rbt_join l a b r =
  let {
    bhl = bheight l;
    bhr = bheight r;
  } in (if Arith.less_nat bhr bhl then paint B (rbt_joinR l a b r)
         else (if Arith.less_nat bhl bhr then paint B (rbt_joinL l a b r)
                else Branch B l a b r));

is_rbt_empty :: forall a b. Rbt a b -> Bool;
is_rbt_empty t = (case t of {
                   Empty -> True;
                   Branch _ _ _ _ _ -> False;
                 });

rbt_split_min :: forall a b. Rbt a b -> (a, (b, Rbt a b));
rbt_split_min Empty = error "undefined";
rbt_split_min (Branch uu l a b r) =
  (if is_rbt_empty l then (a, (b, r))
    else (case rbt_split_min l of {
           (aa, (ba, la)) -> (aa, (ba, rbt_join la a b r));
         }));

rbt_join2 :: forall a b. Rbt a b -> Rbt a b -> Rbt a b;
rbt_join2 l r =
  (if is_rbt_empty r then l else (case rbt_split_min r of {
                                   (a, (b, c)) -> rbt_join l a b c;
                                 }));

rbtreeify_g :: forall a b. Arith.Nat -> [(a, b)] -> (Rbt a b, [(a, b)]);
rbtreeify_g n kvs =
  (if Arith.equal_nat n Arith.zero_nat || Arith.equal_nat n Arith.one_nat
    then (Empty, kvs)
    else (case Arith.divmod_nat n (Arith.nat_of_integer (2 :: Integer)) of {
           (na, r) ->
             (if Arith.equal_nat r Arith.zero_nat
               then (case rbtreeify_g na kvs of {
                      (t1, (k, v) : kvsa) ->
                        Product_Type.apfst (Branch B t1 k v)
                          (rbtreeify_g na kvsa);
                    })
               else (case rbtreeify_f na kvs of {
                      (t1, (k, v) : kvsa) ->
                        Product_Type.apfst (Branch B t1 k v)
                          (rbtreeify_g na kvsa);
                    }));
         }));

rbtreeify_f :: forall a b. Arith.Nat -> [(a, b)] -> (Rbt a b, [(a, b)]);
rbtreeify_f n kvs =
  (if Arith.equal_nat n Arith.zero_nat then (Empty, kvs)
    else (if Arith.equal_nat n Arith.one_nat
           then (case kvs of {
                  (k, v) : kvsa -> (Branch R Empty k v Empty, kvsa);
                })
           else (case Arith.divmod_nat n (Arith.nat_of_integer (2 :: Integer))
                  of {
                  (na, r) ->
                    (if Arith.equal_nat r Arith.zero_nat
                      then (case rbtreeify_f na kvs of {
                             (t1, (k, v) : kvsa) ->
                               Product_Type.apfst (Branch B t1 k v)
                                 (rbtreeify_g na kvsa);
                           })
                      else (case rbtreeify_f na kvs of {
                             (t1, (k, v) : kvsa) ->
                               Product_Type.apfst (Branch B t1 k v)
                                 (rbtreeify_f na kvsa);
                           }));
                })));

rbtreeify :: forall a b. [(a, b)] -> Rbt a b;
rbtreeify kvs = fst (rbtreeify_g (Arith.suc (List.size_list kvs)) kvs);

small_rbt :: forall a b. Rbt a b -> Bool;
small_rbt t = Arith.less_nat (bheight t) (Arith.nat_of_integer (4 :: Integer));

balance_right :: forall a b. Rbt a b -> a -> b -> Rbt a b -> Rbt a b;
balance_right a k x (Branch R b s y c) = Branch R a k x (Branch B b s y c);
balance_right (Branch B a k x b) s y Empty =
  balance (Branch R a k x b) s y Empty;
balance_right (Branch B a k x b) s y (Branch B va vb vc vd) =
  balance (Branch R a k x b) s y (Branch B va vb vc vd);
balance_right (Branch R a k x (Branch B b s y c)) t z Empty =
  Branch R (balance (paint R a) k x b) s y (Branch B c t z Empty);
balance_right (Branch R a k x (Branch B b s y c)) t z (Branch B va vb vc vd) =
  Branch R (balance (paint R a) k x b) s y
    (Branch B c t z (Branch B va vb vc vd));
balance_right Empty k x Empty = Empty;
balance_right (Branch R va vb vc Empty) k x Empty = Empty;
balance_right (Branch R va vb vc (Branch R ve vf vg vh)) k x Empty = Empty;
balance_right Empty k x (Branch B va vb vc vd) = Empty;
balance_right (Branch R ve vf vg Empty) k x (Branch B va vb vc vd) = Empty;
balance_right (Branch R ve vf vg (Branch R vi vj vk vl)) k x
  (Branch B va vb vc vd) = Empty;

rbt_del :: forall a b. (Compare.Compare_order a) => a -> Rbt a b -> Rbt a b;
rbt_del x Empty = Empty;
rbt_del x (Branch c a y s b) = (case Compare.compare x y of {
                                 Comparator.Eqa -> combine a b;
                                 Comparator.Lt -> rbt_del_from_left x a y s b;
                                 Comparator.Gt -> rbt_del_from_right x a y s b;
                               });

rbt_del_from_left ::
  forall a b.
    (Compare.Compare_order a) => a -> Rbt a b -> a -> b -> Rbt a b -> Rbt a b;
rbt_del_from_left x (Branch B lt z v rt) y s b =
  balance_left (rbt_del x (Branch B lt z v rt)) y s b;
rbt_del_from_left x Empty y s b = Branch R (rbt_del x Empty) y s b;
rbt_del_from_left x (Branch R va vb vc vd) y s b =
  Branch R (rbt_del x (Branch R va vb vc vd)) y s b;

rbt_del_from_right ::
  forall a b.
    (Compare.Compare_order a) => a -> Rbt a b -> a -> b -> Rbt a b -> Rbt a b;
rbt_del_from_right x a y s (Branch B lt z v rt) =
  balance_right a y s (rbt_del x (Branch B lt z v rt));
rbt_del_from_right x a y s Empty = Branch R a y s (rbt_del x Empty);
rbt_del_from_right x a y s (Branch R va vb vc vd) =
  Branch R a y s (rbt_del x (Branch R va vb vc vd));

rbt_ins ::
  forall a b.
    (Compare.Compare_order a) => (a -> b -> b -> b) ->
                                   a -> b -> Rbt a b -> Rbt a b;
rbt_ins f k v Empty = Branch R Empty k v Empty;
rbt_ins f k v (Branch B l x y r) =
  (case Compare.compare k x of {
    Comparator.Eqa -> Branch B l x (f k y v) r;
    Comparator.Lt -> balance (rbt_ins f k v l) x y r;
    Comparator.Gt -> balance l x y (rbt_ins f k v r);
  });
rbt_ins f k v (Branch R l x y r) =
  (case Compare.compare k x of {
    Comparator.Eqa -> Branch R l x (f k y v) r;
    Comparator.Lt -> Branch R (rbt_ins f k v l) x y r;
    Comparator.Gt -> Branch R l x y (rbt_ins f k v r);
  });

rbt_split ::
  forall a b.
    (Compare.Compare_order a) => Rbt a b -> a -> (Rbt a b, (Maybe b, Rbt a b));
rbt_split Empty k = (Empty, (Nothing, Empty));
rbt_split (Branch uu l a b r) x =
  (case Compare.compare x a of {
    Comparator.Eqa -> (l, (Just b, r));
    Comparator.Lt -> (case rbt_split l x of {
                       (l1, (beta, l2)) -> (l1, (beta, rbt_join l2 a b r));
                     });
    Comparator.Gt -> (case rbt_split r x of {
                       (r1, (beta, r2)) -> (rbt_join l a b r1, (beta, r2));
                     });
  });

rbt_insert_with_key ::
  forall a b.
    (Compare.Compare_order a) => (a -> b -> b -> b) ->
                                   a -> b -> Rbt a b -> Rbt a b;
rbt_insert_with_key f k v t = paint B (rbt_ins f k v t);

rbt_union_swap_rec ::
  forall a b.
    (Compare.Compare_order a) => (a -> b -> b -> b) ->
                                   Bool -> Rbt a b -> Rbt a b -> Rbt a b;
rbt_union_swap_rec f gamma t1 t2 =
  (case (if flip_rbt t2 t1 then (not gamma, (t1, t2)) else (gamma, (t2, t1))) of
    {
    (gammaa, (t2a, t1a)) ->
      let {
        fa = (if gammaa then (\ k v va -> f k va v) else f);
      } in (if small_rbt t2a then fold (rbt_insert_with_key fa) t2a t1a
             else (case t1a of {
                    Empty -> t2a;
                    Branch _ l1 a b r1 ->
                      (case rbt_split t2a a of {
                        (l2, (beta, r2)) ->
                          rbt_join (rbt_union_swap_rec f gammaa l1 l2) a
                            (case beta of {
                              Nothing -> b;
                              Just c -> fa a b c;
                            })
                            (rbt_union_swap_rec f gammaa r1 r2);
                      });
                  }));
  });

rbt_union_with_key ::
  forall a b.
    (Compare.Compare_order a) => (a -> b -> b -> b) ->
                                   Rbt a b -> Rbt a b -> Rbt a b;
rbt_union_with_key f t1 t2 = paint B (rbt_union_swap_rec f False t1 t2);

rbt_union ::
  forall a b. (Compare.Compare_order a) => Rbt a b -> Rbt a b -> Rbt a b;
rbt_union = rbt_union_with_key (\ _ _ rv -> rv);

rbt_delete :: forall a b. (Compare.Compare_order a) => a -> Rbt a b -> Rbt a b;
rbt_delete k t = paint B (rbt_del k t);

rbt_insert ::
  forall a b. (Compare.Compare_order a) => a -> b -> Rbt a b -> Rbt a b;
rbt_insert = rbt_insert_with_key (\ _ _ nv -> nv);

rbt_lookup :: forall a b. (Compare.Compare_order a) => Rbt a b -> a -> Maybe b;
rbt_lookup Empty k = Nothing;
rbt_lookup (Branch uu l x y r) k = (case Compare.compare k x of {
                                     Comparator.Eqa -> Just y;
                                     Comparator.Lt -> rbt_lookup l k;
                                     Comparator.Gt -> rbt_lookup r k;
                                   });

rbt_bulkload :: forall a b. (Compare.Compare_order a) => [(a, b)] -> Rbt a b;
rbt_bulkload xs = List.foldr (\ (a, b) -> rbt_insert a b) xs Empty;

}
