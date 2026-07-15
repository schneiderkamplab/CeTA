{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  RBT_ext(rbt_init, rbt_product, rBT_Impl_fold1, rBT_Impl_rbt_ex,
           rBT_Impl_rbt_all, rbt_keys_generator)
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
import qualified List_Fusion;
import qualified RBT_Impl;

rbt_init ::
  forall a b c. RBT_Impl.Rbt a b -> ([(c, RBT_Impl.Rbt a b)], RBT_Impl.Rbt a b);
rbt_init = (\ a -> ([], a));

rbt_product ::
  forall a b c d e.
    (a -> b -> c -> d -> e) ->
      RBT_Impl.Rbt a b -> RBT_Impl.Rbt c d -> RBT_Impl.Rbt (a, c) e;
rbt_product f rbt1 rbt2 =
  RBT_Impl.rbtreeify
    (reverse
      (RBT_Impl.fold
        (\ a b ->
          RBT_Impl.fold (\ c d -> (\ e -> ((a, c), f a b c d) : e)) rbt2)
        rbt1 []));

rbt_has_next ::
  forall a b c. ([(a, RBT_Impl.Rbt b c)], RBT_Impl.Rbt b c) -> Bool;
rbt_has_next ([], RBT_Impl.Empty) = False;
rbt_has_next (vb : vc, va) = True;
rbt_has_next (v, RBT_Impl.Branch vb vc vd ve vf) = True;

rbt_keys_next ::
  forall a b.
    ([(a, RBT_Impl.Rbt a b)], RBT_Impl.Rbt a b) ->
      (a, ([(a, RBT_Impl.Rbt a b)], RBT_Impl.Rbt a b));
rbt_keys_next ((k, t) : kts, RBT_Impl.Empty) = (k, (kts, t));
rbt_keys_next (kts, RBT_Impl.Branch c l k v r) =
  rbt_keys_next ((k, r) : kts, l);

rBT_Impl_fold1 :: forall a. (a -> a -> a) -> RBT_Impl.Rbt a () -> a;
rBT_Impl_fold1 f RBT_Impl.Empty = error "undefined";
rBT_Impl_fold1 f (RBT_Impl.Branch c RBT_Impl.Empty k v r) =
  RBT_Impl.fold (\ ka _ -> f ka) r k;
rBT_Impl_fold1 f (RBT_Impl.Branch ca (RBT_Impl.Branch c l ka va ra) k v r) =
  RBT_Impl.fold (\ kb _ -> f kb) r
    (f k (rBT_Impl_fold1 f (RBT_Impl.Branch c l ka va ra)));

rBT_Impl_rbt_ex :: forall a b. (a -> b -> Bool) -> RBT_Impl.Rbt a b -> Bool;
rBT_Impl_rbt_ex p RBT_Impl.Empty = False;
rBT_Impl_rbt_ex p (RBT_Impl.Branch c l k v r) =
  p k v || (rBT_Impl_rbt_ex p l || rBT_Impl_rbt_ex p r);

rBT_Impl_rbt_all :: forall a b. (a -> b -> Bool) -> RBT_Impl.Rbt a b -> Bool;
rBT_Impl_rbt_all p RBT_Impl.Empty = True;
rBT_Impl_rbt_all p (RBT_Impl.Branch c l k v r) =
  p k v && rBT_Impl_rbt_all p l && rBT_Impl_rbt_all p r;

rbt_keys_generator ::
  forall a b.
    List_Fusion.Generator a ([(a, RBT_Impl.Rbt a b)], RBT_Impl.Rbt a b);
rbt_keys_generator = List_Fusion.Generator (rbt_has_next, rbt_keys_next);

}
