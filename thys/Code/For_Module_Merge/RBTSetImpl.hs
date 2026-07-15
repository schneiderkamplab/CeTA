{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  RBTSetImpl(memb_rm_basic_ops, empty_rm_basic_ops, delete_rm_basic_ops,
              ins_dj_rm_basic_ops, alpha_rm_basic_ops,
              g_bex_dflt_basic_oops_rm_basic_ops,
              g_ball_dflt_basic_oops_rm_basic_ops,
              g_inter_dflt_basic_oops_rm_basic_ops,
              g_isEmpty_dflt_basic_oops_rm_basic_ops,
              g_to_list_dflt_basic_oops_rm_basic_ops,
              g_from_list_dflt_basic_oops_rm_basic_ops)
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
import qualified RBT_add;
import qualified RBT_Impl;
import qualified Map;
import qualified Set;
import qualified Collection_Enum;
import qualified Orderings;
import qualified Option;
import qualified RBT;
import qualified Compare;

ins_rm_basic_ops ::
  forall a. (Compare.Compare_order a) => a -> RBT.Rbt a () -> RBT.Rbt a ();
ins_rm_basic_ops x s = RBT.insert x () s;

memb_rm_basic_ops ::
  forall a. (Compare.Compare_order a) => a -> RBT.Rbt a () -> Bool;
memb_rm_basic_ops x s = not (Option.is_none (RBT.lookup s x));

empty_rm_basic_ops :: forall a. (Orderings.Linorder a) => () -> RBT.Rbt a ();
empty_rm_basic_ops = (\ _ -> RBT.empty);

delete_rm_basic_ops ::
  forall a. (Compare.Compare_order a) => a -> RBT.Rbt a () -> RBT.Rbt a ();
delete_rm_basic_ops x s = RBT.delete x s;

ins_dj_rm_basic_ops ::
  forall a. (Compare.Compare_order a) => a -> RBT.Rbt a () -> RBT.Rbt a ();
ins_dj_rm_basic_ops x s = RBT.insert x () s;

alpha_rm_basic_ops ::
  forall a.
    (Collection_Enum.Cenum a,
      Compare.Compare_order a) => RBT.Rbt a () -> Set.Set a;
alpha_rm_basic_ops s = Map.dom (RBT.lookup s);

iteratei_bset_op_list_it_dflt_basic_oops_rm_basic_ops ::
  forall a b.
    (Orderings.Linorder a) => RBT.Rbt a () ->
                                (b -> Bool) -> (a -> b -> b) -> b -> b;
iteratei_bset_op_list_it_dflt_basic_oops_rm_basic_ops s =
  (\ c f -> RBT_add.rm_iterateoi (RBT.impl_of s) c (f . fst));

g_bex_dflt_basic_oops_rm_basic_ops ::
  forall a. (Orderings.Linorder a) => RBT.Rbt a () -> (a -> Bool) -> Bool;
g_bex_dflt_basic_oops_rm_basic_ops s p =
  iteratei_bset_op_list_it_dflt_basic_oops_rm_basic_ops s not (\ x _ -> p x)
    False;

g_ball_dflt_basic_oops_rm_basic_ops ::
  forall a. (Orderings.Linorder a) => RBT.Rbt a () -> (a -> Bool) -> Bool;
g_ball_dflt_basic_oops_rm_basic_ops s p =
  iteratei_bset_op_list_it_dflt_basic_oops_rm_basic_ops s (\ c -> c)
    (\ x _ -> p x) True;

g_inter_dflt_basic_oops_rm_basic_ops ::
  forall a.
    (Compare.Compare_order a) => RBT.Rbt a () -> RBT.Rbt a () -> RBT.Rbt a ();
g_inter_dflt_basic_oops_rm_basic_ops s1 s2 =
  iteratei_bset_op_list_it_dflt_basic_oops_rm_basic_ops s1 (\ _ -> True)
    (\ x s -> (if memb_rm_basic_ops x s2 then ins_dj_rm_basic_ops x s else s))
    (empty_rm_basic_ops ());

g_isEmpty_dflt_basic_oops_rm_basic_ops ::
  forall a. (Orderings.Linorder a) => RBT.Rbt a () -> Bool;
g_isEmpty_dflt_basic_oops_rm_basic_ops s =
  iteratei_bset_op_list_it_dflt_basic_oops_rm_basic_ops s (\ c -> c)
    (\ _ _ -> False) True;

g_to_list_dflt_basic_oops_rm_basic_ops ::
  forall a. (Orderings.Linorder a) => RBT.Rbt a () -> [a];
g_to_list_dflt_basic_oops_rm_basic_ops s =
  iteratei_bset_op_list_it_dflt_basic_oops_rm_basic_ops s (\ _ -> True)
    (\ a b -> a : b) [];

g_from_list_aux_dflt_basic_oops_rm_basic_ops ::
  forall a. (Compare.Compare_order a) => RBT.Rbt a () -> [a] -> RBT.Rbt a ();
g_from_list_aux_dflt_basic_oops_rm_basic_ops accs (x : l) =
  g_from_list_aux_dflt_basic_oops_rm_basic_ops (ins_rm_basic_ops x accs) l;
g_from_list_aux_dflt_basic_oops_rm_basic_ops y [] = y;

g_from_list_dflt_basic_oops_rm_basic_ops ::
  forall a. (Compare.Compare_order a) => [a] -> RBT.Rbt a ();
g_from_list_dflt_basic_oops_rm_basic_ops l =
  g_from_list_aux_dflt_basic_oops_rm_basic_ops (empty_rm_basic_ops ()) l;

}
