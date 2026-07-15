{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Multihole_Context(Mctxt(..), equal_mctxt, hole_poss, fill_holes, split_term,
                     uncap_till, funas_mctxt, ground_mctxt, if_Fun_in_set,
                     funas_mctxt_list, vars_mctxt, subst_apply_mctxt)
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
import qualified Multihole_Context_Impl;
import qualified Option;
import qualified Complete_Lattices;
import qualified Compare;
import qualified Container_Setup;
import qualified Cardinality;
import qualified Collection_Enum;
import qualified HOL;
import qualified Term;
import qualified Groups_List;
import qualified List;
import qualified Phantom_Type;
import qualified Set;
import qualified Arith;
import qualified Set_Impl;
import qualified Collection_Order;
import qualified Collection_Eq;

data Mctxt a b = MVar b | MHole | MFun a [Mctxt a b];

instance (Eq a, Eq b) => Eq (Mctxt a b) where {
  a == b = equal_mctxt a b;
};

equal_mctxt :: forall a b. (Eq a, Eq b) => Mctxt a b -> Mctxt a b -> Bool;
equal_mctxt MHole (MFun x31 x32) = False;
equal_mctxt (MFun x31 x32) MHole = False;
equal_mctxt (MVar x1) (MFun x31 x32) = False;
equal_mctxt (MFun x31 x32) (MVar x1) = False;
equal_mctxt (MVar x1) MHole = False;
equal_mctxt MHole (MVar x1) = False;
equal_mctxt (MFun x31 x32) (MFun y31 y32) = x31 == y31 && x32 == y32;
equal_mctxt (MVar x1) (MVar y1) = x1 == y1;
equal_mctxt MHole MHole = True;

hole_poss :: forall a b. Mctxt a b -> Set.Set [Arith.Nat];
hole_poss (MVar x) =
  Set_Impl.set_empty (Phantom_Type.of_phantom Set_Impl.set_impl_list);
hole_poss MHole =
  Set.insert []
    (Set_Impl.set_empty (Phantom_Type.of_phantom Set_Impl.set_impl_list));
hole_poss (MFun f cs) =
  List.foldr
    (Set.sup_set .
      (\ i -> Set.image (\ a -> i : a) (hole_poss (List.nth cs i))))
    (List.upt Arith.zero_nat (List.size_list cs))
    (Set_Impl.set_empty (Phantom_Type.of_phantom Set_Impl.set_impl_list));

num_holes :: forall a b. Mctxt a b -> Arith.Nat;
num_holes (MVar uu) = Arith.zero_nat;
num_holes MHole = Arith.one_nat;
num_holes (MFun uv ctxts) = Groups_List.sum_list (map num_holes ctxts);

partition_by :: forall a. [a] -> [Arith.Nat] -> [[a]];
partition_by xs [] = [];
partition_by xs (y : ys) = List.take y xs : partition_by (List.drop y xs) ys;

fill_holes :: forall a b. Mctxt a b -> [Term.Term a b] -> Term.Term a b;
fill_holes (MVar x) uu = Term.Var x;
fill_holes MHole [t] = t;
fill_holes (MFun f cs) ts =
  Term.Fun f
    (map (\ i ->
           fill_holes (List.nth cs i)
             (List.nth (partition_by ts (map num_holes cs)) i))
      (List.upt Arith.zero_nat (List.size_list cs)));

split_term ::
  forall a b.
    (Term.Term a b -> Bool) -> Term.Term a b -> (Mctxt a b, [Term.Term a b]);
split_term p (Term.Var x) =
  (if p (Term.Var x) then (MHole, [Term.Var x]) else (MVar x, []));
split_term p (Term.Fun f ts) =
  (if p (Term.Fun f ts) then (MHole, [Term.Fun f ts])
    else let {
           us = map (split_term p) ts;
         } in (MFun f (map fst us), concatMap snd us));

uncap_till ::
  forall a b. (Term.Term a b -> Bool) -> Term.Term a b -> [Term.Term a b];
uncap_till p (Term.Var x) = (if p (Term.Var x) then [Term.Var x] else []);
uncap_till p (Term.Fun f ts) =
  (if p (Term.Fun f ts) then [Term.Fun f ts] else concatMap (uncap_till p) ts);

funas_mctxt ::
  forall a b.
    (Cardinality.Finite_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Compare.Compare a, Eq a,
      Set_Impl.Set_impl a, Compare.Compare b,
      Eq b) => Mctxt a b -> Set.Set (a, Arith.Nat);
funas_mctxt (MFun f cs) =
  Set.sup_set (Set.insert (f, List.size_list cs) Set.bot_set)
    (Complete_Lattices.sup_set (Set.image funas_mctxt (List.set cs)));
funas_mctxt (MVar v) = Set.bot_set;
funas_mctxt MHole = Set.bot_set;

ground_mctxt :: forall a b. Mctxt a b -> Bool;
ground_mctxt (MVar uu) = False;
ground_mctxt MHole = True;
ground_mctxt (MFun f cs) = all ground_mctxt cs;

if_Fun_in_set ::
  forall a b.
    (Collection_Eq.Ceq a,
      Collection_Order.Ccompare a) => Set.Set (a, Arith.Nat) ->
Term.Term a b -> Bool;
if_Fun_in_set f =
  (\ t -> Term.is_Var t || Set.member (Option.the (Term.root t)) f);

mctxt_of_term :: forall a b. Term.Term a b -> Mctxt a b;
mctxt_of_term (Term.Var x) = MVar x;
mctxt_of_term (Term.Fun f ts) = MFun f (map mctxt_of_term ts);

funas_mctxt_list :: forall a b. Mctxt a b -> [(a, Arith.Nat)];
funas_mctxt_list c = Multihole_Context_Impl.add_funas_mctxt c [];

vars_mctxt ::
  forall a b.
    (Compare.Compare a, Eq a, Cardinality.Finite_UNIV b,
      Collection_Enum.Cenum b, Collection_Eq.Ceq b,
      Collection_Order.Cproper_interval b, Compare.Compare b, Eq b,
      Set_Impl.Set_impl b) => Mctxt a b -> Set.Set b;
vars_mctxt (MVar x1) = Set.insert x1 Set.bot_set;
vars_mctxt MHole = Set.bot_set;
vars_mctxt (MFun x31 x32) =
  Complete_Lattices.sup_set (Set.image vars_mctxt (List.set x32));

subst_apply_mctxt ::
  forall a b c. Mctxt a b -> (b -> Term.Term a c) -> Mctxt a c;
subst_apply_mctxt MHole uu = MHole;
subst_apply_mctxt (MVar x) sigma = mctxt_of_term (sigma x);
subst_apply_mctxt (MFun f cs) sigma =
  MFun f (map (\ c -> subst_apply_mctxt c sigma) cs);

}
