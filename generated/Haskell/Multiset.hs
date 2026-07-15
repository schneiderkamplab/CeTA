{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Multiset(Multiset(..), subseteq_mset, equal_multiset, plus_multiset,
            zero_multiset, add_mset, mset, image_mset, minus_multiset,
            filter_mset, multeqp_code, sum_mset, size_multiset)
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
import qualified DAList_Multiset;
import qualified DAList;
import qualified Arith;

newtype Multiset a = Bag (DAList.Alist a Arith.Nat);

count :: forall a. (Eq a) => Multiset a -> a -> Arith.Nat;
count (Bag xs) = DAList_Multiset.count_of (DAList.impl_of xs);

subseteq_mset :: forall a. (Eq a) => Multiset a -> Multiset a -> Bool;
subseteq_mset (Bag xs) a =
  all (\ (x, n) -> Arith.less_eq_nat n (count a x)) (DAList.impl_of xs);

equal_multiset :: forall a. (Eq a) => Multiset a -> Multiset a -> Bool;
equal_multiset m1 m2 = subseteq_mset m1 m2 && subseteq_mset m2 m1;

instance (Eq a) => Eq (Multiset a) where {
  a == b = equal_multiset a b;
};

plus_multiset :: forall a. (Eq a) => Multiset a -> Multiset a -> Multiset a;
plus_multiset (Bag xs) (Bag ys) =
  Bag (DAList_Multiset.join (\ _ (a, b) -> Arith.plus_nat a b) xs ys);

instance (Eq a) => Arith.Plus (Multiset a) where {
  plus = plus_multiset;
};

zero_multiset :: forall a. Multiset a;
zero_multiset = Bag DAList.empty;

instance Arith.Zero (Multiset a) where {
  zero = zero_multiset;
};

instance (Eq a) => Arith.Semigroup_add (Multiset a) where {
};

instance (Eq a) => Arith.Monoid_add (Multiset a) where {
};

instance (Eq a) => Arith.Ab_semigroup_add (Multiset a) where {
};

instance (Eq a) => Arith.Comm_monoid_add (Multiset a) where {
};

add_mset :: forall a. (Eq a) => a -> Multiset a -> Multiset a;
add_mset x (Bag xs) =
  Bag (DAList_Multiset.join (\ _ (a, b) -> Arith.plus_nat a b)
        (DAList.update x Arith.one_nat DAList.empty) xs);

mset :: forall a. (Eq a) => [a] -> Multiset a;
mset [] = zero_multiset;
mset (a : x) = add_mset a (mset x);

set_mset ::
  forall a.
    (Arith.Ceq a, Arith.Ccompare a,
      Arith.Set_impl a) => Multiset a -> Arith.Set a;
set_mset (Bag ms) =
  DAList_Multiset.fold
    (\ a n ->
      (if Arith.equal_nat n Arith.zero_nat then (\ m -> m) else Arith.insert a))
    Arith.bot_set ms;

image_mset :: forall a b. (Eq b) => (a -> b) -> Multiset a -> Multiset b;
image_mset f (Bag ms) =
  DAList_Multiset.fold
    (\ a n -> plus_multiset (Bag (DAList_Multiset.single_alist_entry (f a) n)))
    zero_multiset ms;

minus_multiset :: forall a. (Eq a) => Multiset a -> Multiset a -> Multiset a;
minus_multiset (Bag xs) (Bag ys) = Bag (DAList_Multiset.subtract_entries xs ys);

inter_mset :: forall a. (Eq a) => Multiset a -> Multiset a -> Multiset a;
inter_mset a b = minus_multiset a (minus_multiset a b);

filter_mset :: forall a. (a -> Bool) -> Multiset a -> Multiset a;
filter_mset p (Bag xs) = Bag (DAList.filtera (p . fst) xs);

multeqp_code ::
  forall a.
    (Arith.Ceq a, Arith.Ccompare a, Eq a,
      Arith.Set_impl a) => (a -> a -> Bool) -> Multiset a -> Multiset a -> Bool;
multeqp_code p n m =
  let {
    z = inter_mset m n;
    x = minus_multiset m z;
    y = minus_multiset n z;
  } in Arith.ball (set_mset y) (\ ya -> Arith.bex (set_mset x) (p ya));

sum_mset :: forall a. (Arith.Comm_monoid_add a) => Multiset a -> a;
sum_mset (Bag ms) =
  DAList_Multiset.fold (\ a n -> Arith.funpow n (Arith.plus a)) Arith.zero ms;

size_multiset :: forall a. Multiset a -> Arith.Nat;
size_multiset (Bag ms) =
  DAList_Multiset.fold (\ _ -> Arith.plus_nat) Arith.zero_nat ms;

}
