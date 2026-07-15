{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  List(Interval, nth, upt, drop, find, fold, last, take, foldl, foldr, those,
        member, insert, union, butlast, extract, hd, tl, set_Cons, listset,
        product, remdups, remove1, subseqs, distinct, set, superset, enumerate,
        partition, removeAll, replicate, map_filter, list_update, lexordp,
        remdups_adj, rec_list, product_lists, inter_list_set, list_all2,
        lexordp_eq, interval, sort_key, size_list, all_interval,
        sorted_list_of_set)
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
import qualified RBT_Set2;
import qualified RBT_Mapping2;
import qualified DList_Set;
import qualified Comparator;
import qualified Efficient_Sort;
import qualified HOL;
import qualified Phantom_Type;
import qualified Set;
import qualified Set_Impl;
import qualified Collection_Order;
import qualified Collection_Eq;
import qualified Product_Type;
import qualified Option;
import qualified Orderings;
import qualified Arith;
import qualified Quasi_Order;

instance Quasi_Order.Quasi_order Arith.Int where {
};

instance Quasi_Order.Weak_order Arith.Int where {
};

class (Orderings.Linorder a,
        Arith.Comm_semiring_1_cancel a) => Interval a where {
};

instance Interval Arith.Nat where {
};

nth :: forall a. [a] -> Arith.Nat -> a;
nth (x : xs) n =
  (if Arith.equal_nat n Arith.zero_nat then x
    else nth xs (Arith.minus_nat n Arith.one_nat));

upt :: Arith.Nat -> Arith.Nat -> [Arith.Nat];
upt i j = (if Arith.less_nat i j then i : upt (Arith.suc i) j else []);

drop :: forall a. Arith.Nat -> [a] -> [a];
drop n [] = [];
drop n (x : xs) =
  (if Arith.equal_nat n Arith.zero_nat then x : xs
    else drop (Arith.minus_nat n Arith.one_nat) xs);

find :: forall a. (a -> Bool) -> [a] -> Maybe a;
find uu [] = Nothing;
find p (x : xs) = (if p x then Just x else find p xs);

fold :: forall a b. (a -> b -> b) -> [a] -> b -> b;
fold f [] s = s;
fold f (x : xs) s = fold f xs (f x s);

last :: forall a. [a] -> a;
last (x : xs) = (if null xs then x else last xs);

take :: forall a. Arith.Nat -> [a] -> [a];
take n [] = [];
take n (x : xs) =
  (if Arith.equal_nat n Arith.zero_nat then []
    else x : take (Arith.minus_nat n Arith.one_nat) xs);

foldl :: forall a b. (a -> b -> a) -> a -> [b] -> a;
foldl f a [] = a;
foldl f a (x : xs) = foldl f (f a x) xs;

foldr :: forall a b. (a -> b -> b) -> [a] -> b -> b;
foldr f [] = id;
foldr f (x : xs) = f x . foldr f xs;

those :: forall a. [Maybe a] -> Maybe [a];
those [] = Just [];
those (x : xs) = (case x of {
                   Nothing -> Nothing;
                   Just y -> Option.map_option (\ a -> y : a) (those xs);
                 });

member :: forall a. (Eq a) => [a] -> a -> Bool;
member [] y = False;
member (x : xs) y = x == y || member xs y;

insert :: forall a. (Eq a) => a -> [a] -> [a];
insert x xs = (if member xs x then xs else x : xs);

union :: forall a. (Eq a) => [a] -> [a] -> [a];
union = fold insert;

butlast :: forall a. [a] -> [a];
butlast [] = [];
butlast (x : xs) = (if null xs then [] else x : butlast xs);

extract :: forall a. (a -> Bool) -> [a] -> Maybe ([a], (a, [a]));
extract p [] = Nothing;
extract p (x : xs) =
  (if p x then Just ([], (x, xs))
    else (case extract p xs of {
           Nothing -> Nothing;
           Just (ys, (y, zs)) -> Just (x : ys, (y, zs));
         }));

hd :: forall a. [a] -> a;
hd (x21 : x22) = x21;

tl :: forall a. [a] -> [a];
tl [] = [];
tl (x21 : x22) = x22;

set_Cons ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Set_Impl.Set_impl a) => Set.Set a -> Set.Set [a] -> Set.Set [a];
set_Cons a xs =
  Set.image (\ (aa, b) -> aa : b)
    (Product_Type.product (Set.inf_set (Set.image (\ x -> x) a) Set.top_set)
      (Set.inf_set Set.top_set (Set.image (\ xsa -> xsa) xs)));

listset ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Set_Impl.Set_impl a) => [Set.Set a] -> Set.Set [a];
listset [] =
  Set.insert []
    (Set_Impl.set_empty (Phantom_Type.of_phantom Set_Impl.set_impl_list));
listset (a : asa) = set_Cons a (listset asa);

product :: forall a b. [a] -> [b] -> [(a, b)];
product [] uu = [];
product (x : xs) ys = map (\ a -> (x, a)) ys ++ product xs ys;

remdups :: forall a. (Eq a) => [a] -> [a];
remdups [] = [];
remdups (x : xs) = (if member xs x then remdups xs else x : remdups xs);

remove1 :: forall a. (Eq a) => a -> [a] -> [a];
remove1 x [] = [];
remove1 x (y : xs) = (if x == y then xs else y : remove1 x xs);

subseqs :: forall a. [a] -> [[a]];
subseqs [] = [[]];
subseqs (x : xs) = let {
                     xss = subseqs xs;
                   } in map (\ a -> x : a) xss ++ xss;

distinct :: forall a. (Eq a) => [a] -> Bool;
distinct [] = True;
distinct (x : xs) = not (member xs x) && distinct xs;

set ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Set_Impl.Set_impl a) => [a] -> Set.Set a;
set xs =
  Set_Impl.set_aux
    (Phantom_Type.of_phantom
      (Set_Impl.set_impl :: Phantom_Type.Phantom a Set_Impl.Set_impla))
    xs;

superset :: forall a. (Eq a) => [a] -> [a] -> Bool;
superset xs = all (member xs);

enumerate :: forall a. Arith.Nat -> [a] -> [(Arith.Nat, a)];
enumerate n [] = [];
enumerate n (x : xs) = (n, x) : enumerate (Arith.suc n) xs;

partition :: forall a. (a -> Bool) -> [a] -> ([a], [a]);
partition p [] = ([], []);
partition p (x : xs) =
  (case partition p xs of {
    (yes, no) -> (if p x then (x : yes, no) else (yes, x : no));
  });

removeAll :: forall a. (Eq a) => a -> [a] -> [a];
removeAll x [] = [];
removeAll x (y : xs) = (if x == y then removeAll x xs else y : removeAll x xs);

replicate :: forall a. Arith.Nat -> a -> [a];
replicate n x =
  (if Arith.equal_nat n Arith.zero_nat then []
    else x : replicate (Arith.minus_nat n Arith.one_nat) x);

map_filter :: forall a b. (a -> Maybe b) -> [a] -> [b];
map_filter f [] = [];
map_filter f (x : xs) = (case f x of {
                          Nothing -> map_filter f xs;
                          Just y -> y : map_filter f xs;
                        });

list_update :: forall a. [a] -> Arith.Nat -> a -> [a];
list_update [] i y = [];
list_update (x : xs) i y =
  (if Arith.equal_nat i Arith.zero_nat then y : xs
    else x : list_update xs (Arith.minus_nat i Arith.one_nat) y);

lexordp :: forall a. (a -> a -> Bool) -> [a] -> [a] -> Bool;
lexordp less [] ys = not (null ys);
lexordp less xs [] = False;
lexordp less (x : xs) (y : ys) =
  less x y || not (less y x) && lexordp less xs ys;

remdups_adj :: forall a. (Eq a) => [a] -> [a];
remdups_adj [] = [];
remdups_adj [x] = [x];
remdups_adj (x : y : xs) =
  (if x == y then remdups_adj (x : xs) else x : remdups_adj (y : xs));

rec_list :: forall a b. a -> (b -> [b] -> a -> a) -> [b] -> a;
rec_list f1 f2 [] = f1;
rec_list f1 f2 (x21 : x22) = f2 x21 x22 (rec_list f1 f2 x22);

product_lists :: forall a. [[a]] -> [[a]];
product_lists [] = [[]];
product_lists (xs : xss) =
  concatMap (\ x -> map (\ a -> x : a) (product_lists xss)) xs;

inter_list_set :: forall a. (Eq a) => [a] -> [a] -> [a];
inter_list_set xs ys = filter (member ys) xs;

length_tailrec :: forall a. [a] -> Arith.Nat -> Arith.Nat;
length_tailrec [] n = n;
length_tailrec (x : xs) n = length_tailrec xs (Arith.suc n);

list_all2 :: forall a b. (a -> b -> Bool) -> [a] -> [b] -> Bool;
list_all2 p [] ys = null ys;
list_all2 p xs [] = null xs;
list_all2 p (x : xs) (y : ys) = p x y && list_all2 p xs ys;

lexordp_eq :: forall a. (a -> a -> Bool) -> [a] -> [a] -> Bool;
lexordp_eq less [] ys = True;
lexordp_eq less xs [] = null xs;
lexordp_eq less (x : xs) (y : ys) =
  less x y || not (less y x) && lexordp_eq less xs ys;

interval :: forall a. (Eq a, Interval a) => a -> a -> [a];
interval a b =
  (if Orderings.less a b then a : interval (Arith.plus a Arith.one) b
    else (if a == b then [a] else []));

sort_key :: forall a b. (Orderings.Linorder b) => (a -> b) -> [a] -> [a];
sort_key key = Efficient_Sort.msort_key key;

size_list :: forall a. [a] -> Arith.Nat;
size_list xs = length_tailrec xs Arith.zero_nat;

all_interval :: forall a. (Eq a, Interval a) => (a -> Bool) -> a -> a -> Bool;
all_interval p a b =
  (if Orderings.less a b then p a && all_interval p (Arith.plus a Arith.one) b
    else True) &&
    (if a == b then p a else True);

sorted_list_of_set ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Eq a,
      Orderings.Linorder a) => Set.Set a -> [a];
sorted_list_of_set (Set.RBT_set rbt) =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "sorted_list_of_set RBT_set: ccompare = None"
        (\ _ -> sorted_list_of_set (Set.RBT_set rbt));
    Just _ -> sort_key (\ x -> x) (RBT_Set2.keys rbt);
  });
sorted_list_of_set (Set.DList_set dxs) =
  (case (Collection_Eq.ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "sorted_list_of_set DList_set: ceq = None"
        (\ _ -> sorted_list_of_set (Set.DList_set dxs));
    Just _ -> sort_key (\ x -> x) (DList_Set.list_of_dlist dxs);
  });
sorted_list_of_set (Set.Set_Monad xs) = sort_key (\ x -> x) (remdups xs);

}
