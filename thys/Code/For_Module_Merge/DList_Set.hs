{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  DList_Set(Set_dlist, list_of_dlist, hd, tl, fold, nulla, empty, list_member,
             insert, union, filtera, length, member, remove, product, dlist_ex,
             dlist_all, list_remdups)
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
import qualified Arith;
import qualified Option;
import qualified List;
import qualified Collection_Eq;

newtype Set_dlist a = Abs_dlist [a];

list_of_dlist :: forall a. (Collection_Eq.Ceq a) => Set_dlist a -> [a];
list_of_dlist (Abs_dlist x) = x;

hd :: forall a. (Collection_Eq.Ceq a) => Set_dlist a -> a;
hd xa = List.hd (list_of_dlist xa);

tl :: forall a. (Collection_Eq.Ceq a) => Set_dlist a -> Set_dlist a;
tl xa = Abs_dlist (List.tl (list_of_dlist xa));

fold ::
  forall a b. (Collection_Eq.Ceq a) => (a -> b -> b) -> Set_dlist a -> b -> b;
fold x xc = List.fold x (list_of_dlist xc);

nulla :: forall a. (Collection_Eq.Ceq a) => Set_dlist a -> Bool;
nulla xa = null (list_of_dlist xa);

empty :: forall a. (Collection_Eq.Ceq a) => Set_dlist a;
empty = Abs_dlist [];

list_member :: forall a. (a -> a -> Bool) -> [a] -> a -> Bool;
list_member equal [] y = False;
list_member equal (x : xs) y = equal x y || list_member equal xs y;

list_insert :: forall a. (a -> a -> Bool) -> a -> [a] -> [a];
list_insert equal x xs = (if list_member equal xs x then xs else x : xs);

insert :: forall a. (Collection_Eq.Ceq a) => a -> Set_dlist a -> Set_dlist a;
insert xb xc =
  Abs_dlist (list_insert (Option.the Collection_Eq.ceq) xb (list_of_dlist xc));

union ::
  forall a. (Collection_Eq.Ceq a) => Set_dlist a -> Set_dlist a -> Set_dlist a;
union = fold insert;

filtera ::
  forall a. (Collection_Eq.Ceq a) => (a -> Bool) -> Set_dlist a -> Set_dlist a;
filtera xb xc = Abs_dlist (filter xb (list_of_dlist xc));

length :: forall a. (Collection_Eq.Ceq a) => Set_dlist a -> Arith.Nat;
length xa = List.size_list (list_of_dlist xa);

member :: forall a. (Collection_Eq.Ceq a) => Set_dlist a -> a -> Bool;
member xa = list_member (Option.the Collection_Eq.ceq) (list_of_dlist xa);

list_remove1 :: forall a. (a -> a -> Bool) -> a -> [a] -> [a];
list_remove1 equal x [] = [];
list_remove1 equal x (y : xs) =
  (if equal x y then xs else y : list_remove1 equal x xs);

remove :: forall a. (Collection_Eq.Ceq a) => a -> Set_dlist a -> Set_dlist a;
remove xb xc =
  Abs_dlist (list_remove1 (Option.the Collection_Eq.ceq) xb (list_of_dlist xc));

product ::
  forall a b.
    (Collection_Eq.Ceq a,
      Collection_Eq.Ceq b) => Set_dlist a -> Set_dlist b -> Set_dlist (a, b);
product dxs1 dxs2 =
  Abs_dlist (fold (\ a -> fold (\ c -> (\ b -> (a, c) : b)) dxs2) dxs1 []);

dlist_ex ::
  forall a. (Collection_Eq.Ceq a) => (a -> Bool) -> Set_dlist a -> Bool;
dlist_ex x xc = any x (list_of_dlist xc);

dlist_all ::
  forall a. (Collection_Eq.Ceq a) => (a -> Bool) -> Set_dlist a -> Bool;
dlist_all x xc = all x (list_of_dlist xc);

list_remdups :: forall a. (a -> a -> Bool) -> [a] -> [a];
list_remdups equal [] = [];
list_remdups equal (x : xs) =
  (if list_member equal xs x then list_remdups equal xs
    else x : list_remdups equal xs);

}
