{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Finite_Map(Fmap, fmdom, fmupd, fmdrop, fmempty, fmmap, fmlookup, equal_fmap)
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
import qualified Map;
import qualified FSet;
import qualified Arith;
import qualified AList;

newtype Fmap a b = Fmap_of_list [(a, b)];

fmadd :: forall a b. (Eq a) => Fmap a b -> Fmap a b -> Fmap a b;
fmadd (Fmap_of_list m) (Fmap_of_list n) = Fmap_of_list (AList.merge m n);

fmdom ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Arith.Set_impl a, Arith.Ceq b,
      Arith.Ccompare b, Arith.Set_impl b) => Fmap a b -> FSet.Fset a;
fmdom (Fmap_of_list m) = FSet.fimage fst (FSet.fset_of_list m);

fmupd :: forall a b. (Eq a) => a -> b -> Fmap a b -> Fmap a b;
fmupd k v m = fmadd m (Fmap_of_list [(k, v)]);

fmfilter :: forall a b. (a -> Bool) -> Fmap a b -> Fmap a b;
fmfilter p (Fmap_of_list m) = Fmap_of_list (filter (\ (k, _) -> p k) m);

fmdrop :: forall a b. (Eq a) => a -> Fmap a b -> Fmap a b;
fmdrop a = fmfilter (\ aa -> not (aa == a));

fmempty :: forall a b. Fmap a b;
fmempty = Fmap_of_list [];

fmmap :: forall a b c. (a -> b) -> Fmap c a -> Fmap c b;
fmmap f (Fmap_of_list m) = Fmap_of_list (map (Arith.apsnd f) m);

fmlookup :: forall a b. (Eq a) => Fmap a b -> a -> Maybe b;
fmlookup (Fmap_of_list m) = Map.map_of m;

fmrel ::
  forall a b c.
    (Arith.Ceq a, Arith.Ccompare a, Arith.Set_impl a, Arith.Ceq b,
      Arith.Ccompare b, Arith.Set_impl b, Arith.Ceq c, Arith.Ccompare c, Eq c,
      Arith.Set_impl c) => (a -> b -> Bool) -> Fmap c a -> Fmap c b -> Bool;
fmrel r m n =
  Arith.ball (FSet.fset (fmdom m))
    (\ x -> Arith.rel_option r (fmlookup m x) (fmlookup n x)) &&
    Arith.ball (FSet.fset (fmdom n))
      (\ x -> Arith.rel_option r (fmlookup m x) (fmlookup n x));

equal_fmap ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Eq a, Arith.Set_impl a, Arith.Ceq b,
      Arith.Ccompare b, Eq b, Arith.Set_impl b) => Fmap a b -> Fmap a b -> Bool;
equal_fmap = fmrel (\ a b -> a == b);

}
