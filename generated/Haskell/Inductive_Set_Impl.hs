{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Inductive_Set_Impl(inductive_set_impl, inductive_set_impl_lazy) where {

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
import qualified Missing_List;
import qualified HOL;
import qualified Arith;

new_as :: forall a b. (a -> b -> Bool) -> [a] -> [b] -> [b];
new_as p bs asa = filter (\ a -> any (\ b -> p b a) bs) asa;

the_set_impl_main ::
  forall a b.
    (Eq a, Eq b) => (a -> b -> Bool) -> (b -> [a]) -> [b] -> [b] -> [a] -> [b];
the_set_impl_main p q remain have bs =
  let {
    new = new_as p bs remain;
  } in (if null new then have
         else the_set_impl_main p q (Missing_List.list_diff remain new)
                (new ++ have) (Arith.remdups (concatMap q new)));

the_set_impl ::
  forall a b.
    (Eq a, Eq b) => [a] -> (b -> a -> Bool) -> (a -> [b]) -> [b] -> [a];
the_set_impl r p q bs = the_set_impl_main p q r [] bs;

inductive_set_impl ::
  forall a b.
    (Eq a, Eq b) => [a] -> (b -> a -> Bool) -> (a -> [b]) -> [b] -> [a];
inductive_set_impl = the_set_impl;

the_set_impl_main_lazy ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Arith.Set_impl a,
      Eq b) => (a -> [b]) -> (b -> [a]) -> [a] -> Arith.Set a -> [b] -> [a];
the_set_impl_main_lazy q gen_as have_asa have_as bs =
  let {
    new_as =
      concatMap
        (\ b ->
          concatMap (\ a -> (if not (Arith.member a have_as) then [a] else []))
            (gen_as b))
        bs;
  } in (if null new_as then have_asa
         else the_set_impl_main_lazy q gen_as (new_as ++ have_asa)
                (Arith.sup_set (Arith.set new_as) have_as)
                (Arith.remdups (concatMap q new_as)));

the_set_impl_lazy ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Arith.Set_impl a,
      Eq b) => (a -> [b]) -> (b -> [a]) -> [b] -> [a];
the_set_impl_lazy q gen_as bs =
  the_set_impl_main_lazy q gen_as [] Arith.bot_set bs;

inductive_set_impl_lazy ::
  forall a b.
    (Eq a, Arith.Ceq b, Arith.Ccompare b,
      Arith.Set_impl b) => (a -> [b]) -> (b -> [a]) -> [a] -> [b];
inductive_set_impl_lazy q p = the_set_impl_lazy p q;

}
