{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Ordered_Semiring(Ordered_semiring_ext(..), class_semiring, gt, geq, max,
                    class_ordered_semiring)
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
import qualified Orderings;
import qualified SN_Orders;
import qualified Congruence;
import qualified Group;
import qualified Ring;
import qualified Set;
import qualified HOL;
import qualified Collection_Order;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Arith;

data Ordered_semiring_ext a b =
  Ordered_semiring_ext (a -> a -> Bool) (a -> a -> Bool) (a -> a -> a) b;

class_semiring ::
  forall a b.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Arith.One a,
      Arith.Plus a, Arith.Times a, Arith.Zero a,
      Set_Impl.Set_impl a) => HOL.Itself a ->
                                b -> Congruence.Partial_object_ext a
                                       (Group.Monoid_ext a (Ring.Ring_ext a b));
class_semiring uu b =
  Congruence.Partial_object_ext Set.top_set
    (Group.Monoid_ext Arith.times Arith.one
      (Ring.Ring_ext Arith.zero Arith.plus b));

gt :: forall a b.
        Congruence.Partial_object_ext a
          (Group.Monoid_ext a (Ring.Ring_ext a (Ordered_semiring_ext a b))) ->
          a -> a -> Bool;
gt (Congruence.Partial_object_ext carrier
     (Group.Monoid_ext mult one
       (Ring.Ring_ext zero add (Ordered_semiring_ext geq gt max more))))
  = gt;

geq ::
  forall a b.
    Congruence.Partial_object_ext a
      (Group.Monoid_ext a (Ring.Ring_ext a (Ordered_semiring_ext a b))) ->
      a -> a -> Bool;
geq (Congruence.Partial_object_ext carrier
      (Group.Monoid_ext mult one
        (Ring.Ring_ext zero add (Ordered_semiring_ext geq gt max more))))
  = geq;

max ::
  forall a b.
    Congruence.Partial_object_ext a
      (Group.Monoid_ext a (Ring.Ring_ext a (Ordered_semiring_ext a b))) ->
      a -> a -> a;
max (Congruence.Partial_object_ext carrier
      (Group.Monoid_ext mult one
        (Ring.Ring_ext zero add (Ordered_semiring_ext geq gt max more))))
  = max;

class_ordered_semiring ::
  forall a b.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      SN_Orders.Ordered_semiring_1 a,
      Set_Impl.Set_impl a) => HOL.Itself a ->
                                (a -> a -> Bool) ->
                                  b -> Congruence.Partial_object_ext a
 (Group.Monoid_ext a (Ring.Ring_ext a (Ordered_semiring_ext a b)));
class_ordered_semiring a gt b =
  class_semiring a
    (Ordered_semiring_ext (\ x y -> Orderings.less_eq y x) gt Orderings.max b);

}
