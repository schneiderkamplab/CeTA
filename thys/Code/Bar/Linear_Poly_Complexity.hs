{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Linear_Poly_Complexity(Lpoly_order_semiring_ext(..), arcpos, defaulta,
                          checkmono, description, check_complexity,
                          plus_single_mono)
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
import qualified Ordered_Semiring;
import qualified Congruence;
import qualified Group;
import qualified Ring;
import qualified Sum_Type;
import qualified Arith;

data Lpoly_order_semiring_ext a b =
  Lpoly_order_semiring_ext Bool a (a -> Bool) (a -> Bool) (a -> Arith.Nat)
    (a -> Arith.Nat -> Sum_Type.Sum (String -> String) ()) (String -> String) b;

arcpos ::
  forall a b.
    Congruence.Partial_object_ext a
      (Group.Monoid_ext a
        (Ring.Ring_ext a
          (Ordered_Semiring.Ordered_semiring_ext a
            (Lpoly_order_semiring_ext a b)))) ->
      a -> Bool;
arcpos
  (Congruence.Partial_object_ext carrier
    (Group.Monoid_ext mult one
      (Ring.Ring_ext zero add
        (Ordered_Semiring.Ordered_semiring_ext geq gt max
          (Lpoly_order_semiring_ext plus_single_mono defaulta arcpos checkmono
            bound check_complexity description more)))))
  = arcpos;

defaulta ::
  forall a b.
    Congruence.Partial_object_ext a
      (Group.Monoid_ext a
        (Ring.Ring_ext a
          (Ordered_Semiring.Ordered_semiring_ext a
            (Lpoly_order_semiring_ext a b)))) ->
      a;
defaulta
  (Congruence.Partial_object_ext carrier
    (Group.Monoid_ext mult one
      (Ring.Ring_ext zero add
        (Ordered_Semiring.Ordered_semiring_ext geq gt max
          (Lpoly_order_semiring_ext plus_single_mono defaulta arcpos checkmono
            bound check_complexity description more)))))
  = defaulta;

checkmono ::
  forall a b.
    Congruence.Partial_object_ext a
      (Group.Monoid_ext a
        (Ring.Ring_ext a
          (Ordered_Semiring.Ordered_semiring_ext a
            (Lpoly_order_semiring_ext a b)))) ->
      a -> Bool;
checkmono
  (Congruence.Partial_object_ext carrier
    (Group.Monoid_ext mult one
      (Ring.Ring_ext zero add
        (Ordered_Semiring.Ordered_semiring_ext geq gt max
          (Lpoly_order_semiring_ext plus_single_mono defaulta arcpos checkmono
            bound check_complexity description more)))))
  = checkmono;

description ::
  forall a b.
    Congruence.Partial_object_ext a
      (Group.Monoid_ext a
        (Ring.Ring_ext a
          (Ordered_Semiring.Ordered_semiring_ext a
            (Lpoly_order_semiring_ext a b)))) ->
      String -> String;
description
  (Congruence.Partial_object_ext carrier
    (Group.Monoid_ext mult one
      (Ring.Ring_ext zero add
        (Ordered_Semiring.Ordered_semiring_ext geq gt max
          (Lpoly_order_semiring_ext plus_single_mono defaulta arcpos checkmono
            bound check_complexity description more)))))
  = description;

check_complexity ::
  forall a b.
    Congruence.Partial_object_ext a
      (Group.Monoid_ext a
        (Ring.Ring_ext a
          (Ordered_Semiring.Ordered_semiring_ext a
            (Lpoly_order_semiring_ext a b)))) ->
      a -> Arith.Nat -> Sum_Type.Sum (String -> String) ();
check_complexity
  (Congruence.Partial_object_ext carrier
    (Group.Monoid_ext mult one
      (Ring.Ring_ext zero add
        (Ordered_Semiring.Ordered_semiring_ext geq gt max
          (Lpoly_order_semiring_ext plus_single_mono defaulta arcpos checkmono
            bound check_complexity description more)))))
  = check_complexity;

plus_single_mono ::
  forall a b.
    Congruence.Partial_object_ext a
      (Group.Monoid_ext a
        (Ring.Ring_ext a
          (Ordered_Semiring.Ordered_semiring_ext a
            (Lpoly_order_semiring_ext a b)))) ->
      Bool;
plus_single_mono
  (Congruence.Partial_object_ext carrier
    (Group.Monoid_ext mult one
      (Ring.Ring_ext zero add
        (Ordered_Semiring.Ordered_semiring_ext geq gt max
          (Lpoly_order_semiring_ext plus_single_mono defaulta arcpos checkmono
            bound check_complexity description more)))))
  = plus_single_mono;

}
