{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Impl_Array_Stack(as_get, as_pop, as_set, as_top, as_push, as_take, as_empty,
                    as_length, as_is_empty, as_singleton)
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
import qualified Quasi_Order;
import qualified Diff_Array;
import qualified HOL;
import qualified Arith;

as_get :: forall a. (Array.Array a, Arith.Nat) -> Arith.Nat -> a;
as_get s i = (case s of {
               (a, _) -> Diff_Array.array_get a i;
             });

as_shrink :: forall a. (Array.Array a, Arith.Nat) -> (Array.Array a, Arith.Nat);
as_shrink s =
  (case s of {
    (a, n) ->
      let {
        aa = (if Arith.less_eq_nat
                   (Arith.times_nat (Arith.nat_of_integer (128 :: Integer)) n)
                   (Diff_Array.array_length a) &&
                   Arith.less_nat (Arith.nat_of_integer (4 :: Integer)) n
               then Diff_Array.array_shrink a n else a);
      } in (aa, n);
  });

as_pop :: forall a. (Array.Array a, Arith.Nat) -> (Array.Array a, Arith.Nat);
as_pop s = (case s of {
             (a, n) -> as_shrink (a, Arith.minus_nat n Arith.one_nat);
           });

as_set ::
  forall a.
    (Array.Array a, Arith.Nat) -> Arith.Nat -> a -> (Array.Array a, Arith.Nat);
as_set s i x = (case s of {
                 (a, b) -> (Diff_Array.array_set a i x, b);
               });

as_top :: forall a. (Array.Array a, Arith.Nat) -> a;
as_top s =
  (case s of {
    (a, n) -> Diff_Array.array_get a (Arith.minus_nat n Arith.one_nat);
  });

as_push ::
  forall a. (Array.Array a, Arith.Nat) -> a -> (Array.Array a, Arith.Nat);
as_push s x =
  (case s of {
    (a, n) ->
      let {
        aa = (if Arith.equal_nat n (Diff_Array.array_length a)
               then Diff_Array.array_grow a
                      (Quasi_Order.max (Arith.nat_of_integer (4 :: Integer))
                        (Arith.times_nat (Arith.nat_of_integer (2 :: Integer))
                          n))
                      x
               else a);
        ab = Diff_Array.array_set aa n x;
      } in (ab, Arith.plus_nat n Arith.one_nat);
  });

as_take ::
  forall a.
    Arith.Nat -> (Array.Array a, Arith.Nat) -> (Array.Array a, Arith.Nat);
as_take m s =
  (case s of {
    (a, n) -> (if Arith.less_nat m n then as_shrink (a, m) else (a, n));
  });

as_empty :: forall a b. (Arith.Zero b) => () -> (Array.Array a, b);
as_empty uu = (Array.Array [], Arith.zero);

as_length :: forall a. (Array.Array a, Arith.Nat) -> Arith.Nat;
as_length = snd;

as_is_empty :: forall a. (Array.Array a, Arith.Nat) -> Bool;
as_is_empty s = Arith.equal_nat (snd s) Arith.zero_nat;

as_singleton :: forall a b. (Arith.One b) => a -> (Array.Array a, b);
as_singleton x = (Array.Array [x], Arith.one);

}
