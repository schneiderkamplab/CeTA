{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Non_Inf_Order_Impl(C_constraint(..), Non_inf_order_ext(..), af, cc, ns, desc,
                      valid)
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
import qualified Non_Inf_Order;
import qualified Sum_Type;
import qualified Arith;
import qualified Term_Rewriting;

data C_constraint a b =
  Conditional_C Bool (Term_Rewriting.Term a b, Term_Rewriting.Term a b)
    (Term_Rewriting.Term a b, Term_Rewriting.Term a b)
  | Unconditional_C Bool (Term_Rewriting.Term a b, Term_Rewriting.Term a b);

data Non_inf_order_ext a b c =
  Non_inf_order_ext (Sum_Type.Sum (String -> String) ())
    ((Term_Rewriting.Term a b, Term_Rewriting.Term a b) ->
      Sum_Type.Sum (String -> String) ())
    (C_constraint a b -> Sum_Type.Sum (String -> String) ())
    ((a, Arith.Nat) -> Arith.Nat -> Non_Inf_Order.Dependance) (String -> String)
    c;

af :: forall a b c.
        Non_inf_order_ext a b c ->
          (a, Arith.Nat) -> Arith.Nat -> Non_Inf_Order.Dependance;
af (Non_inf_order_ext valid ns cc af desc more) = af;

cc :: forall a b c.
        Non_inf_order_ext a b c ->
          C_constraint a b -> Sum_Type.Sum (String -> String) ();
cc (Non_inf_order_ext valid ns cc af desc more) = cc;

ns :: forall a b c.
        Non_inf_order_ext a b c ->
          (Term_Rewriting.Term a b, Term_Rewriting.Term a b) ->
            Sum_Type.Sum (String -> String) ();
ns (Non_inf_order_ext valid ns cc af desc more) = ns;

desc :: forall a b c. Non_inf_order_ext a b c -> String -> String;
desc (Non_inf_order_ext valid ns cc af desc more) = desc;

valid ::
  forall a b c. Non_inf_order_ext a b c -> Sum_Type.Sum (String -> String) ();
valid (Non_inf_order_ext valid ns cc af desc more) = valid;

}
