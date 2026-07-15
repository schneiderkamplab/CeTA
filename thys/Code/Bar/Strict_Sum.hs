{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Strict_Sum(Sum_bot(..), bind, errora, returna, catch_error, left, right,
              case_sum_bot)
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
import qualified Sum_Type;

newtype Sum_bot a b = Sumbot (Sum_Type.Sum a b);

bind :: forall a b c. Sum_bot a b -> (b -> Sum_bot a c) -> Sum_bot a c;
bind (Sumbot a) f = (case a of {
                      Sum_Type.Inl b -> Sumbot (Sum_Type.Inl b);
                      Sum_Type.Inr aa -> f aa;
                    });

errora :: forall a b. a -> Sum_bot a b;
errora x = Sumbot (Sum_Type.Inl x);

returna :: forall a b. a -> Sum_bot b a;
returna x = Sumbot (Sum_Type.Inr x);

catch_error :: forall a b c. Sum_bot a b -> (a -> Sum_bot c b) -> Sum_bot c b;
catch_error (Sumbot a) f = (case a of {
                             Sum_Type.Inl aa -> f aa;
                             Sum_Type.Inr aa -> Sumbot (Sum_Type.Inr aa);
                           });

left :: forall a b. a -> Sum_bot a b;
left x = Sumbot (Sum_Type.Inl x);

right :: forall a b. a -> Sum_bot b a;
right x = Sumbot (Sum_Type.Inr x);

case_sum_bot :: forall a b c. a -> (b -> a) -> (c -> a) -> Sum_bot b c -> a;
case_sum_bot f g h (Sumbot p) = (case p of {
                                  Sum_Type.Inl a -> g a;
                                  Sum_Type.Inr a -> h a;
                                });

}
