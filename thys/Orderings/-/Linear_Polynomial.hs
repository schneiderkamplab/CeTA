{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Linear_Polynomial(L_poly(..), eval_lpoly) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;
import qualified Congruence;
import qualified Group;
import qualified Ring;

data L_poly a b = LPoly b [(a, b)];

eval_pvars ::
  forall a b c.
    Congruence.Partial_object_ext a (Group.Monoid_ext a (Ring.Ring_ext a b)) ->
      (c -> a) -> [(c, a)] -> a;
eval_pvars r uu [] = Ring.zero r;
eval_pvars r alpha ((x, a) : vas) =
  Ring.add r (Group.mult r a (alpha x)) (eval_pvars r alpha vas);

eval_lpoly ::
  forall a b c.
    Congruence.Partial_object_ext a (Group.Monoid_ext a (Ring.Ring_ext a b)) ->
      (c -> a) -> L_poly c a -> a;
eval_lpoly r alpha (LPoly a vas) = Ring.add r a (eval_pvars r alpha vas);

}
