{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Abstract_Rewriting_Impl(compute_NF, compute_trancl) where {

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
import qualified Relation;
import qualified HOL;
import qualified Arith;

compute_NF :: forall a. (a -> Maybe a) -> a -> Maybe a;
compute_NF f a = (case f a of {
                   Nothing -> Just a;
                   Just aa -> compute_NF f aa;
                 });

compute_trancl ::
  forall a.
    (Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a,
      Arith.Set_impl a) => Arith.Set a -> Arith.Set (a, a) -> Arith.Set a;
compute_trancl a r =
  let {
    b = Relation.image r a;
  } in (if Arith.less_eq_set b Arith.bot_set then Arith.bot_set
         else Arith.sup_set b
                (compute_trancl b
                  (Arith.filtera
                    (\ ab ->
                      not (Arith.member (fst ab) a) &&
                        not (Arith.member (snd ab) b))
                    r)));

}
