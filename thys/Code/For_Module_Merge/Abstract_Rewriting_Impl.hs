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
import qualified Set;
import qualified Collection_Enum;
import qualified Set_Impl;
import qualified Collection_Order;
import qualified Collection_Eq;
import qualified Option;

compute_NF :: forall a. (a -> Maybe a) -> a -> Maybe a;
compute_NF f a = (case f a of {
                   Nothing -> Just a;
                   Just aa -> compute_NF f aa;
                 });

compute_trancl ::
  forall a.
    (Collection_Enum.Cenum a, Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Set_Impl.Set_impl a) => Set.Set a -> Set.Set (a, a) -> Set.Set a;
compute_trancl a r =
  let {
    b = Relation.image r a;
  } in (if Set.less_eq_set b Set.bot_set then Set.bot_set
         else Set.sup_set b
                (compute_trancl b
                  (Set.filtera
                    (\ ab ->
                      not (Set.member (fst ab) a) &&
                        not (Set.member (snd ab) b))
                    r)));

}
