{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module AC_Subterm_Criterion(proj_term) where {

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
import qualified List;
import qualified Status;
import qualified Set;
import qualified Arith;
import qualified Multiset;
import qualified Term;
import qualified Collection_Order;
import qualified Collection_Eq;

proj_term ::
  forall a b.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Eq a,
      Eq b) => Status.Status a ->
                 Set.Set (a, Arith.Nat) ->
                   Term.Term a b -> Multiset.Multiset (Term.Term a b);
proj_term proj f (Term.Var x) =
  Multiset.add_mset (Term.Var x) Multiset.zero_multiset;
proj_term proj fa (Term.Fun f ts) =
  (if Set.member (f, List.size_list ts) fa
    then Multiset.sum_mset
           (Multiset.mset
             (map (\ i -> proj_term proj fa (List.nth ts i))
               (Status.status proj (f, List.size_list ts))))
    else Multiset.add_mset (Term.Fun f ts) Multiset.zero_multiset);

}
