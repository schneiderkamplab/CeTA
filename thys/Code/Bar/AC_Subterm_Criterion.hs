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
import qualified Status;
import qualified Multiset;
import qualified Term_Rewriting;
import qualified Arith;

proj_term ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Eq a,
      Eq b) => Status.Status a ->
                 Arith.Set (a, Arith.Nat) ->
                   Term_Rewriting.Term a b ->
                     Multiset.Multiset (Term_Rewriting.Term a b);
proj_term proj f (Term_Rewriting.Var x) =
  Multiset.add_mset (Term_Rewriting.Var x) Multiset.zero_multiset;
proj_term proj fa (Term_Rewriting.Fun f ts) =
  (if Arith.member (f, Arith.size_list ts) fa
    then Multiset.sum_mset
           (Multiset.mset
             (map (\ i -> proj_term proj fa (Arith.nth ts i))
               (Status.status proj (f, Arith.size_list ts))))
    else Multiset.add_mset (Term_Rewriting.Fun f ts) Multiset.zero_multiset);

}
