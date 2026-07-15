{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module AC_Aux(filter_fun) where {

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
import qualified Multiset;
import qualified Term;
import qualified Arith;

filter_fun ::
  forall a b.
    Multiset.Multiset (Term.Term a b) ->
      ((a, Arith.Nat) -> (a, Arith.Nat) -> Bool) ->
        (a, Arith.Nat) -> Multiset.Multiset (Term.Term a b);
filter_fun t p f =
  Multiset.filter_mset (\ a -> (case a of {
                                 Term.Var _ -> False;
                                 Term.Fun g ts -> p (g, List.size_list ts) f;
                               }))
    t;

}
