{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module AC_Weight(weight) where {

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
import qualified Groups_List;
import qualified List;
import qualified Term;
import qualified Arith;

weight ::
  forall a b.
    ((a, Arith.Nat) -> Arith.Nat) -> Arith.Nat -> Term.Term a b -> Arith.Nat;
weight w w0 (Term.Var x) = w0;
weight w w0 (Term.Fun f ts) =
  Arith.plus_nat (w (f, List.size_list ts))
    (Groups_List.sum_list (map (weight w w0) ts));

}
