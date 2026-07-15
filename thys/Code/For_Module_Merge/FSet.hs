{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module FSet(Fset, fset, fimage, fset_of_list) where {

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
import qualified Collection_Order;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Set;

newtype Fset a = Abs_fset (Set.Set a);

fset :: forall a. Fset a -> Set.Set a;
fset (Abs_fset x) = x;

fimage ::
  forall b a.
    (Collection_Eq.Ceq b, Collection_Order.Ccompare b, Collection_Eq.Ceq a,
      Collection_Order.Ccompare a,
      Set_Impl.Set_impl a) => (b -> a) -> Fset b -> Fset a;
fimage xb xc = Abs_fset (Set.image xb (fset xc));

fset_of_list ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Set_Impl.Set_impl a) => [a] -> Fset a;
fset_of_list xa = Abs_fset (List.set xa);

}
