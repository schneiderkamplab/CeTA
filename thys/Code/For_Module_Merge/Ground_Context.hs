{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Ground_Context(Gctxt(..), equal_gctxt, match, pos_gctxt, unifiable)
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
import qualified Complete_Lattices;
import qualified Product_Type;
import qualified List;
import qualified Phantom_Type;
import qualified Set;
import qualified Arith;
import qualified Compare;
import qualified Container_Setup;
import qualified Cardinality;
import qualified Collection_Enum;
import qualified Collection_Order;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Ground_Context_Impl;
import qualified Option;
import qualified Term;

data Gctxt a b = GCHole | GCFun a [Gctxt a b];

instance (Eq a) => Eq (Gctxt a b) where {
  a == b = equal_gctxt a b;
};

equal_gctxt :: forall a b. (Eq a) => Gctxt a b -> Gctxt a b -> Bool;
equal_gctxt GCHole (GCFun x21 x22) = False;
equal_gctxt (GCFun x21 x22) GCHole = False;
equal_gctxt (GCFun x21 x22) (GCFun y21 y22) = x21 == y21 && x22 == y22;
equal_gctxt GCHole GCHole = True;

match :: forall a b. (Eq a, Eq b) => Gctxt a b -> Term.Term a b -> Bool;
match c t = not (Option.is_none (Ground_Context_Impl.match (c, t)));

pos_gctxt ::
  forall a b.
    (Compare.Compare a, Eq a,
      Compare.Compare b) => Gctxt a b -> Set.Set [Arith.Nat];
pos_gctxt GCHole =
  Set.insert []
    (Set_Impl.set_empty (Phantom_Type.of_phantom Set_Impl.set_impl_list));
pos_gctxt (GCFun f cs) =
  Set.sup_set
    (Set.insert []
      (Set_Impl.set_empty (Phantom_Type.of_phantom Set_Impl.set_impl_list)))
    (Complete_Lattices.sup_set
      (Set.image (\ (c, i) -> Set.image (\ a -> i : a) (pos_gctxt c))
        (List.set (zip cs (List.upt Arith.zero_nat (List.size_list cs))))));

unifiable :: forall a b. (Eq a) => Gctxt a b -> Gctxt a b -> Bool;
unifiable s t = not (Option.is_none (Ground_Context_Impl.merge s t));

}
