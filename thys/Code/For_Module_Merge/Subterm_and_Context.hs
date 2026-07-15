{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Subterm_and_Context(Actxt(..), equal_actxt, funas_term, intp_actxt,
                       actxt_compose, map_actxt)
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
import qualified List;
import qualified Term;
import qualified Set;
import qualified Arith;
import qualified Collection_Order;
import qualified Set_Impl;
import qualified Collection_Eq;

data Actxt a b = Hole | More a [b] (Actxt a b) [b];

equal_actxt :: forall a b. (Eq a, Eq b) => Actxt a b -> Actxt a b -> Bool;
equal_actxt Hole (More x21 x22 x23 x24) = False;
equal_actxt (More x21 x22 x23 x24) Hole = False;
equal_actxt (More x21 x22 x23 x24) (More y21 y22 y23 y24) =
  x21 == y21 && x22 == y22 && equal_actxt x23 y23 && x24 == y24;
equal_actxt Hole Hole = True;

instance (Eq a, Eq b) => Eq (Actxt a b) where {
  a == b = equal_actxt a b;
};

funas_term ::
  forall a b.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Set_Impl.Set_impl a) => Term.Term a b -> Set.Set (a, Arith.Nat);
funas_term (Term.Var uu) = Set.bot_set;
funas_term (Term.Fun f ts) =
  Set.sup_set (Set.insert (f, List.size_list ts) Set.bot_set)
    (List.foldr (Set.sup_set . funas_term) ts Set.bot_set);

intp_actxt :: forall a b. (a -> [b] -> b) -> Actxt a b -> b -> b;
intp_actxt i Hole a = a;
intp_actxt i (More f ls c rs) a = i f (ls ++ intp_actxt i c a : rs);

actxt_compose :: forall a b. Actxt a b -> Actxt a b -> Actxt a b;
actxt_compose Hole d = d;
actxt_compose (More f ls c rs) d = More f ls (actxt_compose c d) rs;

map_actxt :: forall a b c d. (a -> b) -> (c -> d) -> Actxt a c -> Actxt b d;
map_actxt f1 f2 Hole = Hole;
map_actxt f1 f2 (More x21 x22 x23 x24) =
  More (f1 x21) (map f2 x22) (map_actxt f1 f2 x23) (map f2 x24);

}
