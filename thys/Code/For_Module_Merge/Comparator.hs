{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Comparator(Order(..), le_of_comp, lt_of_comp, comp_of_ords, equal_order,
              comparator_of)
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
import qualified Orderings;

data Order = Eqa | Lt | Gt;

le_of_comp :: forall a. (a -> a -> Order) -> a -> a -> Bool;
le_of_comp acomp x y = (case acomp x y of {
                         Eqa -> True;
                         Lt -> True;
                         Gt -> False;
                       });

lt_of_comp :: forall a. (a -> a -> Order) -> a -> a -> Bool;
lt_of_comp acomp x y = (case acomp x y of {
                         Eqa -> False;
                         Lt -> True;
                         Gt -> False;
                       });

comp_of_ords ::
  forall a. (a -> a -> Bool) -> (a -> a -> Bool) -> a -> a -> Order;
comp_of_ords le lt x y = (if lt x y then Lt else (if le x y then Eqa else Gt));

equal_order :: Order -> Order -> Bool;
equal_order Lt Gt = False;
equal_order Gt Lt = False;
equal_order Eqa Gt = False;
equal_order Gt Eqa = False;
equal_order Eqa Lt = False;
equal_order Lt Eqa = False;
equal_order Gt Gt = True;
equal_order Lt Lt = True;
equal_order Eqa Eqa = True;

comparator_of :: forall a. (Eq a, Orderings.Linorder a) => a -> a -> Order;
comparator_of x y =
  (if Orderings.less x y then Lt else (if x == y then Eqa else Gt));

}
