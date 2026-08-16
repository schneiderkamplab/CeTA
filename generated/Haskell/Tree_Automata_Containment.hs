{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Tree_Automata_Containment(Xoption(..), Status(..), is_busy, status_result,
                             map_xoption, equal_xoption)
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
import qualified Term_Rewriting;

data Xoption a = XNone | XSome a;

data Status a b = Done (Xoption (Term_Rewriting.Term a b)) | Changed
  | Unchanged;

is_busy :: forall a b. Status a b -> Bool;
is_busy (Done uu) = False;
is_busy Changed = True;
is_busy Unchanged = True;

status_result :: forall a b. Status a b -> Xoption (Term_Rewriting.Term a b);
status_result (Done t) = t;
status_result Changed = XNone;
status_result Unchanged = XNone;

map_xoption :: forall a b. (a -> b) -> Xoption a -> Xoption b;
map_xoption f XNone = XNone;
map_xoption f (XSome x2) = XSome (f x2);

equal_xoption :: forall a. (Eq a) => Xoption a -> Xoption a -> Bool;
equal_xoption XNone (XSome x2) = False;
equal_xoption (XSome x2) XNone = False;
equal_xoption (XSome x2) (XSome y2) = x2 == y2;
equal_xoption XNone XNone = True;

}
