{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module List_Order_Implementations(List_order_type(..), list_ext, list_ext_name)
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
import qualified Dual_Multiset_Impl;
import qualified Min_Set_Order_Impl;
import qualified Multiset_Extension2;
import qualified Set_Order_Impl;
import qualified Arith;

data List_order_type = MS_Ext | Max_Ext | Min_Ext | Dms_Ext;

list_ext ::
  forall a.
    Arith.Nat ->
      List_order_type -> (a -> a -> (Bool, Bool)) -> [a] -> [a] -> (Bool, Bool);
list_ext uu MS_Ext = Multiset_Extension2.mul_ext;
list_ext uv Max_Ext = Set_Order_Impl.set_ext;
list_ext uw Min_Ext = Min_Set_Order_Impl.min_set_ext;
list_ext n Dms_Ext = Dual_Multiset_Impl.dms_order_ext n;

list_ext_name :: List_order_type -> String;
list_ext_name MS_Ext = "MS";
list_ext_name Dms_Ext = "DMS";
list_ext_name Min_Ext = "MIN";
list_ext_name Max_Ext = "MAX";

}
