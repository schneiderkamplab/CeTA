{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Compare_Order_Instances() where {

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
import qualified Product_Lexorder;
import qualified Comparator;
import qualified Compare;
import qualified Orderings;
import qualified List_Lexorder;
import qualified Compare_Instances;

instance (Compare.Compare_order a, Eq a) => Compare.Compare_order [a] where {
};

instance (Compare.Compare_order a,
           Compare.Compare_order b) => Compare.Compare_order (a, b) where {
};

}
