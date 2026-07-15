{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Okui_Criterion(rename_list) where {

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
import qualified Product_Type;
import qualified Mgu_generic;
import qualified List;
import qualified RenamingN;
import qualified Term;
import qualified Arith;
import qualified Fresh;

rename_list ::
  forall a b.
    (Fresh.Infinite a) => RenamingN.RenamingN a ->
                            [Term.Term b a] -> [Term.Term b a];
rename_list ren ss =
  map (\ (i, a) -> Term.map_term (\ x -> x) (Mgu_generic.rename_many ren i) a)
    (zip (List.upt Arith.zero_nat (List.size_list ss)) ss);

}
