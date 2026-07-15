{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module RTrancl(mk_rtrancl_list) where {

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
import qualified Arith;

mk_rtrancl_list_main ::
  forall a. (a -> a -> Bool) -> (a -> [a]) -> [a] -> [a] -> [a];
mk_rtrancl_list_main subsumes r todo fin =
  (case todo of {
    [] -> fin;
    a : tod ->
      (if any (\ b -> subsumes b a) fin
        then mk_rtrancl_list_main subsumes r tod fin
        else mk_rtrancl_list_main subsumes r (r a ++ tod) (a : fin));
  });

mk_rtrancl_list :: forall a. (a -> a -> Bool) -> (a -> [a]) -> [a] -> [a];
mk_rtrancl_list subsumes r init = mk_rtrancl_list_main subsumes r init [];

}
