{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module RTrancl_Impl(rtrancl_option) where {

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
import qualified HOL;
import qualified Arith;

all_reachable_main ::
  forall a.
    (Arith.Ceq a,
      Arith.Ccompare a) => (a -> [a]) -> Arith.Set a -> [a] -> [a] -> Maybe [a];
all_reachable_main succsR tsS ts todos =
  let {
    n_terms = concatMap succsR todos;
    really_new = filter (\ t -> not (Arith.member t tsS)) n_terms;
  } in (if null really_new then Just ts
         else all_reachable_main succsR
                (Arith.foldr Arith.insert really_new tsS) (really_new ++ ts)
                really_new);

rtrancl_option ::
  forall a.
    (Arith.Ceq a, Arith.Ccompare a,
      Arith.Set_impl a) => (a -> [a]) -> [a] -> Maybe [a];
rtrancl_option succsR ts = all_reachable_main succsR (Arith.set ts) ts ts;

}
