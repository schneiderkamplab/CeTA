{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Multi_Map(Multimap, empty, insert, lookup, values) where {

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
import qualified Mapping;

newtype Multimap a b = Abs_multimap (b -> a, (Mapping.Mapping a [b], [b]));

empty ::
  forall a b.
    (Arith.Ccompare b, Mapping.Mapping_impl b) => (a -> b) -> Multimap b a;
empty xa = Abs_multimap (xa, (Mapping.empty, []));

rep_multimap ::
  forall a b. Multimap a b -> (b -> a, (Mapping.Mapping a [b], [b]));
rep_multimap (Abs_multimap x) = x;

option_list_to_list :: forall a. Maybe [a] -> [a];
option_list_to_list Nothing = [];
option_list_to_list (Just asa) = asa;

insert ::
  forall a b. (Arith.Ccompare b, Eq b) => a -> Multimap b a -> Multimap b a;
insert xb xc =
  Abs_multimap
    (case rep_multimap xc of {
      (f, (m, alla)) -> let {
                          k = f xb;
                          old = option_list_to_list (Mapping.lookup m k);
                          new = xb : old;
                        } in (f, (Mapping.update k new m, xb : alla));
    });

lookup :: forall a b. (Arith.Ccompare a, Eq a) => Multimap a b -> a -> [b];
lookup xa = (case rep_multimap xa of {
              (_, (m, _)) -> (\ k -> option_list_to_list (Mapping.lookup m k));
            });

values :: forall a b. Multimap a b -> [b];
values xa = (case rep_multimap xa of {
              (_, (_, alla)) -> alla;
            });

}
