{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Matching(match_list, match, matches) where {

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
import qualified Matching_Impl;
import qualified Abstract_Matching;
import qualified Mapping;
import qualified Option;
import qualified Term;
import qualified Mapping_Impl;
import qualified Collection_Order;

match_list ::
  forall a b c.
    (Collection_Order.Ccompare a, Eq a, Mapping_Impl.Mapping_impl a, Eq b,
      Eq c) => (a -> Term.Term b c) ->
                 [(Term.Term b a, Term.Term b c)] -> Maybe (a -> Term.Term b c);
match_list d p =
  Option.map_option (Abstract_Matching.subst_of_map d . Mapping.lookup)
    (Matching_Impl.match_term_list_code p Mapping.empty);

match ::
  forall a b.
    (Eq a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b) => Term.Term a b ->
Term.Term a b -> Maybe (b -> Term.Term a b);
match t l = match_list Term.Var [(l, t)];

matches ::
  forall a b c.
    (Eq a, Eq b, Collection_Order.Ccompare c, Eq c,
      Mapping_Impl.Mapping_impl c) => Term.Term a b -> Term.Term a c -> Bool;
matches t p = (case match_list (\ _ -> t) [(p, t)] of {
                Nothing -> False;
                Just _ -> True;
              });

}
