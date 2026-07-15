{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Matching_Impl(match_term_list_code) where {

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
import qualified Unification;
import qualified Option;
import qualified Mapping;
import qualified Collection_Order;
import qualified Term;

match_term_list_code ::
  forall a b c.
    (Eq a, Collection_Order.Ccompare b, Eq b,
      Eq c) => [(Term.Term a b, Term.Term a c)] ->
                 Mapping.Mapping b (Term.Term a c) ->
                   Maybe (Mapping.Mapping b (Term.Term a c));
match_term_list_code [] sigma = Just sigma;
match_term_list_code ((Term.Var x, t) : p) sigma =
  (if Option.is_none (Mapping.lookup sigma x) ||
        Mapping.lookup sigma x == Just t
    then match_term_list_code p (Mapping.update x t sigma) else Nothing);
match_term_list_code ((Term.Fun f ss, Term.Fun g ts) : p) sigma =
  (case Unification.decompose (Term.Fun f ss) (Term.Fun g ts) of {
    Nothing -> Nothing;
    Just us -> match_term_list_code (us ++ p) sigma;
  });
match_term_list_code ((Term.Fun f ss, Term.Var x) : p) sigma = Nothing;

}
