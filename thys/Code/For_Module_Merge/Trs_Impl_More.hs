{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Trs_Impl_More(match_rules, check_variants_rule, check_variants_trs)
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
import qualified Trs_Impl;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Shows_Literal;
import qualified Option_Monad;
import qualified Matching;
import qualified Option;
import qualified Term;
import qualified Mapping_Impl;
import qualified Collection_Order;

match_rules ::
  forall a b.
    (Eq a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b) => [(Term.Term a b, Term.Term a b)] ->
[(Term.Term a b, Term.Term a b)] -> Maybe (b -> Term.Term a b);
match_rules rs_1 rs_2 =
  Option.bind
    (Option_Monad.zip_option (map fst rs_2 ++ map snd rs_2)
      (map fst rs_1 ++ map snd rs_1))
    (Matching.match_list Term.Var);

check_variants_rule ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b,
      Shows_Literal.Showl b) => (Term.Term a b, Term.Term a b) ->
                                  (Term.Term a b, Term.Term a b) ->
                                    Sum_Type.Sum (String -> String) ();
check_variants_rule ra r =
  Check_Monad.check
    (not (Option.is_none (match_rules [ra] [r])) &&
      not (Option.is_none (match_rules [r] [ra])))
    (((Trs_Impl.showsl_rule ra . Shows_Literal.showsl_literal " and ") .
       Trs_Impl.showsl_rule r) .
      Shows_Literal.showsl_literal " are not variants of each other\n");

check_variant_in_trs ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b,
      Shows_Literal.Showl b) => [(Term.Term a b, Term.Term a b)] ->
                                  (Term.Term a b, Term.Term a b) ->
                                    Sum_Type.Sum (String -> String) ();
check_variant_in_trs ra r =
  Error_Monad.catch_error
    (Error_Monad.catch_error (Error_Monad.existsM (check_variants_rule r) ra)
      (\ x -> Sum_Type.Inl (Shows_Literal.showsl_sep id id x)))
    (\ _ ->
      Sum_Type.Inl
        ((Trs_Impl.showsl_rule r .
           Shows_Literal.showsl_literal " is not a variant of any rule in ") .
          Trs_Impl.showsl_trs ra));

check_variants_trs ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b,
      Shows_Literal.Showl b) => [(Term.Term a b, Term.Term a b)] ->
                                  [(Term.Term a b, Term.Term a b)] ->
                                    Sum_Type.Sum (String -> String) ();
check_variants_trs ra r =
  Error_Monad.catch_error (Error_Monad.forallM (check_variant_in_trs r) ra)
    (\ x -> Sum_Type.Inl (snd x));

}
