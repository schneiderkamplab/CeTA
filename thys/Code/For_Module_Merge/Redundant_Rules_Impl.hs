{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Redundant_Rules_Impl(check_redundant_rules, check_redundant_rules_ncr)
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
import qualified Check_Joins;
import qualified Product_Type;
import qualified Missing_List;
import qualified Trs_Impl;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified List;
import qualified HOL;
import qualified Sum_Type;
import qualified Arith;
import qualified Mapping_Impl;
import qualified Collection_Order;
import qualified Shows_Literal;
import qualified Compare;
import qualified Term;

check_redundant_rules ::
  forall a b.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a,
      Collection_Order.Ccompare b, Compare.Compare b, Eq b,
      Mapping_Impl.Mapping_impl b,
      Shows_Literal.Showl b) => [(Term.Term a b, Term.Term a b)] ->
                                  [(Term.Term a b, Term.Term a b)] ->
                                    Arith.Nat ->
                                      [[Term.Term a b]] ->
Sum_Type.Sum (String -> String) ();
check_redundant_rules ra r n convs =
  let {
    s = Missing_List.list_diff r ra;
    t = Missing_List.list_diff ra r;
  } in Error_Monad.bind
         (Error_Monad.catch_error
           (Error_Monad.forallM
             (\ (l, rb) ->
               Check_Monad.check
                 (List.member (Trs_Impl.reachable_terms ra l n) rb)
                 (Shows_Literal.showsl_lit "could not simulate rule " .
                   Trs_Impl.showsl_rule (l, rb)))
             s)
           (\ x -> Sum_Type.Inl (snd x)))
         (\ _ ->
           Error_Monad.catch_error
             (Error_Monad.forallM
               (\ (l, raa) ->
                 Error_Monad.catch_error
                   (Error_Monad.existsM
                     (Check_Joins.check_conversion_sequence r l raa) convs)
                   (\ _ -> Trs_Impl.check_join_BFS_limit n r l raa))
               t)
             (\ x -> Sum_Type.Inl (snd x)));

check_redundant_rules_ncr ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b,
      Shows_Literal.Showl b) => [(Term.Term a b, Term.Term a b)] ->
                                  [(Term.Term a b, Term.Term a b)] ->
                                    Arith.Nat ->
                                      Sum_Type.Sum (String -> String) ();
check_redundant_rules_ncr ra r n =
  Error_Monad.bind
    (Error_Monad.catch_error (Check_Monad.check_subseteq ra r)
      (\ _ ->
        Sum_Type.Inl
          (Shows_Literal.showsl_lit "old TRS is not a subsystem of given TRS")))
    (\ _ ->
      let {
        s = Missing_List.list_diff r ra;
        t = Missing_List.list_diff ra r;
      } in Error_Monad.bind
             (Error_Monad.catch_error
               (Error_Monad.forallM
                 (\ (l, rb) ->
                   Check_Monad.check
                     (List.member (Trs_Impl.reachable_terms ra l n) rb)
                     (Shows_Literal.showsl_lit "could not simulate rule " .
                       Trs_Impl.showsl_rule (l, rb)))
                 s)
               (\ x -> Sum_Type.Inl (snd x)))
             (\ _ ->
               Error_Monad.catch_error
                 (Error_Monad.forallM
                   (\ (l, raa) ->
                     Check_Monad.check
                       (List.member (Trs_Impl.reachable_terms r l n) raa)
                       (Shows_Literal.showsl_lit "could not simulate rule " .
                         Trs_Impl.showsl_rule (l, raa)))
                   t)
                 (\ x -> Sum_Type.Inl (snd x))));

}
