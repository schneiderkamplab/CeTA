{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Outermost_RZ_Checker(Outermost_rz_termination_proof(..),
                        check_outermost_rz_termination_proof)
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
import qualified FOR_Preliminaries;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Dependency_Pair_Problem_Spec;
import qualified Termination_Problem_Spec;
import qualified Sum_Type;
import qualified Countable;
import qualified Compare;
import qualified Compare_Order_Instances;
import qualified Mapping;
import qualified Outermost_RZ_Transformation;
import qualified HOL;
import qualified Quasi_Order;
import qualified Arith;
import qualified Map;
import qualified Check_Termination;
import qualified Labelings;
import qualified Term_Rewriting;

data Outermost_rz_termination_proof a b c =
  Outermost_RZ_Transformation (Labelings.Lab a b) (Labelings.Lab a b)
    (Labelings.Lab a b) (Labelings.Lab a b) (Labelings.Lab a b)
    [(Labelings.Lab a b, Labelings.Lab a b)]
    [Term_Rewriting.Term (Labelings.Lab a b) c]
    (Check_Termination.Trs_termination_proof a b c);

rz_flat_of :: forall a b c. (Eq a) => [(a, b)] -> (a, c) -> b;
rz_flat_of flats fn = Arith.the (Map.map_of flats (fst fn));

rz_flat_keys ::
  forall a b. (Arith.Zero b, Quasi_Order.Ord b) => [(a, b)] -> [a];
rz_flat_keys f =
  Arith.map_filter
    (\ x ->
      (if Quasi_Order.less Arith.zero (snd x) then Just (fst x) else Nothing))
    f;

rz_pattern_check ::
  forall a b.
    (Eq a, Arith.Ceq b, Arith.Ccompare b,
      Arith.Set_impl b) => [(a, Arith.Nat)] ->
                             [Term_Rewriting.Term a b] -> Bool;
rz_pattern_check f patterns =
  all (\ s ->
        not (Term_Rewriting.is_Var s) &&
          Term_Rewriting.linear_term s &&
            Arith.superset f (Term_Rewriting.funas_term_list s))
    patterns;

rz_flat_map_check ::
  forall a b c.
    (Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a, Eq a, Arith.Set_impl a,
      Arith.Zero b, Quasi_Order.Ord b) => [(a, b)] -> [(a, c)] -> Bool;
rz_flat_map_check f flats =
  Arith.distinct (map fst flats) &&
    Arith.set_eq (Arith.set (map fst flats)) (Arith.set (rz_flat_keys f));

rz_generated_rules ::
  forall a.
    (Eq a) => a -> a -> a -> a -> a -> [(a, a)] ->
 [(Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char])] ->
   [Term_Rewriting.Term a [Arith.Char]] ->
     [(Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char])];
rz_generated_rules top_sym up_sym down block c flats r patterns =
  let {
    f0 = Arith.remdups (Term_Rewriting.funas_trs_list r);
    f1 = Arith.remdups ((c, Arith.zero_nat) : f0);
  } in Outermost_RZ_Transformation.rz_transformed_rules_list top_sym up_sym down
         block (rz_flat_of flats)
         [Arith.char_0x5F, Arith.char_0x5F, Arith.char_0x72, Arith.char_0x7A,
           Arith.char_0x5F, Arith.char_0x72, Arith.char_0x65, Arith.char_0x73,
           Arith.char_0x65, Arith.char_0x74]
         f1 r patterns;

rz_quasi_left_linear_check ::
  forall a b c.
    (Eq a, Arith.Ceq b, Arith.Ccompare b, Eq b, Mapping.Mapping_impl b,
      Arith.Set_impl b) => [(Term_Rewriting.Term a b, c)] -> Bool;
rz_quasi_left_linear_check r =
  all (\ l ->
        any (\ k -> Term_Rewriting.linear_term k && Term_Rewriting.matches l k)
          (map fst r))
    (map fst r);

check_outermost_rz_termination_proof ::
  forall a b c.
    (Compare.Compare_order b, Countable.Countable b, Eq b,
      Term_Rewriting.Showl b) => Termination_Problem_Spec.Tp_ops_ext a
                                   (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                   () ->
                                   Dependency_Pair_Problem_Spec.Dpp_ops_ext c
                                     (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                     () ->
                                     (String -> String) ->
                                       [(Term_Rewriting.Term
   (Labelings.Lab b [Arith.Nat]) [Arith.Char],
  Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
 Outermost_rz_termination_proof b [Arith.Nat] [Arith.Char] ->
   Sum_Type.Sum (String -> String) ();
check_outermost_rz_termination_proof ia j i r
  (Outermost_RZ_Transformation top_sym up_sym down block c flats patterns child)
  = FOR_Preliminaries.debug i "Raffelsieper-Zantema outermost transformation"
      (Error_Monad.bind (Term_Rewriting.check_wf_trs r)
        (\ _ ->
          let {
            f0 = Arith.remdups (Term_Rewriting.funas_trs_list r);
            f1 = Arith.remdups ((c, Arith.zero_nat) : f0);
          } in Error_Monad.bind
                 (Check_Monad.check (rz_quasi_left_linear_check r)
                   (Term_Rewriting.showsl_lit
                     "left-hand sides are not quasi-left-linear"))
                 (\ _ ->
                   Error_Monad.bind
                     (Check_Monad.check
                       (not (Arith.membera f0 (c, Arith.zero_nat)))
                       (Term_Rewriting.showsl_lit
                         "grounding constant is not fresh"))
                     (\ _ ->
                       Error_Monad.bind
                         (Check_Monad.check
                           (not (Arith.membera f1 (block, Arith.zero_nat)))
                           (Term_Rewriting.showsl_lit
                             "tree-automata marker is not fresh"))
                         (\ _ ->
                           Error_Monad.bind
                             (Check_Monad.check (rz_flat_map_check f1 flats)
                               (Term_Rewriting.showsl_lit
                                 "flat-symbol map does not cover the positive-arity signature exactly"))
                             (\ _ ->
                               Error_Monad.bind
                                 (Check_Monad.check
                                   (rz_pattern_check f1 patterns)
                                   (Term_Rewriting.showsl_lit
                                     "non-redex patterns are malformed"))
                                 (\ _ ->
                                   Error_Monad.bind
                                     (Check_Monad.check
                                       (Outermost_RZ_Transformation.rz_cover_check
 f1 block
 [Arith.char_0x5F, Arith.char_0x5F, Arith.char_0x72, Arith.char_0x7A,
   Arith.char_0x5F, Arith.char_0x63, Arith.char_0x6F, Arith.char_0x76,
   Arith.char_0x65, Arith.char_0x72]
 (Outermost_RZ_Transformation.rz_linear_lhss r ++ patterns))
                                       (Term_Rewriting.showsl_lit
 "non-redex patterns do not cover the source signature"))
                                     (\ _ ->
                                       let {
 generated = rz_generated_rules top_sym up_sym down block c flats r patterns;
                                       } in
 Check_Termination.check_trs_termination_proof ia j False
   (Term_Rewriting.add_index i Arith.one_nat)
   (Termination_Problem_Spec.mk ia False [] generated []) child))))))));

}
