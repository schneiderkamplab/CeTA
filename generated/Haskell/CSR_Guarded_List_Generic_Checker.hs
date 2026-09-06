{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module CSR_Guarded_List_Generic_Checker(csr_guard_rules_check) where {

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
import qualified Term_Rewriting;
import qualified CSR_Guarded_List_Measure;

data Csr_guard_truth_form a =
  Guard_Truth_Form [a] [(a, CSR_Guarded_List_Measure.Csr_guard_sort)];

csr_guard_sort_requirement_implied ::
  CSR_Guarded_List_Measure.Csr_guard_sort ->
    CSR_Guarded_List_Measure.Csr_guard_sort -> Bool;
csr_guard_sort_requirement_implied target source =
  CSR_Guarded_List_Measure.equal_csr_guard_sort target source ||
    CSR_Guarded_List_Measure.equal_csr_guard_sort target
      CSR_Guarded_List_Measure.Guard_List &&
      CSR_Guarded_List_Measure.equal_csr_guard_sort source
        CSR_Guarded_List_Measure.Guard_IList;

csr_guard_requirements_covered ::
  forall a.
    (Eq a) => [(a, CSR_Guarded_List_Measure.Csr_guard_sort)] ->
                [(a, CSR_Guarded_List_Measure.Csr_guard_sort)] -> Bool;
csr_guard_requirements_covered source target =
  all (\ (x, a) ->
        any (\ (y, b) -> x == y && csr_guard_sort_requirement_implied b a)
          target)
    source;

csr_guard_truth_requirements ::
  forall a.
    Csr_guard_truth_form a -> [(a, CSR_Guarded_List_Measure.Csr_guard_sort)];
csr_guard_truth_requirements (Guard_Truth_Form xs req) = req;

csr_guard_truth_variables :: forall a. Csr_guard_truth_form a -> [a];
csr_guard_truth_variables (Guard_Truth_Form xs req) = xs;

csr_guard_truth_form_append ::
  forall a.
    Csr_guard_truth_form a -> Csr_guard_truth_form a -> Csr_guard_truth_form a;
csr_guard_truth_form_append (Guard_Truth_Form xs req) (Guard_Truth_Form ys ss) =
  Guard_Truth_Form (xs ++ ys) (req ++ ss);

csr_guard_symbolic_truth ::
  forall a b.
    (Eq a) => a -> a -> a -> a -> a -> a ->
 a -> a -> a -> a -> a -> a -> Term_Rewriting.Term a b ->
                                 Maybe (Csr_guard_truth_form b);
csr_guard_symbolic_truth tt a natp listp ilistp z su len ni co ta zs
  (Term_Rewriting.Var x) = Just (Guard_Truth_Form [x] []);
csr_guard_symbolic_truth tt a natp listp ilistp z su len ni co ta zs
  (Term_Rewriting.Fun f ts) =
  (if f == tt && null ts then Just (Guard_Truth_Form [] [])
    else (if f == a &&
               Arith.equal_nat (Arith.size_list ts)
                 (Arith.nat_of_integer (2 :: Integer))
           then (case (csr_guard_symbolic_truth tt a natp listp ilistp z su len
                         ni co ta zs (Arith.nth ts Arith.zero_nat),
                        csr_guard_symbolic_truth tt a natp listp ilistp z su len
                          ni co ta zs (Arith.nth ts Arith.one_nat))
                  of {
                  (Nothing, _) -> Nothing;
                  (Just _, Nothing) -> Nothing;
                  (Just fa, Just g) -> Just (csr_guard_truth_form_append fa g);
                })
           else (if f == natp &&
                      Arith.equal_nat (Arith.size_list ts) Arith.one_nat
                  then Arith.map_option
                         (\ fa ->
                           Guard_Truth_Form []
                             (CSR_Guarded_List_Measure.csr_guard_form_requirements
                               fa))
                         (CSR_Guarded_List_Measure.csr_guard_symbolic_rank z su
                           len ni co ta zs CSR_Guarded_List_Measure.Guard_Nat
                           (Arith.nth ts Arith.zero_nat))
                  else (if f == listp &&
                             Arith.equal_nat (Arith.size_list ts) Arith.one_nat
                         then Arith.map_option
                                (\ fa ->
                                  Guard_Truth_Form []
                                    (CSR_Guarded_List_Measure.csr_guard_form_requirements
                                      fa))
                                (CSR_Guarded_List_Measure.csr_guard_symbolic_rank
                                  z su len ni co ta zs
                                  CSR_Guarded_List_Measure.Guard_List
                                  (Arith.nth ts Arith.zero_nat))
                         else (if f == ilistp &&
                                    Arith.equal_nat (Arith.size_list ts)
                                      Arith.one_nat
                                then Arith.map_option
                                       (\ fa ->
 Guard_Truth_Form [] (CSR_Guarded_List_Measure.csr_guard_form_requirements fa))
                                       (CSR_Guarded_List_Measure.csr_guard_symbolic_rank
 z su len ni co ta zs CSR_Guarded_List_Measure.Guard_IList
 (Arith.nth ts Arith.zero_nat))
                                else Nothing)))));

csr_guard_truth_rule_backward_check ::
  forall a b.
    (Eq a,
      Eq b) => a -> a -> a -> a -> a -> a ->
  a -> a -> a -> a -> a -> a -> Term_Rewriting.Term a b ->
                                  Term_Rewriting.Term a b -> Bool;
csr_guard_truth_rule_backward_check tt a natp listp ilistp z su len ni co ta zs
  l r =
  (case csr_guard_symbolic_truth tt a natp listp ilistp z su len ni co ta zs r
    of {
    Nothing -> True;
    Just f_r ->
      (case csr_guard_symbolic_truth tt a natp listp ilistp z su len ni co ta zs
              l
        of {
        Nothing -> False;
        Just f_l ->
          Arith.superset (csr_guard_truth_variables f_r)
            (csr_guard_truth_variables f_l) &&
            csr_guard_requirements_covered (csr_guard_truth_requirements f_l)
              (csr_guard_truth_requirements f_r);
      });
  });

csr_guard_rules_check ::
  forall a b.
    (Eq a,
      Eq b) => a -> a -> a -> a -> a -> a ->
  a -> a -> a -> a -> a -> a -> a -> a -> a ->
    [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] -> Bool;
csr_guard_rules_check tt a natp listp ilistp u11 u21 u31 z su len ni co ta zs r
  = all (\ (l, ra) ->
          csr_guard_truth_rule_backward_check tt a natp listp ilistp z su len ni
            co ta zs l ra &&
            all (\ aa ->
                  CSR_Guarded_List_Measure.csr_guard_normal_rule_backward_eq a
                    u11 u21 u31 z su len ni co ta zs aa l ra)
              [CSR_Guarded_List_Measure.Guard_Nat,
                CSR_Guarded_List_Measure.Guard_List,
                CSR_Guarded_List_Measure.Guard_IList])
      r;

}
