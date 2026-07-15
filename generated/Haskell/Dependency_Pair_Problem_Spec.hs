{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Dependency_Pair_Problem_Spec(Dpp_ops_ext(..), p, q, r, pw, rw, mk, nfs, pairs,
                                rules, is_QNF, q_empty, minimal, rules_map,
                                wwf_rules, delete_P_Pw, delete_R_Rw,
                                split_pairs, split_rules, replace_pair,
                                intersect_pairs, intersect_rules,
                                reverse_rules_map, rules_no_left_var,
                                nFQ_subset_NF_rules, rules_non_collapsing)
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
import qualified Term_Rewriting;
import qualified Arith;

data Dpp_ops_ext a b c d =
  Dpp_ops_ext
    (a -> (Bool,
            (Bool,
              (Arith.Set (Term_Rewriting.Term b c, Term_Rewriting.Term b c),
                (Arith.Set (Term_Rewriting.Term b c, Term_Rewriting.Term b c),
                  (Arith.Set (Term_Rewriting.Term b c),
                    (Arith.Set
                       (Term_Rewriting.Term b c, Term_Rewriting.Term b c),
                      Arith.Set
                        (Term_Rewriting.Term b c,
                          Term_Rewriting.Term b c))))))))
    (a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)])
    (a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)])
    (a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)])
    (a -> [Term_Rewriting.Term b c])
    (a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)])
    (a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)])
    (a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)]) (a -> Bool)
    (a -> Bool) (a -> Bool) (a -> Term_Rewriting.Term b c -> Bool) (a -> Bool)
    (a -> (b, Arith.Nat) ->
            [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)])
    (a -> (b, Arith.Nat) ->
            [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)])
    (a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] -> a)
    (a -> (Term_Rewriting.Term b c, Term_Rewriting.Term b c) ->
            [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] -> a)
    (a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] -> a)
    (a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
            [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] -> a)
    (a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
            [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] -> a)
    (a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
            ([(Term_Rewriting.Term b c, Term_Rewriting.Term b c)],
              [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)]))
    (a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
            ([(Term_Rewriting.Term b c, Term_Rewriting.Term b c)],
              [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)]))
    (Bool ->
      Bool ->
        [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
          [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
            [Term_Rewriting.Term b c] ->
              [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
                [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] -> a)
    (a -> Bool) (a -> Bool) (a -> Bool) d;

p :: forall a b c d.
       Dpp_ops_ext a b c d ->
         a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)];
p (Dpp_ops_ext dpp p pw pairs q r rw rules q_empty rules_no_left_var
    rules_non_collapsing is_QNF nFQ_subset_NF_rules rules_map reverse_rules_map
    intersect_pairs replace_pair intersect_rules delete_P_Pw delete_R_Rw
    split_pairs split_rules mk minimal nfs wwf_rules more)
  = p;

q :: forall a b c d. Dpp_ops_ext a b c d -> a -> [Term_Rewriting.Term b c];
q (Dpp_ops_ext dpp p pw pairs q r rw rules q_empty rules_no_left_var
    rules_non_collapsing is_QNF nFQ_subset_NF_rules rules_map reverse_rules_map
    intersect_pairs replace_pair intersect_rules delete_P_Pw delete_R_Rw
    split_pairs split_rules mk minimal nfs wwf_rules more)
  = q;

r :: forall a b c d.
       Dpp_ops_ext a b c d ->
         a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)];
r (Dpp_ops_ext dpp p pw pairs q r rw rules q_empty rules_no_left_var
    rules_non_collapsing is_QNF nFQ_subset_NF_rules rules_map reverse_rules_map
    intersect_pairs replace_pair intersect_rules delete_P_Pw delete_R_Rw
    split_pairs split_rules mk minimal nfs wwf_rules more)
  = r;

pw :: forall a b c d.
        Dpp_ops_ext a b c d ->
          a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)];
pw (Dpp_ops_ext dpp p pw pairs q r rw rules q_empty rules_no_left_var
     rules_non_collapsing is_QNF nFQ_subset_NF_rules rules_map reverse_rules_map
     intersect_pairs replace_pair intersect_rules delete_P_Pw delete_R_Rw
     split_pairs split_rules mk minimal nfs wwf_rules more)
  = pw;

rw :: forall a b c d.
        Dpp_ops_ext a b c d ->
          a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)];
rw (Dpp_ops_ext dpp p pw pairs q r rw rules q_empty rules_no_left_var
     rules_non_collapsing is_QNF nFQ_subset_NF_rules rules_map reverse_rules_map
     intersect_pairs replace_pair intersect_rules delete_P_Pw delete_R_Rw
     split_pairs split_rules mk minimal nfs wwf_rules more)
  = rw;

mk :: forall a b c d.
        Dpp_ops_ext a b c d ->
          Bool ->
            Bool ->
              [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
                [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
                  [Term_Rewriting.Term b c] ->
                    [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
                      [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] -> a;
mk (Dpp_ops_ext dpp p pw pairs q r rw rules q_empty rules_no_left_var
     rules_non_collapsing is_QNF nFQ_subset_NF_rules rules_map reverse_rules_map
     intersect_pairs replace_pair intersect_rules delete_P_Pw delete_R_Rw
     split_pairs split_rules mk minimal nfs wwf_rules more)
  = mk;

nfs :: forall a b c d. Dpp_ops_ext a b c d -> a -> Bool;
nfs (Dpp_ops_ext dpp p pw pairs q r rw rules q_empty rules_no_left_var
      rules_non_collapsing is_QNF nFQ_subset_NF_rules rules_map
      reverse_rules_map intersect_pairs replace_pair intersect_rules delete_P_Pw
      delete_R_Rw split_pairs split_rules mk minimal nfs wwf_rules more)
  = nfs;

pairs ::
  forall a b c d.
    Dpp_ops_ext a b c d ->
      a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)];
pairs (Dpp_ops_ext dpp p pw pairs q r rw rules q_empty rules_no_left_var
        rules_non_collapsing is_QNF nFQ_subset_NF_rules rules_map
        reverse_rules_map intersect_pairs replace_pair intersect_rules
        delete_P_Pw delete_R_Rw split_pairs split_rules mk minimal nfs wwf_rules
        more)
  = pairs;

rules ::
  forall a b c d.
    Dpp_ops_ext a b c d ->
      a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)];
rules (Dpp_ops_ext dpp p pw pairs q r rw rules q_empty rules_no_left_var
        rules_non_collapsing is_QNF nFQ_subset_NF_rules rules_map
        reverse_rules_map intersect_pairs replace_pair intersect_rules
        delete_P_Pw delete_R_Rw split_pairs split_rules mk minimal nfs wwf_rules
        more)
  = rules;

is_QNF ::
  forall a b c d. Dpp_ops_ext a b c d -> a -> Term_Rewriting.Term b c -> Bool;
is_QNF
  (Dpp_ops_ext dpp p pw pairs q r rw rules q_empty rules_no_left_var
    rules_non_collapsing is_QNF nFQ_subset_NF_rules rules_map reverse_rules_map
    intersect_pairs replace_pair intersect_rules delete_P_Pw delete_R_Rw
    split_pairs split_rules mk minimal nfs wwf_rules more)
  = is_QNF;

q_empty :: forall a b c d. Dpp_ops_ext a b c d -> a -> Bool;
q_empty
  (Dpp_ops_ext dpp p pw pairs q r rw rules q_empty rules_no_left_var
    rules_non_collapsing is_QNF nFQ_subset_NF_rules rules_map reverse_rules_map
    intersect_pairs replace_pair intersect_rules delete_P_Pw delete_R_Rw
    split_pairs split_rules mk minimal nfs wwf_rules more)
  = q_empty;

minimal :: forall a b c d. Dpp_ops_ext a b c d -> a -> Bool;
minimal
  (Dpp_ops_ext dpp p pw pairs q r rw rules q_empty rules_no_left_var
    rules_non_collapsing is_QNF nFQ_subset_NF_rules rules_map reverse_rules_map
    intersect_pairs replace_pair intersect_rules delete_P_Pw delete_R_Rw
    split_pairs split_rules mk minimal nfs wwf_rules more)
  = minimal;

rules_map ::
  forall a b c d.
    Dpp_ops_ext a b c d ->
      a -> (b, Arith.Nat) ->
             [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)];
rules_map
  (Dpp_ops_ext dpp p pw pairs q r rw rules q_empty rules_no_left_var
    rules_non_collapsing is_QNF nFQ_subset_NF_rules rules_map reverse_rules_map
    intersect_pairs replace_pair intersect_rules delete_P_Pw delete_R_Rw
    split_pairs split_rules mk minimal nfs wwf_rules more)
  = rules_map;

wwf_rules :: forall a b c d. Dpp_ops_ext a b c d -> a -> Bool;
wwf_rules
  (Dpp_ops_ext dpp p pw pairs q r rw rules q_empty rules_no_left_var
    rules_non_collapsing is_QNF nFQ_subset_NF_rules rules_map reverse_rules_map
    intersect_pairs replace_pair intersect_rules delete_P_Pw delete_R_Rw
    split_pairs split_rules mk minimal nfs wwf_rules more)
  = wwf_rules;

delete_P_Pw ::
  forall a b c d.
    Dpp_ops_ext a b c d ->
      a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
             [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] -> a;
delete_P_Pw
  (Dpp_ops_ext dpp p pw pairs q r rw rules q_empty rules_no_left_var
    rules_non_collapsing is_QNF nFQ_subset_NF_rules rules_map reverse_rules_map
    intersect_pairs replace_pair intersect_rules delete_P_Pw delete_R_Rw
    split_pairs split_rules mk minimal nfs wwf_rules more)
  = delete_P_Pw;

delete_R_Rw ::
  forall a b c d.
    Dpp_ops_ext a b c d ->
      a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
             [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] -> a;
delete_R_Rw
  (Dpp_ops_ext dpp p pw pairs q r rw rules q_empty rules_no_left_var
    rules_non_collapsing is_QNF nFQ_subset_NF_rules rules_map reverse_rules_map
    intersect_pairs replace_pair intersect_rules delete_P_Pw delete_R_Rw
    split_pairs split_rules mk minimal nfs wwf_rules more)
  = delete_R_Rw;

split_pairs ::
  forall a b c d.
    Dpp_ops_ext a b c d ->
      a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
             ([(Term_Rewriting.Term b c, Term_Rewriting.Term b c)],
               [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)]);
split_pairs
  (Dpp_ops_ext dpp p pw pairs q r rw rules q_empty rules_no_left_var
    rules_non_collapsing is_QNF nFQ_subset_NF_rules rules_map reverse_rules_map
    intersect_pairs replace_pair intersect_rules delete_P_Pw delete_R_Rw
    split_pairs split_rules mk minimal nfs wwf_rules more)
  = split_pairs;

split_rules ::
  forall a b c d.
    Dpp_ops_ext a b c d ->
      a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
             ([(Term_Rewriting.Term b c, Term_Rewriting.Term b c)],
               [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)]);
split_rules
  (Dpp_ops_ext dpp p pw pairs q r rw rules q_empty rules_no_left_var
    rules_non_collapsing is_QNF nFQ_subset_NF_rules rules_map reverse_rules_map
    intersect_pairs replace_pair intersect_rules delete_P_Pw delete_R_Rw
    split_pairs split_rules mk minimal nfs wwf_rules more)
  = split_rules;

replace_pair ::
  forall a b c d.
    Dpp_ops_ext a b c d ->
      a -> (Term_Rewriting.Term b c, Term_Rewriting.Term b c) ->
             [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] -> a;
replace_pair
  (Dpp_ops_ext dpp p pw pairs q r rw rules q_empty rules_no_left_var
    rules_non_collapsing is_QNF nFQ_subset_NF_rules rules_map reverse_rules_map
    intersect_pairs replace_pair intersect_rules delete_P_Pw delete_R_Rw
    split_pairs split_rules mk minimal nfs wwf_rules more)
  = replace_pair;

intersect_pairs ::
  forall a b c d.
    Dpp_ops_ext a b c d ->
      a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] -> a;
intersect_pairs
  (Dpp_ops_ext dpp p pw pairs q r rw rules q_empty rules_no_left_var
    rules_non_collapsing is_QNF nFQ_subset_NF_rules rules_map reverse_rules_map
    intersect_pairs replace_pair intersect_rules delete_P_Pw delete_R_Rw
    split_pairs split_rules mk minimal nfs wwf_rules more)
  = intersect_pairs;

intersect_rules ::
  forall a b c d.
    Dpp_ops_ext a b c d ->
      a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] -> a;
intersect_rules
  (Dpp_ops_ext dpp p pw pairs q r rw rules q_empty rules_no_left_var
    rules_non_collapsing is_QNF nFQ_subset_NF_rules rules_map reverse_rules_map
    intersect_pairs replace_pair intersect_rules delete_P_Pw delete_R_Rw
    split_pairs split_rules mk minimal nfs wwf_rules more)
  = intersect_rules;

reverse_rules_map ::
  forall a b c d.
    Dpp_ops_ext a b c d ->
      a -> (b, Arith.Nat) ->
             [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)];
reverse_rules_map
  (Dpp_ops_ext dpp p pw pairs q r rw rules q_empty rules_no_left_var
    rules_non_collapsing is_QNF nFQ_subset_NF_rules rules_map reverse_rules_map
    intersect_pairs replace_pair intersect_rules delete_P_Pw delete_R_Rw
    split_pairs split_rules mk minimal nfs wwf_rules more)
  = reverse_rules_map;

rules_no_left_var :: forall a b c d. Dpp_ops_ext a b c d -> a -> Bool;
rules_no_left_var
  (Dpp_ops_ext dpp p pw pairs q r rw rules q_empty rules_no_left_var
    rules_non_collapsing is_QNF nFQ_subset_NF_rules rules_map reverse_rules_map
    intersect_pairs replace_pair intersect_rules delete_P_Pw delete_R_Rw
    split_pairs split_rules mk minimal nfs wwf_rules more)
  = rules_no_left_var;

nFQ_subset_NF_rules :: forall a b c d. Dpp_ops_ext a b c d -> a -> Bool;
nFQ_subset_NF_rules
  (Dpp_ops_ext dpp p pw pairs q r rw rules q_empty rules_no_left_var
    rules_non_collapsing is_QNF nFQ_subset_NF_rules rules_map reverse_rules_map
    intersect_pairs replace_pair intersect_rules delete_P_Pw delete_R_Rw
    split_pairs split_rules mk minimal nfs wwf_rules more)
  = nFQ_subset_NF_rules;

rules_non_collapsing :: forall a b c d. Dpp_ops_ext a b c d -> a -> Bool;
rules_non_collapsing
  (Dpp_ops_ext dpp p pw pairs q r rw rules q_empty rules_no_left_var
    rules_non_collapsing is_QNF nFQ_subset_NF_rules rules_map reverse_rules_map
    intersect_pairs replace_pair intersect_rules delete_P_Pw delete_R_Rw
    split_pairs split_rules mk minimal nfs wwf_rules more)
  = rules_non_collapsing;

}
