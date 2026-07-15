{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Termination_Problem_Spec(Tp_ops_ext(..), q, r, rw, mk, nfs, rules, is_QNF,
                            q_empty, delete_R_Rw, split_rules,
                            nFQ_subset_NF_rules)
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
import qualified Term;
import qualified Set;
import qualified Arith;

data Tp_ops_ext a b c d =
  Tp_ops_ext
    (a -> (Bool,
            (Set.Set (Term.Term b c),
              (Set.Set (Term.Term b c, Term.Term b c),
                Set.Set (Term.Term b c, Term.Term b c)))))
    (a -> [Term.Term b c]) (a -> [(Term.Term b c, Term.Term b c)])
    (a -> [(Term.Term b c, Term.Term b c)])
    (a -> [(Term.Term b c, Term.Term b c)]) (a -> Bool)
    (a -> Term.Term b c -> Bool) (a -> Bool)
    (a -> (b, Arith.Nat) -> [(Term.Term b c, Term.Term b c)])
    (a -> [(Term.Term b c, Term.Term b c)] ->
            [(Term.Term b c, Term.Term b c)] -> a)
    (a -> [(Term.Term b c, Term.Term b c)] ->
            ([(Term.Term b c, Term.Term b c)],
              [(Term.Term b c, Term.Term b c)]))
    (Bool ->
      [Term.Term b c] ->
        [(Term.Term b c, Term.Term b c)] ->
          [(Term.Term b c, Term.Term b c)] -> a)
    (a -> Bool) d;

q :: forall a b c d. Tp_ops_ext a b c d -> a -> [Term.Term b c];
q (Tp_ops_ext qreltrs q r rw rules q_empty is_QNF nFQ_subset_NF_rules rules_map
    delete_R_Rw split_rules mk nfs more)
  = q;

r :: forall a b c d.
       Tp_ops_ext a b c d -> a -> [(Term.Term b c, Term.Term b c)];
r (Tp_ops_ext qreltrs q r rw rules q_empty is_QNF nFQ_subset_NF_rules rules_map
    delete_R_Rw split_rules mk nfs more)
  = r;

rw :: forall a b c d.
        Tp_ops_ext a b c d -> a -> [(Term.Term b c, Term.Term b c)];
rw (Tp_ops_ext qreltrs q r rw rules q_empty is_QNF nFQ_subset_NF_rules rules_map
     delete_R_Rw split_rules mk nfs more)
  = rw;

mk :: forall a b c d.
        Tp_ops_ext a b c d ->
          Bool ->
            [Term.Term b c] ->
              [(Term.Term b c, Term.Term b c)] ->
                [(Term.Term b c, Term.Term b c)] -> a;
mk (Tp_ops_ext qreltrs q r rw rules q_empty is_QNF nFQ_subset_NF_rules rules_map
     delete_R_Rw split_rules mk nfs more)
  = mk;

nfs :: forall a b c d. Tp_ops_ext a b c d -> a -> Bool;
nfs (Tp_ops_ext qreltrs q r rw rules q_empty is_QNF nFQ_subset_NF_rules
      rules_map delete_R_Rw split_rules mk nfs more)
  = nfs;

rules ::
  forall a b c d. Tp_ops_ext a b c d -> a -> [(Term.Term b c, Term.Term b c)];
rules (Tp_ops_ext qreltrs q r rw rules q_empty is_QNF nFQ_subset_NF_rules
        rules_map delete_R_Rw split_rules mk nfs more)
  = rules;

is_QNF :: forall a b c d. Tp_ops_ext a b c d -> a -> Term.Term b c -> Bool;
is_QNF
  (Tp_ops_ext qreltrs q r rw rules q_empty is_QNF nFQ_subset_NF_rules rules_map
    delete_R_Rw split_rules mk nfs more)
  = is_QNF;

q_empty :: forall a b c d. Tp_ops_ext a b c d -> a -> Bool;
q_empty
  (Tp_ops_ext qreltrs q r rw rules q_empty is_QNF nFQ_subset_NF_rules rules_map
    delete_R_Rw split_rules mk nfs more)
  = q_empty;

delete_R_Rw ::
  forall a b c d.
    Tp_ops_ext a b c d ->
      a -> [(Term.Term b c, Term.Term b c)] ->
             [(Term.Term b c, Term.Term b c)] -> a;
delete_R_Rw
  (Tp_ops_ext qreltrs q r rw rules q_empty is_QNF nFQ_subset_NF_rules rules_map
    delete_R_Rw split_rules mk nfs more)
  = delete_R_Rw;

split_rules ::
  forall a b c d.
    Tp_ops_ext a b c d ->
      a -> [(Term.Term b c, Term.Term b c)] ->
             ([(Term.Term b c, Term.Term b c)],
               [(Term.Term b c, Term.Term b c)]);
split_rules
  (Tp_ops_ext qreltrs q r rw rules q_empty is_QNF nFQ_subset_NF_rules rules_map
    delete_R_Rw split_rules mk nfs more)
  = split_rules;

nFQ_subset_NF_rules :: forall a b c d. Tp_ops_ext a b c d -> a -> Bool;
nFQ_subset_NF_rules
  (Tp_ops_ext qreltrs q r rw rules q_empty is_QNF nFQ_subset_NF_rules rules_map
    delete_R_Rw split_rules mk nfs more)
  = nFQ_subset_NF_rules;

}
