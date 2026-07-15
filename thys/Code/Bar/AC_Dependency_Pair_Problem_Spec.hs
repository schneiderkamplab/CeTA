{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  AC_Dependency_Pair_Problem_Spec(Ac_dpp_ops_ext(..), e, p, r, pw, rw, mk,
                                   pairs, rules, ac_dpp_trivial_check,
                                   eq_rules_map, intersect_pairs,
                                   delete_pairs_rules, eq_rules_no_left_var,
                                   reverse_eq_rules_map,
                                   eq_rules_non_collapsing)
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
import qualified Shows_Literal;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Term_Rewriting;
import qualified Arith;

data Ac_dpp_ops_ext a b c d =
  Ac_dpp_ops_ext
    (a -> (Arith.Set (Term_Rewriting.Term b c, Term_Rewriting.Term b c),
            (Arith.Set (Term_Rewriting.Term b c, Term_Rewriting.Term b c),
              (Arith.Set (Term_Rewriting.Term b c, Term_Rewriting.Term b c),
                (Arith.Set (Term_Rewriting.Term b c, Term_Rewriting.Term b c),
                  Arith.Set
                    (Term_Rewriting.Term b c, Term_Rewriting.Term b c))))))
    (a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)])
    (a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)])
    (a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)])
    (a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)])
    (a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)])
    (a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)])
    (a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)])
    ([(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
      [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
        [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
          [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
            [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] -> a)
    (a -> (b, Arith.Nat) ->
            [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)])
    (a -> (b, Arith.Nat) ->
            [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)])
    (a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
            [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] -> a)
    (a -> Bool) (a -> Bool)
    (a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] -> a) d;

e :: forall a b c d.
       Ac_dpp_ops_ext a b c d ->
         a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)];
e (Ac_dpp_ops_ext ac_dpp p pw pairs r rw rules e mk eq_rules_map
    reverse_eq_rules_map delete_pairs_rules eq_rules_no_left_var
    eq_rules_non_collapsing intersect_pairs more)
  = e;

p :: forall a b c d.
       Ac_dpp_ops_ext a b c d ->
         a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)];
p (Ac_dpp_ops_ext ac_dpp p pw pairs r rw rules e mk eq_rules_map
    reverse_eq_rules_map delete_pairs_rules eq_rules_no_left_var
    eq_rules_non_collapsing intersect_pairs more)
  = p;

r :: forall a b c d.
       Ac_dpp_ops_ext a b c d ->
         a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)];
r (Ac_dpp_ops_ext ac_dpp p pw pairs r rw rules e mk eq_rules_map
    reverse_eq_rules_map delete_pairs_rules eq_rules_no_left_var
    eq_rules_non_collapsing intersect_pairs more)
  = r;

pw :: forall a b c d.
        Ac_dpp_ops_ext a b c d ->
          a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)];
pw (Ac_dpp_ops_ext ac_dpp p pw pairs r rw rules e mk eq_rules_map
     reverse_eq_rules_map delete_pairs_rules eq_rules_no_left_var
     eq_rules_non_collapsing intersect_pairs more)
  = pw;

rw :: forall a b c d.
        Ac_dpp_ops_ext a b c d ->
          a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)];
rw (Ac_dpp_ops_ext ac_dpp p pw pairs r rw rules e mk eq_rules_map
     reverse_eq_rules_map delete_pairs_rules eq_rules_no_left_var
     eq_rules_non_collapsing intersect_pairs more)
  = rw;

mk :: forall a b c d.
        Ac_dpp_ops_ext a b c d ->
          [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
            [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
              [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
                [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
                  [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] -> a;
mk (Ac_dpp_ops_ext ac_dpp p pw pairs r rw rules e mk eq_rules_map
     reverse_eq_rules_map delete_pairs_rules eq_rules_no_left_var
     eq_rules_non_collapsing intersect_pairs more)
  = mk;

pairs ::
  forall a b c d.
    Ac_dpp_ops_ext a b c d ->
      a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)];
pairs (Ac_dpp_ops_ext ac_dpp p pw pairs r rw rules e mk eq_rules_map
        reverse_eq_rules_map delete_pairs_rules eq_rules_no_left_var
        eq_rules_non_collapsing intersect_pairs more)
  = pairs;

rules ::
  forall a b c d.
    Ac_dpp_ops_ext a b c d ->
      a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)];
rules (Ac_dpp_ops_ext ac_dpp p pw pairs r rw rules e mk eq_rules_map
        reverse_eq_rules_map delete_pairs_rules eq_rules_no_left_var
        eq_rules_non_collapsing intersect_pairs more)
  = rules;

ac_dpp_trivial_check ::
  forall a b c.
    Ac_dpp_ops_ext a b c () -> a -> Sum_Type.Sum (String -> String) ();
ac_dpp_trivial_check i dpp =
  Error_Monad.bind
    (Check_Monad.check (null (p i dpp))
      (Shows_Literal.showsl_lit "there are strict pairs"))
    (\ _ ->
      Check_Monad.check (null (pw i dpp) || null (r i dpp))
        (Shows_Literal.showsl_lit "there are weak pairs and strict rules"));

eq_rules_map ::
  forall a b c d.
    Ac_dpp_ops_ext a b c d ->
      a -> (b, Arith.Nat) ->
             [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)];
eq_rules_map
  (Ac_dpp_ops_ext ac_dpp p pw pairs r rw rules e mk eq_rules_map
    reverse_eq_rules_map delete_pairs_rules eq_rules_no_left_var
    eq_rules_non_collapsing intersect_pairs more)
  = eq_rules_map;

intersect_pairs ::
  forall a b c d.
    Ac_dpp_ops_ext a b c d ->
      a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] -> a;
intersect_pairs
  (Ac_dpp_ops_ext ac_dpp p pw pairs r rw rules e mk eq_rules_map
    reverse_eq_rules_map delete_pairs_rules eq_rules_no_left_var
    eq_rules_non_collapsing intersect_pairs more)
  = intersect_pairs;

delete_pairs_rules ::
  forall a b c d.
    Ac_dpp_ops_ext a b c d ->
      a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
             [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] -> a;
delete_pairs_rules
  (Ac_dpp_ops_ext ac_dpp p pw pairs r rw rules e mk eq_rules_map
    reverse_eq_rules_map delete_pairs_rules eq_rules_no_left_var
    eq_rules_non_collapsing intersect_pairs more)
  = delete_pairs_rules;

eq_rules_no_left_var :: forall a b c d. Ac_dpp_ops_ext a b c d -> a -> Bool;
eq_rules_no_left_var
  (Ac_dpp_ops_ext ac_dpp p pw pairs r rw rules e mk eq_rules_map
    reverse_eq_rules_map delete_pairs_rules eq_rules_no_left_var
    eq_rules_non_collapsing intersect_pairs more)
  = eq_rules_no_left_var;

reverse_eq_rules_map ::
  forall a b c d.
    Ac_dpp_ops_ext a b c d ->
      a -> (b, Arith.Nat) ->
             [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)];
reverse_eq_rules_map
  (Ac_dpp_ops_ext ac_dpp p pw pairs r rw rules e mk eq_rules_map
    reverse_eq_rules_map delete_pairs_rules eq_rules_no_left_var
    eq_rules_non_collapsing intersect_pairs more)
  = reverse_eq_rules_map;

eq_rules_non_collapsing :: forall a b c d. Ac_dpp_ops_ext a b c d -> a -> Bool;
eq_rules_non_collapsing
  (Ac_dpp_ops_ext ac_dpp p pw pairs r rw rules e mk eq_rules_map
    reverse_eq_rules_map delete_pairs_rules eq_rules_no_left_var
    eq_rules_non_collapsing intersect_pairs more)
  = eq_rules_non_collapsing;

}
