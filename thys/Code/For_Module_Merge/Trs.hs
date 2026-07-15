{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Trs(wf_rule, vars_rule, vars_trs, funas_rule, funas_trs, funs_trs_list,
       instance_rule, map_funs_rule, vars_trs_list, funas_trs_list,
       funs_rule_list, vars_rule_list, funas_rule_list, eq_rule_mod_vars,
       funas_args_trs_list)
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
import qualified Matching;
import qualified Option;
import qualified Mapping_Impl;
import qualified Trs_Impl;
import qualified Subterm_and_Context;
import qualified Arith;
import qualified Complete_Lattices;
import qualified Set;
import qualified Cardinality;
import qualified Collection_Enum;
import qualified Compare;
import qualified Container_Setup;
import qualified Collection_Order;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Term_Impl;
import qualified List;
import qualified Term;

wf_rule :: forall a b. (Eq b) => (Term.Term a b, Term.Term a b) -> Bool;
wf_rule r =
  not (Term.is_Var (fst r)) &&
    all (List.member (Term_Impl.insert_vars_term (fst r) []))
      (Term_Impl.insert_vars_term (snd r) []);

vars_rule ::
  forall a b.
    (Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Set_Impl.Set_impl b) => (Term.Term a b, Term.Term a b) -> Set.Set b;
vars_rule r = Set.sup_set (Term.vars_term (fst r)) (Term.vars_term (snd r));

vars_trs ::
  forall a b.
    (Compare.Compare a, Eq a, Cardinality.Finite_UNIV b,
      Collection_Enum.Cenum b, Collection_Eq.Ceq b,
      Collection_Order.Cproper_interval b, Compare.Compare b, Eq b,
      Set_Impl.Set_impl b) => Set.Set (Term.Term a b, Term.Term a b) ->
                                Set.Set b;
vars_trs r = Complete_Lattices.sup_set (Set.image vars_rule r);

funas_rule ::
  forall a b.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Set_Impl.Set_impl a) => (Term.Term a b, Term.Term a b) ->
                                Set.Set (a, Arith.Nat);
funas_rule r =
  Set.sup_set (Subterm_and_Context.funas_term (fst r))
    (Subterm_and_Context.funas_term (snd r));

funas_trs ::
  forall a b.
    (Cardinality.Finite_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Compare.Compare a, Eq a,
      Set_Impl.Set_impl a, Compare.Compare b,
      Eq b) => Set.Set (Term.Term a b, Term.Term a b) -> Set.Set (a, Arith.Nat);
funas_trs r = Complete_Lattices.sup_set (Set.image funas_rule r);

funs_trs_list :: forall a b. [(Term.Term a b, Term.Term a b)] -> [a];
funs_trs_list trs = List.foldr Trs_Impl.add_funs_rule trs [];

instance_rule ::
  forall a b c.
    (Eq a, Eq b, Collection_Order.Ccompare c, Eq c,
      Mapping_Impl.Mapping_impl c) => (Term.Term a b, Term.Term a b) ->
(Term.Term a c, Term.Term a c) -> Bool;
instance_rule lr st =
  not (Option.is_none
        (Matching.match_list (\ _ -> fst lr)
          [(fst st, fst lr), (snd st, snd lr)]));

map_funs_rule ::
  forall a b c.
    (a -> b) ->
      (Term.Term a c, Term.Term a c) -> (Term.Term b c, Term.Term b c);
map_funs_rule fg lr =
  (Term.map_term fg (\ x -> x) (fst lr), Term.map_term fg (\ x -> x) (snd lr));

vars_trs_list :: forall a b. [(Term.Term a b, Term.Term a b)] -> [b];
vars_trs_list trs = List.foldr Trs_Impl.add_vars_rule trs [];

funas_trs_list ::
  forall a b. [(Term.Term a b, Term.Term a b)] -> [(a, Arith.Nat)];
funas_trs_list trs = List.foldr Trs_Impl.add_funas_rule trs [];

funs_rule_list :: forall a b. (Term.Term a b, Term.Term a b) -> [a];
funs_rule_list r = Trs_Impl.add_funs_rule r [];

vars_rule_list :: forall a b. (Term.Term a b, Term.Term a b) -> [b];
vars_rule_list r = Trs_Impl.add_vars_rule r [];

funas_rule_list ::
  forall a b. (Term.Term a b, Term.Term a b) -> [(a, Arith.Nat)];
funas_rule_list r = Trs_Impl.add_funas_rule r [];

eq_rule_mod_vars ::
  forall a b.
    (Eq a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b) => (Term.Term a b, Term.Term a b) ->
(Term.Term a b, Term.Term a b) -> Bool;
eq_rule_mod_vars lr st = instance_rule lr st && instance_rule st lr;

funas_args_trs_list ::
  forall a b. [(Term.Term a b, Term.Term a b)] -> [(a, Arith.Nat)];
funas_args_trs_list trs = List.foldr Trs_Impl.add_funas_args_rule trs [];

}
