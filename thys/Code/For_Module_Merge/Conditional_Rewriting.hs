{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Conditional_Rewriting(funas_ctrs, map_funs_crule, extended_properly_oriented)
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
import qualified HOL;
import qualified Trs;
import qualified Complete_Lattices;
import qualified List;
import qualified Term;
import qualified Set;
import qualified Arith;
import qualified Cardinality;
import qualified Collection_Enum;
import qualified Compare;
import qualified Container_Setup;
import qualified Collection_Order;
import qualified Set_Impl;
import qualified Collection_Eq;

x_vars ::
  forall a b.
    (Compare.Compare a, Eq a, Cardinality.Finite_UNIV b,
      Collection_Enum.Cenum b, Collection_Eq.Ceq b,
      Collection_Order.Cproper_interval b, Compare.Compare b, Eq b,
      Set_Impl.Set_impl b) => ((Term.Term a b, Term.Term a b),
                                [(Term.Term a b, Term.Term a b)]) ->
                                Arith.Nat -> Set.Set b;
x_vars rho i =
  Set.sup_set (Term.vars_term (fst (fst rho)))
    (Complete_Lattices.sup_set
      (Set.image Term.vars_term
        (Set.image snd (List.set (List.take i (snd rho))))));

funas_crule ::
  forall a b.
    (Cardinality.Finite_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Compare.Compare a, Eq a,
      Set_Impl.Set_impl a, Compare.Compare b,
      Eq b) => ((Term.Term a b, Term.Term a b),
                 [(Term.Term a b, Term.Term a b)]) ->
                 Set.Set (a, Arith.Nat);
funas_crule rho =
  Set.sup_set (Trs.funas_rule (fst rho)) (Trs.funas_trs (List.set (snd rho)));

funas_ctrs ::
  forall a b.
    (Cardinality.Finite_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Compare.Compare a, Eq a,
      Set_Impl.Set_impl a, Compare.Compare b,
      Eq b) => Set.Set
                 ((Term.Term a b, Term.Term a b),
                   [(Term.Term a b, Term.Term a b)]) ->
                 Set.Set (a, Arith.Nat);
funas_ctrs r = Complete_Lattices.sup_set (Set.image funas_crule r);

map_funs_crule ::
  forall a b c.
    (a -> b) ->
      ((Term.Term a c, Term.Term a c), [(Term.Term a c, Term.Term a c)]) ->
        ((Term.Term b c, Term.Term b c), [(Term.Term b c, Term.Term b c)]);
map_funs_crule f r =
  ((Term.map_term f (\ x -> x) (fst (fst r)),
     Term.map_term f (\ x -> x) (snd (fst r))),
    map (Trs.map_funs_rule f) (snd r));

extended_properly_oriented ::
  forall a b.
    (Compare.Compare a, Eq a, Cardinality.Finite_UNIV b,
      Collection_Enum.Cenum b, Collection_Eq.Ceq b,
      Collection_Order.Cproper_interval b, Compare.Compare b, Eq b,
      Set_Impl.Set_impl b) => Set.Set
                                ((Term.Term a b, Term.Term a b),
                                  [(Term.Term a b, Term.Term a b)]) ->
                                Bool;
extended_properly_oriented r =
  Set.ball r
    (\ rho ->
      Set.less_eq_set (Term.vars_term (snd (fst rho)))
        (Term.vars_term (fst (fst rho))) ||
        not (List.all_interval
              (not .
                (\ m ->
                  let {
                    d = Arith.minus_nat m Arith.one_nat;
                  } in (if Arith.less_nat d m
                         then List.all_interval
                                (\ i ->
                                  Set.less_eq_set
                                    (Term.vars_term
                                      (fst (List.nth (snd rho) i)))
                                    (x_vars rho i))
                                Arith.zero_nat d
                         else True) &&
                    let {
                      d = Arith.minus_nat (List.size_list (snd rho))
                            Arith.one_nat;
                    } in (if Arith.less_nat d (List.size_list (snd rho))
                           then List.all_interval
                                  (\ i ->
                                    Set.less_eq_set
                                      (Set.inf_set
(Term.vars_term (snd (fst rho))) (Trs.vars_rule (List.nth (snd rho) i)))
                                      (x_vars rho m))
                                  m d
                           else True)))
              Arith.zero_nat (List.size_list (snd rho))));

}
