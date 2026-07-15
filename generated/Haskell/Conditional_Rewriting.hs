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
import qualified Complete_Lattices;
import qualified Compare;
import qualified Term_Rewriting;
import qualified Arith;

x_vars ::
  forall a b.
    (Compare.Compare a, Eq a, Arith.Finite_UNIV b, Arith.Cenum b, Arith.Ceq b,
      Arith.Cproper_interval b, Compare.Compare b, Eq b,
      Arith.Set_impl b) => ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                             [(Term_Rewriting.Term a b,
                                Term_Rewriting.Term a b)]) ->
                             Arith.Nat -> Arith.Set b;
x_vars rho i =
  Arith.sup_set (Term_Rewriting.vars_term (fst (fst rho)))
    (Complete_Lattices.sup_set
      (Arith.image Term_Rewriting.vars_term
        (Arith.image snd (Arith.set (Arith.take i (snd rho))))));

funas_crule ::
  forall a b.
    (Arith.Finite_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Compare.Compare a, Eq a, Arith.Set_impl a, Compare.Compare b,
      Eq b) => ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]) ->
                 Arith.Set (a, Arith.Nat);
funas_crule rho =
  Arith.sup_set (Term_Rewriting.funas_rule (fst rho))
    (Term_Rewriting.funas_trs (Arith.set (snd rho)));

funas_ctrs ::
  forall a b.
    (Arith.Finite_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Compare.Compare a, Eq a, Arith.Set_impl a, Compare.Compare b,
      Eq b) => Arith.Set
                 ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                   [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]) ->
                 Arith.Set (a, Arith.Nat);
funas_ctrs r = Complete_Lattices.sup_set (Arith.image funas_crule r);

map_funs_crule ::
  forall a b c.
    (a -> b) ->
      ((Term_Rewriting.Term a c, Term_Rewriting.Term a c),
        [(Term_Rewriting.Term a c, Term_Rewriting.Term a c)]) ->
        ((Term_Rewriting.Term b c, Term_Rewriting.Term b c),
          [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)]);
map_funs_crule f r =
  ((Term_Rewriting.map_term f (\ x -> x) (fst (fst r)),
     Term_Rewriting.map_term f (\ x -> x) (snd (fst r))),
    map (Term_Rewriting.map_funs_rule f) (snd r));

extended_properly_oriented ::
  forall a b.
    (Compare.Compare a, Eq a, Arith.Finite_UNIV b, Arith.Cenum b, Arith.Ceq b,
      Arith.Cproper_interval b, Compare.Compare b, Eq b,
      Arith.Set_impl b) => Arith.Set
                             ((Term_Rewriting.Term a b,
                                Term_Rewriting.Term a b),
                               [(Term_Rewriting.Term a b,
                                  Term_Rewriting.Term a b)]) ->
                             Bool;
extended_properly_oriented r =
  Arith.ball r
    (\ rho ->
      Arith.less_eq_set (Term_Rewriting.vars_term (snd (fst rho)))
        (Term_Rewriting.vars_term (fst (fst rho))) ||
        not (Arith.all_interval
              (not .
                (\ m ->
                  let {
                    d = Arith.minus_nat m Arith.one_nat;
                  } in (if Arith.less_nat d m
                         then Arith.all_interval
                                (\ i ->
                                  Arith.less_eq_set
                                    (Term_Rewriting.vars_term
                                      (fst (Arith.nth (snd rho) i)))
                                    (x_vars rho i))
                                Arith.zero_nat d
                         else True) &&
                    let {
                      d = Arith.minus_nat (Arith.size_list (snd rho))
                            Arith.one_nat;
                    } in (if Arith.less_nat d (Arith.size_list (snd rho))
                           then Arith.all_interval
                                  (\ i ->
                                    Arith.less_eq_set
                                      (Arith.inf_set
(Term_Rewriting.vars_term (snd (fst rho)))
(Term_Rewriting.vars_rule (Arith.nth (snd rho) i)))
                                      (x_vars rho m))
                                  m d
                           else True)))
              Arith.zero_nat (Arith.size_list (snd rho))));

}
