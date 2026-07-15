{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module IA_Checker(La_solver_type(..), check_clause, lit_normalize) where {

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
import qualified Abstract_Linear_Poly;
import qualified Show_Literal_Polynomial;
import qualified Option;
import qualified Product_Type;
import qualified Error_Monad;
import qualified Mapping_Impl;
import qualified Collection_Order;
import qualified Integer_Arithmetic;
import qualified List;
import qualified Formula;
import qualified Term;
import qualified Polynomials;
import qualified Orderings;
import qualified Branch_and_Bound;
import qualified Simplex;
import qualified Mapping;
import qualified Sum_Type;
import qualified Arith;
import qualified Rat;
import qualified Shows_Literal;
import qualified HOL;

data La_solver_type = Simplex_Solver | BB_Solver;

default_la_solver_type :: La_solver_type;
default_la_solver_type = BB_Solver;

instance HOL.Default La_solver_type where {
  defaulta = default_la_solver_type;
};

showsl_la_solver_type :: La_solver_type -> String -> String;
showsl_la_solver_type BB_Solver = Shows_Literal.showsl_lit "Branch-and-Bound";
showsl_la_solver_type Simplex_Solver = Shows_Literal.showsl_lit "Simplex";

showsl_list_la_solver_type :: [La_solver_type] -> String -> String;
showsl_list_la_solver_type xs =
  Shows_Literal.default_showsl_list showsl_la_solver_type xs;

instance Shows_Literal.Showl La_solver_type where {
  showsl = showsl_la_solver_type;
  showsl_list = showsl_list_la_solver_type;
};

data Linearity a = Non_Linear | One | Variable a;

la_solver ::
  La_solver_type -> [Simplex.Constraint] -> Maybe (Arith.Nat -> Arith.Int);
la_solver BB_Solver cs = Branch_and_Bound.branch_and_bound_int cs;
la_solver Simplex_Solver cs =
  (case Simplex.simplex cs of {
    Sum_Type.Inl _ -> Nothing;
    Sum_Type.Inr v -> Just (\ x -> Rat.floor_rat (Simplex.map2fun v x));
  });

monom_list_linearity :: forall a. [(a, Arith.Nat)] -> Linearity a;
monom_list_linearity [] = One;
monom_list_linearity [(x, n)] =
  (if Arith.equal_nat n Arith.one_nat then Variable x else Non_Linear);
monom_list_linearity (v : vb : vc) = Non_Linear;

monom_linearity ::
  forall a. (Orderings.Linorder a) => Polynomials.Monom a -> Linearity a;
monom_linearity xa = monom_list_linearity (Polynomials.rep_monom xa);

split_bool_vars ::
  forall a b.
    [Formula.Formula (Term.Term a b)] ->
      ([Formula.Formula (Term.Term a b)], [Formula.Formula (Term.Term a b)]);
split_bool_vars = List.partition (\ lit -> Term.is_Var (Formula.get_Atom lit));

unsat_bool_checker :: forall a. (Eq a) => [Formula.Formula a] -> Bool;
unsat_bool_checker blits =
  any (\ blit -> List.member blits (Formula.form_not blit)) blits;

translate_atom :: forall a. Formula.Formula a -> a;
translate_atom (Formula.Atom e) = e;

translate_atoms :: forall a. [Formula.Formula a] -> [a];
translate_atoms = map translate_atom;

translate_conj ::
  forall a b.
    Formula.Formula (Term.Term a b) ->
      ([Formula.Formula (Term.Term a b)], [Term.Term a b]);
translate_conj (Formula.Conjunction phi_s) =
  (case split_bool_vars phi_s of {
    (bvars, ia_lits) -> (bvars, translate_atoms ia_lits);
  });

ipoly_to_linear_poly ::
  forall a.
    (Orderings.Linorder a) => (a -> Arith.Nat) ->
                                [(Polynomials.Monom a, Arith.Int)] ->
                                  Maybe (Abstract_Linear_Poly.Linear_poly,
  Arith.Int);
ipoly_to_linear_poly rho [] =
  Just (Abstract_Linear_Poly.zero_linear_poly, Arith.zero_int);
ipoly_to_linear_poly rho ((monomial, c) : rest) =
  Option.bind (ipoly_to_linear_poly rho rest)
    (\ (p, d) ->
      (case monom_linearity monomial of {
        Non_Linear -> Nothing;
        One -> Just (p, Arith.plus_int c d);
        Variable x ->
          Just (Abstract_Linear_Poly.plus_linear_poly
                  (Abstract_Linear_Poly.lp_monom (Rat.of_int c) (rho x)) p,
                 d);
      }));

to_linear_constraints ::
  forall a.
    (Orderings.Linorder a) => (a -> Arith.Nat) ->
                                Integer_Arithmetic.Poly_constraint a ->
                                  [Simplex.Constraint];
to_linear_constraints rho (Integer_Arithmetic.Poly_Ge p) =
  (case ipoly_to_linear_poly rho p of {
    Nothing -> [];
    Just (q, c) -> [Simplex.GEQ q (Rat.of_int (Arith.uminus_int c))];
  });
to_linear_constraints rho (Integer_Arithmetic.Poly_Eq p) =
  (case ipoly_to_linear_poly rho p of {
    Nothing -> [];
    Just (q, c) -> [Simplex.EQ q (Rat.of_int (Arith.uminus_int c))];
  });

unsat_via_la_solver ::
  forall a.
    (Collection_Order.Ccompare a, Eq a, Mapping_Impl.Mapping_impl a,
      Orderings.Linorder a) => La_solver_type ->
                                 [Integer_Arithmetic.Poly_constraint a] ->
                                   Maybe (Maybe ([a], a -> Arith.Int));
unsat_via_la_solver typea les =
  let {
    vs = List.remdups
           (concatMap Integer_Arithmetic.vars_poly_constraint_list les);
    ren_map =
      Mapping.of_alist (zip vs (List.upt Arith.zero_nat (List.size_list vs)));
    ren_fun = (\ v -> (case Mapping.lookup ren_map v of {
                        Nothing -> Arith.zero_nat;
                        Just n -> n;
                      }));
    cs = concatMap (to_linear_constraints ren_fun) les;
  } in (case la_solver typea cs of {
         Nothing -> Just Nothing;
         Just beta ->
           let {
             alpha = beta . ren_fun;
           } in (if all (Integer_Arithmetic.interpret_poly_constraint alpha) les
                  then Just (Just (vs, alpha)) else Nothing);
       });

unsat_checker ::
  forall a.
    (Collection_Order.Ccompare a, Eq a, Mapping_Impl.Mapping_impl a,
      Orderings.Linorder a,
      Shows_Literal.Showl a) => La_solver_type ->
                                  [Integer_Arithmetic.Poly_constraint a] ->
                                    Sum_Type.Sum (String -> String) ();
unsat_checker solver cnjs =
  Error_Monad.catch_error
    (case unsat_via_la_solver solver cnjs of {
      Nothing ->
        Sum_Type.Inl
          (Shows_Literal.showsl_lit
            "could not use linear arithmetic solver to prove unsatisfiability");
      Just Nothing -> Sum_Type.Inr ();
      Just (Just (vs, alpha)) ->
        Sum_Type.Inl
          (Shows_Literal.showsl_lit
             "the linear inequalities are satisfiable:\n" .
            Shows_Literal.showsl_list_gen
              (\ v ->
                (Show_Literal_Polynomial.showsl_monom
                   (Polynomials.var_monom v) .
                  Shows_Literal.showsl_lit " := ") .
                  Shows_Literal.showsl_int (alpha v))
              "" "" "\n" "" vs);
    })
    (\ x ->
      Sum_Type.Inl
        (((((Shows_Literal.showsl_lit "The linear inequalities\n  " .
              Shows_Literal.showsl_sep Integer_Arithmetic.showsl_poly_constraint
                (Shows_Literal.showsl_lit "\n  ") cnjs) .
             Shows_Literal.showsl_lit
               "\ncannot be proved unsatisfiable via solver\n  ") .
            showsl_la_solver_type solver) .
           Shows_Literal.showsl_literal "\n") .
          x));

check_clause ::
  forall a.
    (Collection_Order.Ccompare a, Eq a, Mapping_Impl.Mapping_impl a,
      Orderings.Linorder a,
      Shows_Literal.Showl a) => La_solver_type ->
                                  Formula.Formula
                                    (Term.Term Integer_Arithmetic.Sig
                                      (a, Integer_Arithmetic.Ty)) ->
                                    Sum_Type.Sum (String -> String) ();
check_clause typea phi =
  (case translate_conj (Formula.form_not phi) of {
    (bvars, ia_lits) ->
      let {
        es = map Integer_Arithmetic.iA_exp_to_poly_constraint ia_lits;
      } in (if unsat_bool_checker bvars then Sum_Type.Inr ()
             else Error_Monad.catch_error (unsat_checker typea es)
                    (\ x ->
                      Sum_Type.Inl
                        (((Shows_Literal.showsl_lit
                             "Could not prove unsatisfiability of IA conjunction\n" .
                            Shows_Literal.showsl_list_gen
                              Integer_Arithmetic.showsl_poly_constraint "False"
                              "" " && " "" es) .
                           Shows_Literal.showsl_literal "\n") .
                          x)));
  });

lit_normalize ::
  forall a.
    Bool ->
      Term.Term Integer_Arithmetic.Sig (a, Integer_Arithmetic.Ty) ->
        Formula.Formula
          (Term.Term Integer_Arithmetic.Sig (a, Integer_Arithmetic.Ty));
lit_normalize False e = Formula.NegAtom e;
lit_normalize True (Term.Fun Integer_Arithmetic.LessF [a, b]) =
  Formula.NegAtom (Term.Fun Integer_Arithmetic.LeF [b, a]);
lit_normalize True (Term.Fun Integer_Arithmetic.LeF [a, b]) =
  Formula.NegAtom (Term.Fun Integer_Arithmetic.LessF [b, a]);
lit_normalize True (Term.Fun Integer_Arithmetic.EqF [a, b]) =
  Formula.Conjunction
    [Formula.NegAtom (Term.Fun Integer_Arithmetic.LessF [a, b]),
      Formula.NegAtom (Term.Fun Integer_Arithmetic.LessF [b, a])];
lit_normalize True (Term.Var x) = Formula.Atom (Term.Var x);

}
