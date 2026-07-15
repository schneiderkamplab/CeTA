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
import qualified Error_Monad;
import qualified Polynomials;
import qualified Quasi_Order;
import qualified Branch_and_Bound;
import qualified Mapping;
import qualified Sum_Type;
import qualified Arith;
import qualified Term_Rewriting;
import qualified HOL;

data La_solver_type = Simplex_Solver | BB_Solver;

default_la_solver_type :: La_solver_type;
default_la_solver_type = BB_Solver;

instance HOL.Default La_solver_type where {
  defaulta = default_la_solver_type;
};

showsl_la_solver_type :: La_solver_type -> String -> String;
showsl_la_solver_type BB_Solver = Term_Rewriting.showsl_lit "Branch-and-Bound";
showsl_la_solver_type Simplex_Solver = Term_Rewriting.showsl_lit "Simplex";

showsl_list_la_solver_type :: [La_solver_type] -> String -> String;
showsl_list_la_solver_type xs =
  Term_Rewriting.default_showsl_list showsl_la_solver_type xs;

instance Term_Rewriting.Showl La_solver_type where {
  showsl = showsl_la_solver_type;
  showsl_list = showsl_list_la_solver_type;
};

data Linearity a = Non_Linear | One | Variable a;

la_solver ::
  La_solver_type ->
    [Term_Rewriting.Constraint] -> Maybe (Arith.Nat -> Arith.Int);
la_solver BB_Solver cs = Branch_and_Bound.branch_and_bound_int cs;
la_solver Simplex_Solver cs =
  (case Term_Rewriting.simplex cs of {
    Sum_Type.Inl _ -> Nothing;
    Sum_Type.Inr v ->
      Just (\ x -> Term_Rewriting.floor_rat (Term_Rewriting.map2fun v x));
  });

monom_list_linearity :: forall a. [(a, Arith.Nat)] -> Linearity a;
monom_list_linearity [] = One;
monom_list_linearity [(x, n)] =
  (if Arith.equal_nat n Arith.one_nat then Variable x else Non_Linear);
monom_list_linearity (v : vb : vc) = Non_Linear;

monom_linearity ::
  forall a. (Quasi_Order.Linorder a) => Polynomials.Monom a -> Linearity a;
monom_linearity xa = monom_list_linearity (Polynomials.rep_monom xa);

split_bool_vars ::
  forall a b.
    [Term_Rewriting.Formula (Term_Rewriting.Term a b)] ->
      ([Term_Rewriting.Formula (Term_Rewriting.Term a b)],
        [Term_Rewriting.Formula (Term_Rewriting.Term a b)]);
split_bool_vars =
  Arith.partition
    (\ lit -> Term_Rewriting.is_Var (Term_Rewriting.get_Atom lit));

unsat_bool_checker :: forall a. (Eq a) => [Term_Rewriting.Formula a] -> Bool;
unsat_bool_checker blits =
  any (\ blit -> Arith.membera blits (Term_Rewriting.form_not blit)) blits;

translate_atom :: forall a. Term_Rewriting.Formula a -> a;
translate_atom (Term_Rewriting.Atom e) = e;

translate_atoms :: forall a. [Term_Rewriting.Formula a] -> [a];
translate_atoms = map translate_atom;

translate_conj ::
  forall a b.
    Term_Rewriting.Formula (Term_Rewriting.Term a b) ->
      ([Term_Rewriting.Formula (Term_Rewriting.Term a b)],
        [Term_Rewriting.Term a b]);
translate_conj (Term_Rewriting.Conjunction phi_s) =
  (case split_bool_vars phi_s of {
    (bvars, ia_lits) -> (bvars, translate_atoms ia_lits);
  });

ipoly_to_linear_poly ::
  forall a.
    (Quasi_Order.Linorder a) => (a -> Arith.Nat) ->
                                  [(Polynomials.Monom a, Arith.Int)] ->
                                    Maybe (Term_Rewriting.Linear_poly,
    Arith.Int);
ipoly_to_linear_poly rho [] =
  Just (Term_Rewriting.zero_linear_poly, Arith.zero_int);
ipoly_to_linear_poly rho ((monomial, c) : rest) =
  Arith.bind (ipoly_to_linear_poly rho rest)
    (\ (p, d) ->
      (case monom_linearity monomial of {
        Non_Linear -> Nothing;
        One -> Just (p, Arith.plus_int c d);
        Variable x ->
          Just (Term_Rewriting.plus_linear_poly
                  (Term_Rewriting.lp_monom (Term_Rewriting.of_int c) (rho x)) p,
                 d);
      }));

to_linear_constraints ::
  forall a.
    (Quasi_Order.Linorder a) => (a -> Arith.Nat) ->
                                  Term_Rewriting.Poly_constraint a ->
                                    [Term_Rewriting.Constraint];
to_linear_constraints rho (Term_Rewriting.Poly_Ge p) =
  (case ipoly_to_linear_poly rho p of {
    Nothing -> [];
    Just (q, c) ->
      [Term_Rewriting.GEQ q (Term_Rewriting.of_int (Arith.uminus_int c))];
  });
to_linear_constraints rho (Term_Rewriting.Poly_Eq p) =
  (case ipoly_to_linear_poly rho p of {
    Nothing -> [];
    Just (q, c) ->
      [Term_Rewriting.EQ q (Term_Rewriting.of_int (Arith.uminus_int c))];
  });

unsat_via_la_solver ::
  forall a.
    (Arith.Ccompare a, Eq a, Mapping.Mapping_impl a,
      Quasi_Order.Linorder a) => La_solver_type ->
                                   [Term_Rewriting.Poly_constraint a] ->
                                     Maybe (Maybe ([a], a -> Arith.Int));
unsat_via_la_solver typea les =
  let {
    vs = Arith.remdups (concatMap Term_Rewriting.vars_poly_constraint_list les);
    ren_map =
      Mapping.of_alist (zip vs (Arith.upt Arith.zero_nat (Arith.size_list vs)));
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
           } in (if all (Term_Rewriting.interpret_poly_constraint alpha) les
                  then Just (Just (vs, alpha)) else Nothing);
       });

unsat_checker ::
  forall a.
    (Arith.Ccompare a, Eq a, Mapping.Mapping_impl a, Quasi_Order.Linorder a,
      Term_Rewriting.Showl a) => La_solver_type ->
                                   [Term_Rewriting.Poly_constraint a] ->
                                     Sum_Type.Sum (String -> String) ();
unsat_checker solver cnjs =
  Error_Monad.catch_error
    (case unsat_via_la_solver solver cnjs of {
      Nothing ->
        Sum_Type.Inl
          (Term_Rewriting.showsl_lit
            "could not use linear arithmetic solver to prove unsatisfiability");
      Just Nothing -> Sum_Type.Inr ();
      Just (Just (vs, alpha)) ->
        Sum_Type.Inl
          (Term_Rewriting.showsl_lit
             "the linear inequalities are satisfiable:\n" .
            Term_Rewriting.showsl_list_gen
              (\ v ->
                (Term_Rewriting.showsl_monom (Polynomials.var_monom v) .
                  Term_Rewriting.showsl_lit " := ") .
                  Term_Rewriting.showsl_int (alpha v))
              "" "" "\n" "" vs);
    })
    (\ x ->
      Sum_Type.Inl
        (((((Term_Rewriting.showsl_lit "The linear inequalities\n  " .
              Term_Rewriting.showsl_sep Term_Rewriting.showsl_poly_constraint
                (Term_Rewriting.showsl_lit "\n  ") cnjs) .
             Term_Rewriting.showsl_lit
               "\ncannot be proved unsatisfiable via solver\n  ") .
            showsl_la_solver_type solver) .
           Term_Rewriting.showsl_literal "\n") .
          x));

check_clause ::
  forall a.
    (Arith.Ccompare a, Eq a, Mapping.Mapping_impl a, Quasi_Order.Linorder a,
      Term_Rewriting.Showl a) => La_solver_type ->
                                   Term_Rewriting.Formula
                                     (Term_Rewriting.Term Term_Rewriting.Sig
                                       (a, Term_Rewriting.Ty)) ->
                                     Sum_Type.Sum (String -> String) ();
check_clause typea phi =
  (case translate_conj (Term_Rewriting.form_not phi) of {
    (bvars, ia_lits) ->
      let {
        es = map Term_Rewriting.iA_exp_to_poly_constraint ia_lits;
      } in (if unsat_bool_checker bvars then Sum_Type.Inr ()
             else Error_Monad.catch_error (unsat_checker typea es)
                    (\ x ->
                      Sum_Type.Inl
                        (((Term_Rewriting.showsl_lit
                             "Could not prove unsatisfiability of IA conjunction\n" .
                            Term_Rewriting.showsl_list_gen
                              Term_Rewriting.showsl_poly_constraint "False" ""
                              " && " "" es) .
                           Term_Rewriting.showsl_literal "\n") .
                          x)));
  });

lit_normalize ::
  forall a.
    Bool ->
      Term_Rewriting.Term Term_Rewriting.Sig (a, Term_Rewriting.Ty) ->
        Term_Rewriting.Formula
          (Term_Rewriting.Term Term_Rewriting.Sig (a, Term_Rewriting.Ty));
lit_normalize False e = Term_Rewriting.NegAtom e;
lit_normalize True (Term_Rewriting.Fun Term_Rewriting.LessF [a, b]) =
  Term_Rewriting.NegAtom (Term_Rewriting.Fun Term_Rewriting.LeF [b, a]);
lit_normalize True (Term_Rewriting.Fun Term_Rewriting.LeF [a, b]) =
  Term_Rewriting.NegAtom (Term_Rewriting.Fun Term_Rewriting.LessF [b, a]);
lit_normalize True (Term_Rewriting.Fun Term_Rewriting.EqF [a, b]) =
  Term_Rewriting.Conjunction
    [Term_Rewriting.NegAtom (Term_Rewriting.Fun Term_Rewriting.LessF [a, b]),
      Term_Rewriting.NegAtom (Term_Rewriting.Fun Term_Rewriting.LessF [b, a])];
lit_normalize True (Term_Rewriting.Var x) =
  Term_Rewriting.Atom (Term_Rewriting.Var x);

}
