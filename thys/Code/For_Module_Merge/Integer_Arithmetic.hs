{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Integer_Arithmetic(Ty(..), equal_ty, Sig(..), Poly_constraint(..),
                      type_of_fun, showsl_IA_exp, def_checker,
                      showsl_poly_constraint, iA_exp_to_poly_constraint,
                      interpret_poly_constraint, vars_poly_constraint_list)
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
import qualified Sorted_Algebra;
import qualified Term_Impl;
import qualified Phantom_Type;
import qualified Set_Impl;
import qualified Set;
import qualified Container_Setup;
import qualified Show_Literal_Polynomial;
import qualified Error_Monad;
import qualified List;
import qualified Check_Monad;
import qualified Formula;
import qualified Sum_Type;
import qualified Term;
import qualified Orderings;
import qualified Polynomials;
import qualified Arith;
import qualified Shows_Literal;

data Ty = BoolT | IntT;

equal_ty :: Ty -> Ty -> Bool;
equal_ty BoolT IntT = False;
equal_ty IntT BoolT = False;
equal_ty IntT IntT = True;
equal_ty BoolT BoolT = True;

instance Eq Ty where {
  a == b = equal_ty a b;
};

showsl_ty :: Ty -> String -> String;
showsl_ty BoolT = Shows_Literal.showsl_lit "Bool";
showsl_ty IntT = Shows_Literal.showsl_lit "Int";

showsl_list_ty :: [Ty] -> String -> String;
showsl_list_ty xs = Shows_Literal.default_showsl_list showsl_ty xs;

instance Shows_Literal.Showl Ty where {
  showsl = showsl_ty;
  showsl_list = showsl_list_ty;
};

data Sig = LessF | LeF | SumF Arith.Nat | ConstF Arith.Int | ProdF Arith.Nat
  | EqF;

equal_sig :: Sig -> Sig -> Bool;
equal_sig (ProdF x5) EqF = False;
equal_sig EqF (ProdF x5) = False;
equal_sig (ConstF x4) EqF = False;
equal_sig EqF (ConstF x4) = False;
equal_sig (ConstF x4) (ProdF x5) = False;
equal_sig (ProdF x5) (ConstF x4) = False;
equal_sig (SumF x3) EqF = False;
equal_sig EqF (SumF x3) = False;
equal_sig (SumF x3) (ProdF x5) = False;
equal_sig (ProdF x5) (SumF x3) = False;
equal_sig (SumF x3) (ConstF x4) = False;
equal_sig (ConstF x4) (SumF x3) = False;
equal_sig LeF EqF = False;
equal_sig EqF LeF = False;
equal_sig LeF (ProdF x5) = False;
equal_sig (ProdF x5) LeF = False;
equal_sig LeF (ConstF x4) = False;
equal_sig (ConstF x4) LeF = False;
equal_sig LeF (SumF x3) = False;
equal_sig (SumF x3) LeF = False;
equal_sig LessF EqF = False;
equal_sig EqF LessF = False;
equal_sig LessF (ProdF x5) = False;
equal_sig (ProdF x5) LessF = False;
equal_sig LessF (ConstF x4) = False;
equal_sig (ConstF x4) LessF = False;
equal_sig LessF (SumF x3) = False;
equal_sig (SumF x3) LessF = False;
equal_sig LessF LeF = False;
equal_sig LeF LessF = False;
equal_sig (ProdF x5) (ProdF y5) = Arith.equal_nat x5 y5;
equal_sig (ConstF x4) (ConstF y4) = Arith.equal_int x4 y4;
equal_sig (SumF x3) (SumF y3) = Arith.equal_nat x3 y3;
equal_sig EqF EqF = True;
equal_sig LeF LeF = True;
equal_sig LessF LessF = True;

instance Eq Sig where {
  a == b = equal_sig a b;
};

showsl_sig :: Sig -> String -> String;
showsl_sig LessF = Shows_Literal.showsl_lit "<";
showsl_sig LeF = Shows_Literal.showsl_lit "<=";
showsl_sig EqF = Shows_Literal.showsl_lit "=";
showsl_sig (SumF n) = Shows_Literal.showsl_lit "+";
showsl_sig (ProdF n) = Shows_Literal.showsl_lit "*";
showsl_sig (ConstF n) = Shows_Literal.showsl_int n;

showsl_list_sig :: [Sig] -> String -> String;
showsl_list_sig xs = Shows_Literal.default_showsl_list showsl_sig xs;

instance Shows_Literal.Showl Sig where {
  showsl = showsl_sig;
  showsl_list = showsl_list_sig;
};

data Poly_constraint a = Poly_Ge [(Polynomials.Monom a, Arith.Int)]
  | Poly_Eq [(Polynomials.Monom a, Arith.Int)];

type_of_fun :: Sig -> ([Ty], Ty);
type_of_fun LessF = ([IntT, IntT], BoolT);
type_of_fun LeF = ([IntT, IntT], BoolT);
type_of_fun EqF = ([IntT, IntT], BoolT);
type_of_fun (SumF n) = (List.replicate n IntT, IntT);
type_of_fun (ConstF uu) = ([], IntT);
type_of_fun (ProdF n) = (List.replicate n IntT, IntT);

def_checker_main ::
  forall a.
    (Eq a) => a -> Ty -> Term.Term Sig (a, Ty) ->
                           Term.Term Sig (a, Ty) ->
                             Term.Term Sig (a, Ty) ->
                               Term.Term Sig (a, Ty) -> Bool;
def_checker_main x ty l1 r1 l2 r2 =
  Formula.is_bool type_of_fun
    (Set.insert BoolT
      (Set_Impl.set_empty
        (Phantom_Type.of_phantom Container_Setup.set_impl_ty)))
    (Term.Fun LeF [l1, r1]) &&
    Sorted_Algebra.has_type type_of_fun r1 ty &&
      Formula.is_bool type_of_fun
        (Set.insert BoolT
          (Set_Impl.set_empty
            (Phantom_Type.of_phantom Container_Setup.set_impl_ty)))
        (Term.Fun LeF [l2, r2]) &&
        Term.equal_term (Term.Var (x, ty)) l1 &&
          Term.equal_term l1 r2 &&
            Term.equal_term l2 r1 &&
              not (Term_Impl.contains_var_term (x, ty) r1);

def_checker_maina ::
  forall a.
    (Eq a) => a -> Ty -> Term.Term Sig (a, Ty) -> Term.Term Sig (a, Ty) -> Bool;
def_checker_maina x ty l1 r1 =
  Formula.is_bool type_of_fun
    (Set.insert BoolT
      (Set_Impl.set_empty
        (Phantom_Type.of_phantom Container_Setup.set_impl_ty)))
    (Term.Fun EqF [l1, r1]) &&
    Sorted_Algebra.has_type type_of_fun r1 ty &&
      Term.equal_term (Term.Var (x, ty)) l1 &&
        not (Term_Impl.contains_var_term (x, ty) r1);

def_checker_eq ::
  forall a.
    (Eq a) => a -> Ty -> Formula.Formula (Term.Term Sig (a, Ty)) ->
                           Sum_Type.Sum (String -> String) ();
def_checker_eq x ty eq =
  (case eq of {
    Formula.Atom (Term.Var _) ->
      Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid literal");
    Formula.Atom (Term.Fun LessF _) ->
      Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid literal");
    Formula.Atom (Term.Fun LeF _) ->
      Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid literal");
    Formula.Atom (Term.Fun (SumF _) _) ->
      Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid literal");
    Formula.Atom (Term.Fun (ConstF _) _) ->
      Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid literal");
    Formula.Atom (Term.Fun (ProdF _) _) ->
      Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid literal");
    Formula.Atom (Term.Fun EqF []) ->
      Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid literal");
    Formula.Atom (Term.Fun EqF [_]) ->
      Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid literal");
    Formula.Atom (Term.Fun EqF [l1, r1]) ->
      Check_Monad.check
        (def_checker_maina x ty l1 r1 || def_checker_maina x ty r1 l1)
        (Shows_Literal.showsl_lit "Non-equation not supported");
    Formula.Atom (Term.Fun EqF (_ : _ : _ : _)) ->
      Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid literal");
    Formula.NegAtom _ ->
      Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid clause");
    Formula.Conjunction _ ->
      Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid clause");
    Formula.Disjunction _ ->
      Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid clause");
  });

iA_exp_to_tpoly ::
  forall a. Term.Term Sig (a, Ty) -> Polynomials.Tpoly a Arith.Int;
iA_exp_to_tpoly (Term.Var (a, ty)) = Polynomials.PVar a;
iA_exp_to_tpoly (Term.Fun (SumF uu) asa) =
  Polynomials.PSum (map iA_exp_to_tpoly asa);
iA_exp_to_tpoly (Term.Fun (ConstF a) []) = Polynomials.PNum a;
iA_exp_to_tpoly (Term.Fun (ProdF uv) asa) =
  Polynomials.PMult (map iA_exp_to_tpoly asa);

iA_exp_to_poly ::
  forall a.
    (Eq a,
      Orderings.Linorder a) => Term.Term Sig (a, Ty) ->
                                 [(Polynomials.Monom a, Arith.Int)];
iA_exp_to_poly = Polynomials.poly_of . iA_exp_to_tpoly;

showsl_IA_exp ::
  forall a.
    (Eq a, Orderings.Linorder a,
      Shows_Literal.Showl a) => Term.Term Sig (a, Ty) -> String -> String;
showsl_IA_exp (Term.Fun LessF [s, t]) =
  (showsl_IA_exp s . Shows_Literal.showsl_lit " < ") . showsl_IA_exp t;
showsl_IA_exp (Term.Fun LeF [s, t]) =
  (showsl_IA_exp s . Shows_Literal.showsl_lit " <= ") . showsl_IA_exp t;
showsl_IA_exp (Term.Fun EqF [s, t]) =
  (showsl_IA_exp s . Shows_Literal.showsl_lit " = ") . showsl_IA_exp t;
showsl_IA_exp (Term.Var v) =
  Show_Literal_Polynomial.showsl_poly (iA_exp_to_poly (Term.Var v));
showsl_IA_exp (Term.Fun LeF []) =
  (Show_Literal_Polynomial.showsl_poly ::
    [(Polynomials.Monom a, Arith.Int)] -> String -> String)
    ((iA_exp_to_poly ::
       Term.Term Sig (a, Ty) -> [(Polynomials.Monom a, Arith.Int)])
      (Term.Fun LeF []));
showsl_IA_exp (Term.Fun LeF [v]) =
  Show_Literal_Polynomial.showsl_poly (iA_exp_to_poly (Term.Fun LeF [v]));
showsl_IA_exp (Term.Fun LeF (v : vc : ve : vf)) =
  Show_Literal_Polynomial.showsl_poly
    (iA_exp_to_poly (Term.Fun LeF (v : vc : ve : vf)));
showsl_IA_exp (Term.Fun (SumF vb) va) =
  Show_Literal_Polynomial.showsl_poly (iA_exp_to_poly (Term.Fun (SumF vb) va));
showsl_IA_exp (Term.Fun (ConstF vb) va) =
  Show_Literal_Polynomial.showsl_poly
    (iA_exp_to_poly (Term.Fun (ConstF vb) va));
showsl_IA_exp (Term.Fun (ProdF vb) va) =
  Show_Literal_Polynomial.showsl_poly (iA_exp_to_poly (Term.Fun (ProdF vb) va));
showsl_IA_exp (Term.Fun EqF []) =
  (Show_Literal_Polynomial.showsl_poly ::
    [(Polynomials.Monom a, Arith.Int)] -> String -> String)
    ((iA_exp_to_poly ::
       Term.Term Sig (a, Ty) -> [(Polynomials.Monom a, Arith.Int)])
      (Term.Fun EqF []));
showsl_IA_exp (Term.Fun EqF [v]) =
  Show_Literal_Polynomial.showsl_poly (iA_exp_to_poly (Term.Fun EqF [v]));
showsl_IA_exp (Term.Fun EqF (v : vc : ve : vf)) =
  Show_Literal_Polynomial.showsl_poly
    (iA_exp_to_poly (Term.Fun EqF (v : vc : ve : vf)));
showsl_IA_exp (Term.Fun v []) =
  (Show_Literal_Polynomial.showsl_poly ::
    [(Polynomials.Monom a, Arith.Int)] -> String -> String)
    ((iA_exp_to_poly ::
       Term.Term Sig (a, Ty) -> [(Polynomials.Monom a, Arith.Int)])
      (Term.Fun v []));
showsl_IA_exp (Term.Fun v [vb]) =
  Show_Literal_Polynomial.showsl_poly (iA_exp_to_poly (Term.Fun v [vb]));
showsl_IA_exp (Term.Fun v (vb : vd : vf : vg)) =
  Show_Literal_Polynomial.showsl_poly
    (iA_exp_to_poly (Term.Fun v (vb : vd : vf : vg)));

def_checker ::
  forall a.
    (Eq a, Orderings.Linorder a,
      Shows_Literal.Showl a) => a -> Ty -> Formula.Formula
     (Term.Term Sig (a, Ty)) ->
     Sum_Type.Sum (String -> String) ();
def_checker x ty phi =
  Error_Monad.catch_error
    (case phi of {
      Formula.Atom _ -> def_checker_eq x ty phi;
      Formula.NegAtom _ -> def_checker_eq x ty phi;
      Formula.Conjunction [] -> Sum_Type.Inr ();
      Formula.Conjunction [eq] -> def_checker_eq x ty eq;
      Formula.Conjunction [Formula.Atom (Term.Var _), _] ->
        Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 1st literal");
      Formula.Conjunction [Formula.Atom (Term.Fun LessF _), _] ->
        Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 1st literal");
      Formula.Conjunction [Formula.Atom (Term.Fun LeF []), _] ->
        Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 1st literal");
      Formula.Conjunction [Formula.Atom (Term.Fun LeF [_]), _] ->
        Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 1st literal");
      Formula.Conjunction [Formula.Atom (Term.Fun LeF [l1, r1]), lt2] ->
        (case lt2 of {
          Formula.Atom (Term.Var _) ->
            Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 2nd literal");
          Formula.Atom (Term.Fun LessF _) ->
            Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 2nd literal");
          Formula.Atom (Term.Fun LeF []) ->
            Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 2nd literal");
          Formula.Atom (Term.Fun LeF [_]) ->
            Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 2nd literal");
          Formula.Atom (Term.Fun LeF [l2, r2]) ->
            Check_Monad.check
              (def_checker_main x ty l1 r1 l2 r2 ||
                def_checker_main x ty l2 r2 l1 r1)
              (Shows_Literal.showsl_lit "Non-equation not supported");
          Formula.Atom (Term.Fun LeF (_ : _ : _ : _)) ->
            Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 2nd literal");
          Formula.Atom (Term.Fun (SumF _) _) ->
            Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 2nd literal");
          Formula.Atom (Term.Fun (ConstF _) _) ->
            Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 2nd literal");
          Formula.Atom (Term.Fun (ProdF _) _) ->
            Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 2nd literal");
          Formula.Atom (Term.Fun EqF _) ->
            Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 2nd literal");
          Formula.NegAtom _ ->
            Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 2nd clause");
          Formula.Conjunction _ ->
            Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 2nd clause");
          Formula.Disjunction _ ->
            Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 2nd clause");
        });
      Formula.Conjunction [Formula.Atom (Term.Fun LeF (_ : _ : _ : _)), _] ->
        Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 1st literal");
      Formula.Conjunction [Formula.Atom (Term.Fun (SumF _) _), _] ->
        Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 1st literal");
      Formula.Conjunction [Formula.Atom (Term.Fun (ConstF _) _), _] ->
        Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 1st literal");
      Formula.Conjunction [Formula.Atom (Term.Fun (ProdF _) _), _] ->
        Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 1st literal");
      Formula.Conjunction [Formula.Atom (Term.Fun EqF _), _] ->
        Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 1st literal");
      Formula.Conjunction [Formula.NegAtom _, _] ->
        Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 1st clause");
      Formula.Conjunction [Formula.Conjunction _, _] ->
        Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 1st clause");
      Formula.Conjunction [Formula.Disjunction _, _] ->
        Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 1st clause");
      Formula.Conjunction (_ : _ : _ : _) ->
        Sum_Type.Inl (Shows_Literal.showsl_lit "Conjunction of more than two");
      Formula.Disjunction _ -> def_checker_eq x ty phi;
    })
    (\ xa ->
      Sum_Type.Inl
        (((((Shows_Literal.showsl_lit "error in definibility checker for " .
              Shows_Literal.showsl x) .
             Shows_Literal.showsl_lit " on formula\n  ") .
            Formula.showsl_formula showsl_IA_exp phi) .
           Shows_Literal.showsl_literal "\n") .
          xa));

showsl_poly_constraint ::
  forall a.
    (Eq a, Orderings.Linorder a,
      Shows_Literal.Showl a) => Poly_constraint a -> String -> String;
showsl_poly_constraint (Poly_Ge p) =
  Show_Literal_Polynomial.showsl_poly p . Shows_Literal.showsl_lit " >= 0";
showsl_poly_constraint (Poly_Eq p) =
  Show_Literal_Polynomial.showsl_poly p . Shows_Literal.showsl_lit " = 0";

iA_exp_to_poly_constraint ::
  forall a.
    (Eq a, Orderings.Linorder a) => Term.Term Sig (a, Ty) -> Poly_constraint a;
iA_exp_to_poly_constraint (Term.Fun LeF [a, b]) =
  Poly_Ge (Polynomials.poly_minus (iA_exp_to_poly b) (iA_exp_to_poly a));
iA_exp_to_poly_constraint (Term.Fun EqF [a, b]) =
  Poly_Eq (Polynomials.poly_minus (iA_exp_to_poly b) (iA_exp_to_poly a));
iA_exp_to_poly_constraint (Term.Fun LessF [a, b]) =
  Poly_Ge
    (Polynomials.poly_minus
      (Polynomials.poly_minus (iA_exp_to_poly b) (iA_exp_to_poly a))
      Polynomials.one_poly);

interpret_poly_constraint ::
  forall a.
    (Orderings.Linorder a) => (a -> Arith.Int) -> Poly_constraint a -> Bool;
interpret_poly_constraint f (Poly_Ge p) =
  Arith.less_eq_int Arith.zero_int (Polynomials.eval_poly f p);
interpret_poly_constraint f (Poly_Eq p) =
  Arith.equal_int (Polynomials.eval_poly f p) Arith.zero_int;

vars_poly_constraint_list ::
  forall a. (Eq a, Orderings.Linorder a) => Poly_constraint a -> [a];
vars_poly_constraint_list (Poly_Ge p) = Polynomials.poly_vars_list p;
vars_poly_constraint_list (Poly_Eq p) = Polynomials.poly_vars_list p;

}
