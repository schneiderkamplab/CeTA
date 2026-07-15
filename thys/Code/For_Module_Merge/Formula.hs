{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Formula(Formula(..), equal_formula, form_or, form_and, form_not, get_Atom,
           formula, in_vars_formula, is_bool, map_formula,
           check_trivial_implication, showsl_formula, showsl_formulaa,
           check_valid_formula)
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
import qualified Error_Monad;
import qualified Check_Monad;
import qualified Sum_Type;
import qualified Shows_Literal;
import qualified Sorted_Algebra;
import qualified Set;
import qualified Collection_Order;
import qualified Collection_Eq;
import qualified Product_Type;
import qualified HOL;
import qualified Term_More;
import qualified List;
import qualified Term;

data Formula a = Atom a | NegAtom a | Conjunction [Formula a]
  | Disjunction [Formula a];

instance (Eq a) => Eq (Formula a) where {
  a == b = equal_formula a b;
};

equal_formula :: forall a. (Eq a) => Formula a -> Formula a -> Bool;
equal_formula (Conjunction x3) (Disjunction x4) = False;
equal_formula (Disjunction x4) (Conjunction x3) = False;
equal_formula (NegAtom x2) (Disjunction x4) = False;
equal_formula (Disjunction x4) (NegAtom x2) = False;
equal_formula (NegAtom x2) (Conjunction x3) = False;
equal_formula (Conjunction x3) (NegAtom x2) = False;
equal_formula (Atom x1) (Disjunction x4) = False;
equal_formula (Disjunction x4) (Atom x1) = False;
equal_formula (Atom x1) (Conjunction x3) = False;
equal_formula (Conjunction x3) (Atom x1) = False;
equal_formula (Atom x1) (NegAtom x2) = False;
equal_formula (NegAtom x2) (Atom x1) = False;
equal_formula (Disjunction x4) (Disjunction y4) = x4 == y4;
equal_formula (Conjunction x3) (Conjunction y3) = x3 == y3;
equal_formula (NegAtom x2) (NegAtom y2) = x2 == y2;
equal_formula (Atom x1) (Atom y1) = x1 == y1;

form_or :: forall a. Formula a -> Formula a -> Formula a;
form_or (Disjunction []) psi = psi;
form_or (Atom v) (Disjunction []) = Atom v;
form_or (NegAtom v) (Disjunction []) = NegAtom v;
form_or (Conjunction v) (Disjunction []) = Conjunction v;
form_or (Disjunction (va : vb)) (Disjunction []) = Disjunction (va : vb);
form_or (Disjunction (v : va)) (Disjunction (vb : vc)) =
  Disjunction ((v : va) ++ vb : vc);
form_or (Disjunction (v : va)) (Atom vb) = Disjunction ((v : va) ++ [Atom vb]);
form_or (Disjunction (v : va)) (NegAtom vb) =
  Disjunction ((v : va) ++ [NegAtom vb]);
form_or (Disjunction (v : va)) (Conjunction vb) =
  Disjunction ((v : va) ++ [Conjunction vb]);
form_or (Atom v) (Disjunction (va : vb)) = Disjunction (Atom v : va : vb);
form_or (NegAtom v) (Disjunction (va : vb)) = Disjunction (NegAtom v : va : vb);
form_or (Conjunction v) (Disjunction (va : vb)) =
  Disjunction (Conjunction v : va : vb);
form_or (Atom v) (Atom va) = Disjunction [Atom v, Atom va];
form_or (Atom v) (NegAtom va) = Disjunction [Atom v, NegAtom va];
form_or (Atom v) (Conjunction va) = Disjunction [Atom v, Conjunction va];
form_or (NegAtom v) (Atom va) = Disjunction [NegAtom v, Atom va];
form_or (NegAtom v) (NegAtom va) = Disjunction [NegAtom v, NegAtom va];
form_or (NegAtom v) (Conjunction va) = Disjunction [NegAtom v, Conjunction va];
form_or (Conjunction v) (Atom va) = Disjunction [Conjunction v, Atom va];
form_or (Conjunction v) (NegAtom va) = Disjunction [Conjunction v, NegAtom va];
form_or (Conjunction v) (Conjunction va) =
  Disjunction [Conjunction v, Conjunction va];

cnf_form_or :: forall a. Formula a -> Formula a -> Formula a;
cnf_form_or (Conjunction phi_s) (Conjunction psi_s) =
  Conjunction (concatMap (\ phi -> map (form_or phi) psi_s) phi_s);
cnf_form_or (Atom v) psi = form_or (Atom v) psi;
cnf_form_or (NegAtom v) psi = form_or (NegAtom v) psi;
cnf_form_or (Disjunction v) psi = form_or (Disjunction v) psi;
cnf_form_or phi (Atom v) = form_or phi (Atom v);
cnf_form_or phi (NegAtom v) = form_or phi (NegAtom v);
cnf_form_or phi (Disjunction v) = form_or phi (Disjunction v);

form_cnf_ex :: forall a. [Formula a] -> Formula a;
form_cnf_ex [] = Conjunction [Disjunction []];
form_cnf_ex (phi : phi_s) = cnf_form_or phi (form_cnf_ex phi_s);

form_and :: forall a. Formula a -> Formula a -> Formula a;
form_and (Conjunction []) psi = psi;
form_and (Atom v) (Conjunction []) = Atom v;
form_and (NegAtom v) (Conjunction []) = NegAtom v;
form_and (Conjunction (va : vb)) (Conjunction []) = Conjunction (va : vb);
form_and (Disjunction v) (Conjunction []) = Disjunction v;
form_and (Conjunction (v : va)) (Conjunction (vb : vc)) =
  Conjunction ((v : va) ++ vb : vc);
form_and (Conjunction (v : va)) (Atom vb) = Conjunction ((v : va) ++ [Atom vb]);
form_and (Conjunction (v : va)) (NegAtom vb) =
  Conjunction ((v : va) ++ [NegAtom vb]);
form_and (Conjunction (v : va)) (Disjunction vb) =
  Conjunction ((v : va) ++ [Disjunction vb]);
form_and (Atom v) (Conjunction (va : vb)) = Conjunction (Atom v : va : vb);
form_and (NegAtom v) (Conjunction (va : vb)) =
  Conjunction (NegAtom v : va : vb);
form_and (Disjunction v) (Conjunction (va : vb)) =
  Conjunction (Disjunction v : va : vb);
form_and (Atom v) (Atom va) = Conjunction [Atom v, Atom va];
form_and (Atom v) (NegAtom va) = Conjunction [Atom v, NegAtom va];
form_and (Atom v) (Disjunction va) = Conjunction [Atom v, Disjunction va];
form_and (NegAtom v) (Atom va) = Conjunction [NegAtom v, Atom va];
form_and (NegAtom v) (NegAtom va) = Conjunction [NegAtom v, NegAtom va];
form_and (NegAtom v) (Disjunction va) = Conjunction [NegAtom v, Disjunction va];
form_and (Disjunction v) (Atom va) = Conjunction [Disjunction v, Atom va];
form_and (Disjunction v) (NegAtom va) = Conjunction [Disjunction v, NegAtom va];
form_and (Disjunction v) (Disjunction va) =
  Conjunction [Disjunction v, Disjunction va];

form_all :: forall a. [Formula a] -> Formula a;
form_all [] = Conjunction [];
form_all (phi : phi_s) = form_and phi (form_all phi_s);

flatten :: forall a. Formula a -> Formula a;
flatten (Conjunction phi_s) = form_all (map flatten phi_s);
flatten (Disjunction phi_s) = form_cnf_ex (map flatten phi_s);
flatten (Atom v) = Conjunction [Disjunction [Atom v]];
flatten (NegAtom v) = Conjunction [Disjunction [NegAtom v]];

is_Atom :: forall a. Formula a -> Bool;
is_Atom (Atom uu) = True;
is_Atom (NegAtom v) = False;
is_Atom (Conjunction v) = False;
is_Atom (Disjunction v) = False;

form_not :: forall a. Formula a -> Formula a;
form_not (Atom a) = NegAtom a;
form_not (NegAtom a) = Atom a;
form_not (Conjunction phi_s) = Disjunction (map form_not phi_s);
form_not (Disjunction phi_s) = Conjunction (map form_not phi_s);

get_Atom :: forall a. Formula a -> a;
get_Atom (Atom a) = a;
get_Atom (NegAtom a) = a;

formula :: forall a. (a -> Bool) -> Formula a -> Bool;
formula atom (Atom a) = atom a;
formula atom (NegAtom a) = atom a;
formula atom (Conjunction phi_s) = all (formula atom) phi_s;
formula atom (Disjunction phi_s) = all (formula atom) phi_s;

in_vars_formula :: forall a b. (Eq a) => a -> Formula (Term.Term b a) -> Bool;
in_vars_formula x (Atom a) = List.member (Term_More.vars_term_list a) x;
in_vars_formula x (NegAtom a) = List.member (Term_More.vars_term_list a) x;
in_vars_formula x (Conjunction phi_s) = any (in_vars_formula x) phi_s;
in_vars_formula x (Disjunction phi_s) = any (in_vars_formula x) phi_s;

trivial_checker :: forall a. (Eq a) => [Formula a] -> Bool;
trivial_checker lits = (case List.partition is_Atom lits of {
                         (asa, nas) -> let {
 pos = map get_Atom asa;
 neg = map get_Atom nas;
                                       } in any (List.member neg) pos;
                       });

get_conjunctions :: forall a. Formula a -> [Formula a];
get_conjunctions (Conjunction phis) = concatMap get_conjunctions phis;
get_conjunctions (Atom v) = [Atom v];
get_conjunctions (NegAtom v) = [NegAtom v];
get_conjunctions (Disjunction v) = [Disjunction v];

get_disjunctions :: forall a. Formula a -> [Formula a];
get_disjunctions (Disjunction phis) = concatMap get_disjunctions phis;
get_disjunctions (Atom v) = [Atom v];
get_disjunctions (NegAtom v) = [NegAtom v];
get_disjunctions (Conjunction v) = [Conjunction v];

is_bool ::
  forall a b c.
    (Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Eq b) => (a -> ([b], b)) -> Set.Set b -> Term.Term a (c, b) -> Bool;
is_bool type_of_fun bool_types e =
  Set.bex bool_types (Sorted_Algebra.has_type type_of_fun e);

map_formula :: forall a b. (a -> b) -> Formula a -> Formula b;
map_formula f (Atom x1) = Atom (f x1);
map_formula f (NegAtom x2) = NegAtom (f x2);
map_formula f (Conjunction x3) = Conjunction (map (map_formula f) x3);
map_formula f (Disjunction x4) = Disjunction (map (map_formula f) x4);

trivial_clause_checker :: forall a. (Eq a) => Formula a -> Bool;
trivial_clause_checker f = (case f of {
                             Disjunction a -> trivial_checker a;
                           });

check_trivial_implication :: forall a. (Eq a) => Formula a -> Formula a -> Bool;
check_trivial_implication phi psi =
  all (\ phia ->
        let {
          c_phis = get_conjunctions phia;
        } in any (\ psia -> all (List.member c_phis) (get_conjunctions psia))
               (get_disjunctions psi))
    (get_disjunctions phi);

showsl_formula ::
  forall a. (a -> String -> String) -> Formula a -> String -> String;
showsl_formula showsl_atom (Atom a) = showsl_atom a;
showsl_formula showsl_atom (NegAtom a) =
  (Shows_Literal.showsl_literal "! (" . showsl_atom a) .
    Shows_Literal.showsl_literal ")";
showsl_formula showsl_atom (Conjunction fs) =
  let {
    a = map (showsl_formula showsl_atom) fs;
  } in Shows_Literal.showsl_list_gen id "True" "Conj[" ", " "]" a;
showsl_formula showsl_atom (Disjunction fs) =
  let {
    a = map (showsl_formula showsl_atom) fs;
  } in Shows_Literal.showsl_list_gen id "False" "Disj[" ", " "]" a;

normalize_lits ::
  forall a b c.
    (Shows_Literal.Showl b) => (Bool ->
                                 Term.Term a (b, c) ->
                                   Formula (Term.Term a (b, c))) ->
                                 Formula (Term.Term a (b, c)) ->
                                   Formula (Term.Term a (b, c));
normalize_lits normalize_lit (Conjunction phi_s) =
  Conjunction (map (normalize_lits normalize_lit) phi_s);
normalize_lits normalize_lit (Disjunction phi_s) =
  Disjunction (map (normalize_lits normalize_lit) phi_s);
normalize_lits normalize_lit (NegAtom phi) = normalize_lit False phi;
normalize_lits normalize_lit (Atom phi) = normalize_lit True phi;

showsl_formulaa ::
  forall a. (Shows_Literal.Showl a) => Formula a -> String -> String;
showsl_formulaa (Atom a) = Shows_Literal.showsl a;
showsl_formulaa (NegAtom a) =
  (Shows_Literal.showsl_lit "! (" . Shows_Literal.showsl a) .
    Shows_Literal.showsl_lit ")";
showsl_formulaa (Conjunction a) =
  Shows_Literal.showsl_list_gen id "TRUE" "(" " & " ")" (map showsl_formulaa a);
showsl_formulaa (Disjunction a) =
  Shows_Literal.showsl_list_gen id "FALSE" "(" " | " ")"
    (map showsl_formulaa a);

check_valid_formula ::
  forall a b c d.
    (Eq a, Eq b, Shows_Literal.Showl b, Eq c, HOL.Default d,
      Shows_Literal.Showl d) => (Term.Term a (b, c) -> String -> String) ->
                                  (d -> Formula (Term.Term a (b, c)) ->
  Sum_Type.Sum (String -> String) ()) ->
                                    (Bool ->
                                      Term.Term a (b, c) ->
Formula (Term.Term a (b, c))) ->
                                      d ->
Formula (Term.Term a (b, c)) -> Sum_Type.Sum (String -> String) ();
check_valid_formula showsl_atom logic_checker normalize_lit h phi =
  Error_Monad.catch_error
    (case flatten phi of {
      Conjunction phi_s ->
        Error_Monad.catch_error
          (Error_Monad.forallM
            (\ phia ->
              Error_Monad.catch_error
                (Check_Monad.check (trivial_clause_checker phia)
                  "trivial clause checker failed")
                (\ _ ->
                  (case flatten (normalize_lits normalize_lit phia) of {
                    Conjunction phi_sa ->
                      Error_Monad.catch_error
                        (Error_Monad.forallM (logic_checker h) phi_sa)
                        (\ x -> Sum_Type.Inl (snd x));
                  })))
            phi_s)
          (\ x -> Sum_Type.Inl (snd x));
    })
    (\ x ->
      Sum_Type.Inl
        (((Shows_Literal.showsl_lit "problem in checking validity of formula " .
            showsl_formula showsl_atom phi) .
           Shows_Literal.showsl_literal "\n") .
          x));

}
