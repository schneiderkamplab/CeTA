{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Transition_Removal(Transition_removal_info(..), lex_processor) where {

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
import qualified Container_Setup;
import qualified Term_More;
import qualified Sorted_Algebra;
import qualified Formula;
import qualified Term;
import qualified Set;
import qualified HOL;
import qualified Product_Type;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified List;
import qualified Sum_Type;
import qualified LTS;
import qualified Collection_Order;
import qualified Shows_Literal;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Cooperation_Program;

data Transition_removal_info a b c d e =
  Transition_removal_info (Cooperation_Program.Sharp c -> a) [d] b a (d -> e);

rank ::
  forall a b c d e.
    Transition_removal_info a b c d e -> Cooperation_Program.Sharp c -> a;
rank (Transition_removal_info x1 x2 x3 x4 x5) = x1;

hinter :: forall a b c d e. Transition_removal_info a b c d e -> d -> e;
hinter (Transition_removal_info x1 x2 x3 x4 x5) = x5;

removed :: forall a b c d e. Transition_removal_info a b c d e -> [d];
removed (Transition_removal_info x1 x2 x3 x4 x5) = x2;

processor ::
  forall a b c d e.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Eq a,
      Set_Impl.Set_impl a,
      Shows_Literal.Showl a) => ((a, LTS.Transition_rule b c d
                                       (Cooperation_Program.Sharp e)) ->
                                  Sum_Type.Sum (String -> String) ()) ->
                                  ((a, LTS.Transition_rule b c d
 (Cooperation_Program.Sharp e)) ->
                                    Sum_Type.Sum (String -> String) ()) ->
                                    [a] ->
                                      LTS.Lts_impl b c d
(Cooperation_Program.Sharp e) a ->
Sum_Type.Sum (String -> String)
  (LTS.Lts_impl b c d (Cooperation_Program.Sharp e) a);
processor check_weak check_strict td pi =
  Error_Monad.catch_error
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Error_Monad.forallM
          (\ (tr, tau) ->
            (if List.member td tr
              then Error_Monad.bind
                     (Check_Monad.check
                       (Cooperation_Program.is_sharp (LTS.source tau))
                       ((Shows_Literal.showsl_lit "non-sharp transition " .
                          Shows_Literal.showsl tr) .
                         Shows_Literal.showsl_lit " cannot be removed"))
                     (\ _ ->
                       Error_Monad.catch_error (check_strict (tr, tau))
                         (\ x ->
                           Sum_Type.Inl
                             (((Shows_Literal.showsl_lit
                                  "Failed to strictly orient transition " .
                                 Shows_Literal.showsl tr) .
                                Shows_Literal.showsl_literal "\n") .
                               x)))
              else (if Cooperation_Program.is_sharp (LTS.source tau)
                     then Error_Monad.catch_error (check_weak (tr, tau))
                            (\ x ->
                              Sum_Type.Inl
                                (((Shows_Literal.showsl_lit
                                     "Failed to weakly orient transition " .
                                    Shows_Literal.showsl tr) .
                                   Shows_Literal.showsl_literal "\n") .
                                  x))
                     else Sum_Type.Inr ())))
          (LTS.transitions_impl pi))
        (\ x -> Sum_Type.Inl (snd x)))
      (\ _ -> Sum_Type.Inr (LTS.del_transitions_impl pi td)))
    (\ x ->
      Sum_Type.Inl
        (((Shows_Literal.showsl_lit "Failed to eliminate transitions " .
            Shows_Literal.showsl_list td) .
           Shows_Literal.showsl_lit ":\n") .
          x));

bound_exp :: forall a b c d e. Transition_removal_info a b c d e -> a;
bound_exp (Transition_removal_info x1 x2 x3 x4 x5) = x4;

lex_less_formula ::
  forall a b c.
    (Shows_Literal.Showl a, Shows_Literal.Showl b,
      Shows_Literal.Showl c) => (Term.Term a (LTS.Trans_var b, c) ->
                                  Term.Term a (LTS.Trans_var b, c) ->
                                    Formula.Formula
                                      (Term.Term a (LTS.Trans_var b, c))) ->
                                  (Term.Term a (LTS.Trans_var b, c) ->
                                    Term.Term a (LTS.Trans_var b, c) ->
                                      Formula.Formula
(Term.Term a (LTS.Trans_var b, c))) ->
                                    [Term.Term a (LTS.Trans_var b, c)] ->
                                      [Term.Term a (LTS.Trans_var b, c)] ->
[Term.Term a (LTS.Trans_var b, c)] ->
  Formula.Formula (Term.Term a (LTS.Trans_var b, c));
lex_less_formula less_eq_formula less_formula xs ys zs =
  (case xs of {
    [] -> Formula.Disjunction [];
    x : xsa ->
      (case ys of {
        [] -> Formula.Disjunction [];
        y : ysa ->
          (case zs of {
            [] -> Formula.Disjunction [];
            z : zsa ->
              (case xsa of {
                [] -> (case ysa of {
                        [] -> (case zsa of {
                                [] -> Formula.form_and (less_formula y z)
(less_eq_formula x z);
                                _ : _ -> Formula.Disjunction [];
                              });
                        _ : _ -> Formula.Disjunction [];
                      });
                _ : _ ->
                  (case ysa of {
                    [] -> Formula.Disjunction [];
                    _ : _ ->
                      (case zsa of {
                        [] -> Formula.Disjunction [];
                        _ : _ ->
                          Formula.form_or
                            (Formula.form_and (less_formula y z)
                              (less_eq_formula x z))
                            (Formula.Conjunction
                              [less_eq_formula y z,
                                lex_less_formula less_eq_formula less_formula
                                  xsa ysa zsa]);
                      });
                  });
              });
          });
      });
  });

check_lex_strict ::
  forall a b c d e f.
    (Eq a, Shows_Literal.Showl a, Collection_Eq.Ceq b,
      Collection_Order.Ccompare b, Eq b, Shows_Literal.Showl b, Eq c,
      Shows_Literal.Showl c, HOL.Default d, Shows_Literal.Showl d,
      Collection_Order.Ccompare e, Eq e, Shows_Literal.Showl e,
      Shows_Literal.Showl f) => (a -> ([b], b)) ->
                                  Set.Set b ->
                                    (Term.Term a (LTS.Trans_var c, b) ->
                                      String -> String) ->
                                      (d ->
Formula.Formula (Term.Term a (LTS.Trans_var c, b)) ->
  Sum_Type.Sum (String -> String) ()) ->
(Bool ->
  Term.Term a (LTS.Trans_var c, b) ->
    Formula.Formula (Term.Term a (LTS.Trans_var c, b))) ->
  (Term.Term a (LTS.Trans_var c, b) ->
    Term.Term a (LTS.Trans_var c, b) ->
      Formula.Formula (Term.Term a (LTS.Trans_var c, b))) ->
    (Term.Term a (LTS.Trans_var c, b) ->
      Term.Term a (LTS.Trans_var c, b) ->
        Formula.Formula (Term.Term a (LTS.Trans_var c, b))) ->
      Transition_removal_info [Term.Term a (c, b)] b e f d ->
        LTS.Lts_impl a c b (Cooperation_Program.Sharp e) f ->
          (f, LTS.Transition_rule a c b (Cooperation_Program.Sharp e)) ->
            Sum_Type.Sum (String -> String) ();
check_lex_strict type_of_fun bool_types showsl_atom logic_checker normalize_lit
  less_eq_formula less_formula info pi (tr, LTS.Transition l r phi) =
  let {
    psi = lex_less_formula less_eq_formula less_formula
            (map (Sorted_Algebra.rename_vars_exp LTS.Pre) (bound_exp info))
            (map (Sorted_Algebra.rename_vars_exp LTS.Post) (rank info r))
            (map (Sorted_Algebra.rename_vars_exp LTS.Pre) (rank info l));
  } in Error_Monad.bind
         (Check_Monad.check
           (Formula.formula (Formula.is_bool type_of_fun bool_types) psi)
           ((Shows_Literal.showsl_lit "lex-less does not encode valid formula" .
              Shows_Literal.showsl_literal "\n") .
             Formula.showsl_formulaa psi))
         (\ _ ->
           Formula.check_valid_formula showsl_atom logic_checker normalize_lit
             (hinter info tr)
             (Formula.Disjunction
               [psi, Formula.form_not
                       (Formula.map_formula
                         (Sorted_Algebra.rename_vars_exp LTS.Pre)
                         (LTS.assertion_of pi l)),
                 Formula.form_not phi]));

lex_leq_formula ::
  forall a b c.
    (Shows_Literal.Showl a, Shows_Literal.Showl b,
      Shows_Literal.Showl c) => (Term.Term a (LTS.Trans_var b, c) ->
                                  Term.Term a (LTS.Trans_var b, c) ->
                                    Formula.Formula
                                      (Term.Term a (LTS.Trans_var b, c))) ->
                                  (Term.Term a (LTS.Trans_var b, c) ->
                                    Term.Term a (LTS.Trans_var b, c) ->
                                      Formula.Formula
(Term.Term a (LTS.Trans_var b, c))) ->
                                    [Term.Term a (LTS.Trans_var b, c)] ->
                                      [Term.Term a (LTS.Trans_var b, c)] ->
[Term.Term a (LTS.Trans_var b, c)] ->
  Formula.Formula (Term.Term a (LTS.Trans_var b, c));
lex_leq_formula less_eq_formula less_formula xs ys zs =
  (case xs of {
    [] -> (case ys of {
            [] -> (case zs of {
                    [] -> Formula.Conjunction [];
                    _ : _ -> Formula.Disjunction [];
                  });
            _ : _ -> Formula.Disjunction [];
          });
    x : xsa ->
      (case ys of {
        [] -> Formula.Disjunction [];
        y : ysa ->
          (case zs of {
            [] -> Formula.Disjunction [];
            z : zsa ->
              (case xsa of {
                [] -> (case ysa of {
                        [] -> (case zsa of {
                                [] -> less_eq_formula y z;
                                _ : _ -> Formula.Disjunction [];
                              });
                        _ : _ -> Formula.Disjunction [];
                      });
                _ : _ ->
                  (case ysa of {
                    [] -> Formula.Disjunction [];
                    _ : _ ->
                      (case zsa of {
                        [] -> Formula.Disjunction [];
                        _ : _ ->
                          Formula.form_or
                            (Formula.form_and (less_formula y z)
                              (less_eq_formula x z))
                            (Formula.Conjunction
                              [less_eq_formula y z,
                                lex_leq_formula less_eq_formula less_formula xsa
                                  ysa zsa]);
                      });
                  });
              });
          });
      });
  });

check_lex_weak ::
  forall a b c d e f.
    (Eq a, Shows_Literal.Showl a, Collection_Eq.Ceq b,
      Collection_Order.Ccompare b, Eq b, Shows_Literal.Showl b, Eq c,
      Shows_Literal.Showl c, HOL.Default d, Shows_Literal.Showl d,
      Collection_Order.Ccompare e, Eq e, Shows_Literal.Showl e,
      Shows_Literal.Showl f) => (a -> ([b], b)) ->
                                  Set.Set b ->
                                    (Term.Term a (LTS.Trans_var c, b) ->
                                      String -> String) ->
                                      (d ->
Formula.Formula (Term.Term a (LTS.Trans_var c, b)) ->
  Sum_Type.Sum (String -> String) ()) ->
(Bool ->
  Term.Term a (LTS.Trans_var c, b) ->
    Formula.Formula (Term.Term a (LTS.Trans_var c, b))) ->
  (Term.Term a (LTS.Trans_var c, b) ->
    Term.Term a (LTS.Trans_var c, b) ->
      Formula.Formula (Term.Term a (LTS.Trans_var c, b))) ->
    (Term.Term a (LTS.Trans_var c, b) ->
      Term.Term a (LTS.Trans_var c, b) ->
        Formula.Formula (Term.Term a (LTS.Trans_var c, b))) ->
      Transition_removal_info [Term.Term a (c, b)] b e f d ->
        LTS.Lts_impl a c b (Cooperation_Program.Sharp e) f ->
          (f, LTS.Transition_rule a c b (Cooperation_Program.Sharp e)) ->
            Sum_Type.Sum (String -> String) ();
check_lex_weak type_of_fun bool_types showsl_atom logic_checker normalize_lit
  less_eq_formula less_formula info pi (tr, LTS.Transition l r phi) =
  let {
    psi = lex_leq_formula less_eq_formula less_formula
            (map (Sorted_Algebra.rename_vars_exp LTS.Pre) (bound_exp info))
            (map (Sorted_Algebra.rename_vars_exp LTS.Post) (rank info r))
            (map (Sorted_Algebra.rename_vars_exp LTS.Pre) (rank info l));
  } in Error_Monad.bind
         (Check_Monad.check
           (Formula.formula (Formula.is_bool type_of_fun bool_types) psi)
           ((Shows_Literal.showsl_lit "lex-leq does not encode valid formula" .
              Shows_Literal.showsl_literal "\n") .
             Formula.showsl_formulaa psi))
         (\ _ ->
           Formula.check_valid_formula showsl_atom logic_checker normalize_lit
             (hinter info tr)
             (Formula.Disjunction
               [psi, Formula.form_not
                       (Formula.map_formula
                         (Sorted_Algebra.rename_vars_exp LTS.Pre)
                         (LTS.assertion_of pi l)),
                 Formula.form_not phi]));

lex_processor ::
  forall a b c d e f.
    (Eq a, Shows_Literal.Showl a, Collection_Eq.Ceq b,
      Collection_Order.Ccompare b, Eq b, Shows_Literal.Showl b, Eq c,
      Shows_Literal.Showl c, HOL.Default d, Shows_Literal.Showl d,
      Collection_Order.Ccompare e, Eq e, Shows_Literal.Showl e,
      Collection_Eq.Ceq f, Collection_Order.Ccompare f, Eq f,
      Set_Impl.Set_impl f,
      Shows_Literal.Showl f) => (a -> ([b], b)) ->
                                  Set.Set b ->
                                    (Term.Term a (LTS.Trans_var c, b) ->
                                      String -> String) ->
                                      (d ->
Formula.Formula (Term.Term a (LTS.Trans_var c, b)) ->
  Sum_Type.Sum (String -> String) ()) ->
(Bool ->
  Term.Term a (LTS.Trans_var c, b) ->
    Formula.Formula (Term.Term a (LTS.Trans_var c, b))) ->
  b -> (Term.Term a (LTS.Trans_var c, b) ->
         Term.Term a (LTS.Trans_var c, b) ->
           Formula.Formula (Term.Term a (LTS.Trans_var c, b))) ->
         (Term.Term a (LTS.Trans_var c, b) ->
           Term.Term a (LTS.Trans_var c, b) ->
             Formula.Formula (Term.Term a (LTS.Trans_var c, b))) ->
           (Term.Term a (LTS.Trans_var c, b) -> Bool) ->
             Transition_removal_info [Term.Term a (c, b)] b e f d ->
               LTS.Lts_impl a c b (Cooperation_Program.Sharp e) f ->
                 Sum_Type.Sum (String -> String)
                   (LTS.Lts_impl a c b (Cooperation_Program.Sharp e) f);
lex_processor type_of_fun bool_types showsl_atom logic_checker normalize_lit
  dom_type less_eq_formula less_formula is_constant info pi =
  Error_Monad.bind
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ l ->
          Error_Monad.catch_error
            (Error_Monad.forallM
              (\ e ->
                Check_Monad.check
                  (Sorted_Algebra.has_type type_of_fun e dom_type)
                  (Shows_Literal.showsl_lit "Unexpected type of expression:\n" .
                    Term_More.showsl_terma e))
              (rank info l))
            (\ x -> Sum_Type.Inl (snd x)))
        (LTS.nodes_lts_impl pi))
      (\ x -> Sum_Type.Inl (snd x)))
    (\ _ ->
      Error_Monad.bind
        (Error_Monad.catch_error
          (Error_Monad.forallM
            (\ e ->
              Check_Monad.check (Sorted_Algebra.has_type type_of_fun e dom_type)
                (Shows_Literal.showsl_lit "Unexpected type of bound: " .
                  Term_More.showsl_terma e))
            (bound_exp info))
          (\ x -> Sum_Type.Inl (snd x)))
        (\ _ ->
          Error_Monad.bind
            (Error_Monad.catch_error
              (Error_Monad.forallM
                (\ e ->
                  Check_Monad.check (is_constant e)
                    (Shows_Literal.showsl_lit "Non-constant bound: " .
                      Term_More.showsl_terma e))
                (map (Sorted_Algebra.rename_vars_exp LTS.Pre) (bound_exp info)))
              (\ x -> Sum_Type.Inl (snd x)))
            (\ _ ->
              processor
                (check_lex_weak type_of_fun bool_types showsl_atom logic_checker
                  normalize_lit less_eq_formula less_formula info pi)
                (check_lex_strict type_of_fun bool_types showsl_atom
                  logic_checker normalize_lit less_eq_formula less_formula info
                  pi)
                (removed info) pi)));

}
