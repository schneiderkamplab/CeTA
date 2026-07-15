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
import qualified HOL;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Shows_Literal;
import qualified Arith;
import qualified Term_Rewriting;

data Transition_removal_info a b c d e =
  Transition_removal_info (Term_Rewriting.Sharp c -> a) [d] b a (d -> e);

rank ::
  forall a b c d e.
    Transition_removal_info a b c d e -> Term_Rewriting.Sharp c -> a;
rank (Transition_removal_info x1 x2 x3 x4 x5) = x1;

hinter :: forall a b c d e. Transition_removal_info a b c d e -> d -> e;
hinter (Transition_removal_info x1 x2 x3 x4 x5) = x5;

removed :: forall a b c d e. Transition_removal_info a b c d e -> [d];
removed (Transition_removal_info x1 x2 x3 x4 x5) = x2;

processor ::
  forall a b c d e.
    (Arith.Ceq a, Arith.Ccompare a, Eq a, Arith.Set_impl a,
      Shows_Literal.Showl a) => ((a, Term_Rewriting.Transition_rule b c d
                                       (Term_Rewriting.Sharp e)) ->
                                  Sum_Type.Sum (String -> String) ()) ->
                                  ((a, Term_Rewriting.Transition_rule b c d
 (Term_Rewriting.Sharp e)) ->
                                    Sum_Type.Sum (String -> String) ()) ->
                                    [a] ->
                                      Term_Rewriting.Lts_impl b c d
(Term_Rewriting.Sharp e) a ->
Sum_Type.Sum (String -> String)
  (Term_Rewriting.Lts_impl b c d (Term_Rewriting.Sharp e) a);
processor check_weak check_strict td pi =
  Error_Monad.catch_error
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Error_Monad.forallM
          (\ (tr, tau) ->
            (if Arith.membera td tr
              then Error_Monad.bind
                     (Check_Monad.check
                       (Term_Rewriting.is_sharp (Term_Rewriting.source tau))
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
              else (if Term_Rewriting.is_sharp (Term_Rewriting.source tau)
                     then Error_Monad.catch_error (check_weak (tr, tau))
                            (\ x ->
                              Sum_Type.Inl
                                (((Shows_Literal.showsl_lit
                                     "Failed to weakly orient transition " .
                                    Shows_Literal.showsl tr) .
                                   Shows_Literal.showsl_literal "\n") .
                                  x))
                     else Sum_Type.Inr ())))
          (Term_Rewriting.transitions_impl pi))
        (\ x -> Sum_Type.Inl (snd x)))
      (\ _ -> Sum_Type.Inr (Term_Rewriting.del_transitions_impl pi td)))
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
      Shows_Literal.Showl c) => (Term_Rewriting.Term a
                                   (Term_Rewriting.Trans_var b, c) ->
                                  Term_Rewriting.Term a
                                    (Term_Rewriting.Trans_var b, c) ->
                                    Term_Rewriting.Formula
                                      (Term_Rewriting.Term a
(Term_Rewriting.Trans_var b, c))) ->
                                  (Term_Rewriting.Term a
                                     (Term_Rewriting.Trans_var b, c) ->
                                    Term_Rewriting.Term a
                                      (Term_Rewriting.Trans_var b, c) ->
                                      Term_Rewriting.Formula
(Term_Rewriting.Term a (Term_Rewriting.Trans_var b, c))) ->
                                    [Term_Rewriting.Term a
                                       (Term_Rewriting.Trans_var b, c)] ->
                                      [Term_Rewriting.Term a
 (Term_Rewriting.Trans_var b, c)] ->
[Term_Rewriting.Term a (Term_Rewriting.Trans_var b, c)] ->
  Term_Rewriting.Formula
    (Term_Rewriting.Term a (Term_Rewriting.Trans_var b, c));
lex_less_formula less_eq_formula less_formula xs ys zs =
  (case xs of {
    [] -> Term_Rewriting.Disjunction [];
    x : xsa ->
      (case ys of {
        [] -> Term_Rewriting.Disjunction [];
        y : ysa ->
          (case zs of {
            [] -> Term_Rewriting.Disjunction [];
            z : zsa ->
              (case xsa of {
                [] -> (case ysa of {
                        [] -> (case zsa of {
                                [] -> Term_Rewriting.form_and (less_formula y z)
(less_eq_formula x z);
                                _ : _ -> Term_Rewriting.Disjunction [];
                              });
                        _ : _ -> Term_Rewriting.Disjunction [];
                      });
                _ : _ ->
                  (case ysa of {
                    [] -> Term_Rewriting.Disjunction [];
                    _ : _ ->
                      (case zsa of {
                        [] -> Term_Rewriting.Disjunction [];
                        _ : _ ->
                          Term_Rewriting.form_or
                            (Term_Rewriting.form_and (less_formula y z)
                              (less_eq_formula x z))
                            (Term_Rewriting.Conjunction
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
    (Eq a, Shows_Literal.Showl a, Arith.Ceq b, Arith.Ccompare b, Eq b,
      Shows_Literal.Showl b, Eq c, Shows_Literal.Showl c, HOL.Default d,
      Shows_Literal.Showl d, Arith.Ccompare e, Eq e, Shows_Literal.Showl e,
      Shows_Literal.Showl f) => (a -> ([b], b)) ->
                                  Arith.Set b ->
                                    (Term_Rewriting.Term a
                                       (Term_Rewriting.Trans_var c, b) ->
                                      String -> String) ->
                                      (d ->
Term_Rewriting.Formula
  (Term_Rewriting.Term a (Term_Rewriting.Trans_var c, b)) ->
  Sum_Type.Sum (String -> String) ()) ->
(Bool ->
  Term_Rewriting.Term a (Term_Rewriting.Trans_var c, b) ->
    Term_Rewriting.Formula
      (Term_Rewriting.Term a (Term_Rewriting.Trans_var c, b))) ->
  (Term_Rewriting.Term a (Term_Rewriting.Trans_var c, b) ->
    Term_Rewriting.Term a (Term_Rewriting.Trans_var c, b) ->
      Term_Rewriting.Formula
        (Term_Rewriting.Term a (Term_Rewriting.Trans_var c, b))) ->
    (Term_Rewriting.Term a (Term_Rewriting.Trans_var c, b) ->
      Term_Rewriting.Term a (Term_Rewriting.Trans_var c, b) ->
        Term_Rewriting.Formula
          (Term_Rewriting.Term a (Term_Rewriting.Trans_var c, b))) ->
      Transition_removal_info [Term_Rewriting.Term a (c, b)] b e f d ->
        Term_Rewriting.Lts_impl a c b (Term_Rewriting.Sharp e) f ->
          (f, Term_Rewriting.Transition_rule a c b (Term_Rewriting.Sharp e)) ->
            Sum_Type.Sum (String -> String) ();
check_lex_strict type_of_fun bool_types showsl_atom logic_checker normalize_lit
  less_eq_formula less_formula info pi (tr, Term_Rewriting.Transition l r phi) =
  let {
    psi = lex_less_formula less_eq_formula less_formula
            (map (Term_Rewriting.rename_vars_exp Term_Rewriting.Pre)
              (bound_exp info))
            (map (Term_Rewriting.rename_vars_exp Term_Rewriting.Post)
              (rank info r))
            (map (Term_Rewriting.rename_vars_exp Term_Rewriting.Pre)
              (rank info l));
  } in Error_Monad.bind
         (Check_Monad.check
           (Term_Rewriting.formula
             (Term_Rewriting.is_bool type_of_fun bool_types) psi)
           ((Shows_Literal.showsl_lit "lex-less does not encode valid formula" .
              Shows_Literal.showsl_literal "\n") .
             Term_Rewriting.showsl_formulaa psi))
         (\ _ ->
           Term_Rewriting.check_valid_formula showsl_atom logic_checker
             normalize_lit (hinter info tr)
             (Term_Rewriting.Disjunction
               [psi, Term_Rewriting.form_not
                       (Term_Rewriting.map_formula
                         (Term_Rewriting.rename_vars_exp Term_Rewriting.Pre)
                         (Term_Rewriting.assertion_of pi l)),
                 Term_Rewriting.form_not phi]));

lex_leq_formula ::
  forall a b c.
    (Shows_Literal.Showl a, Shows_Literal.Showl b,
      Shows_Literal.Showl c) => (Term_Rewriting.Term a
                                   (Term_Rewriting.Trans_var b, c) ->
                                  Term_Rewriting.Term a
                                    (Term_Rewriting.Trans_var b, c) ->
                                    Term_Rewriting.Formula
                                      (Term_Rewriting.Term a
(Term_Rewriting.Trans_var b, c))) ->
                                  (Term_Rewriting.Term a
                                     (Term_Rewriting.Trans_var b, c) ->
                                    Term_Rewriting.Term a
                                      (Term_Rewriting.Trans_var b, c) ->
                                      Term_Rewriting.Formula
(Term_Rewriting.Term a (Term_Rewriting.Trans_var b, c))) ->
                                    [Term_Rewriting.Term a
                                       (Term_Rewriting.Trans_var b, c)] ->
                                      [Term_Rewriting.Term a
 (Term_Rewriting.Trans_var b, c)] ->
[Term_Rewriting.Term a (Term_Rewriting.Trans_var b, c)] ->
  Term_Rewriting.Formula
    (Term_Rewriting.Term a (Term_Rewriting.Trans_var b, c));
lex_leq_formula less_eq_formula less_formula xs ys zs =
  (case xs of {
    [] -> (case ys of {
            [] -> (case zs of {
                    [] -> Term_Rewriting.Conjunction [];
                    _ : _ -> Term_Rewriting.Disjunction [];
                  });
            _ : _ -> Term_Rewriting.Disjunction [];
          });
    x : xsa ->
      (case ys of {
        [] -> Term_Rewriting.Disjunction [];
        y : ysa ->
          (case zs of {
            [] -> Term_Rewriting.Disjunction [];
            z : zsa ->
              (case xsa of {
                [] -> (case ysa of {
                        [] -> (case zsa of {
                                [] -> less_eq_formula y z;
                                _ : _ -> Term_Rewriting.Disjunction [];
                              });
                        _ : _ -> Term_Rewriting.Disjunction [];
                      });
                _ : _ ->
                  (case ysa of {
                    [] -> Term_Rewriting.Disjunction [];
                    _ : _ ->
                      (case zsa of {
                        [] -> Term_Rewriting.Disjunction [];
                        _ : _ ->
                          Term_Rewriting.form_or
                            (Term_Rewriting.form_and (less_formula y z)
                              (less_eq_formula x z))
                            (Term_Rewriting.Conjunction
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
    (Eq a, Shows_Literal.Showl a, Arith.Ceq b, Arith.Ccompare b, Eq b,
      Shows_Literal.Showl b, Eq c, Shows_Literal.Showl c, HOL.Default d,
      Shows_Literal.Showl d, Arith.Ccompare e, Eq e, Shows_Literal.Showl e,
      Shows_Literal.Showl f) => (a -> ([b], b)) ->
                                  Arith.Set b ->
                                    (Term_Rewriting.Term a
                                       (Term_Rewriting.Trans_var c, b) ->
                                      String -> String) ->
                                      (d ->
Term_Rewriting.Formula
  (Term_Rewriting.Term a (Term_Rewriting.Trans_var c, b)) ->
  Sum_Type.Sum (String -> String) ()) ->
(Bool ->
  Term_Rewriting.Term a (Term_Rewriting.Trans_var c, b) ->
    Term_Rewriting.Formula
      (Term_Rewriting.Term a (Term_Rewriting.Trans_var c, b))) ->
  (Term_Rewriting.Term a (Term_Rewriting.Trans_var c, b) ->
    Term_Rewriting.Term a (Term_Rewriting.Trans_var c, b) ->
      Term_Rewriting.Formula
        (Term_Rewriting.Term a (Term_Rewriting.Trans_var c, b))) ->
    (Term_Rewriting.Term a (Term_Rewriting.Trans_var c, b) ->
      Term_Rewriting.Term a (Term_Rewriting.Trans_var c, b) ->
        Term_Rewriting.Formula
          (Term_Rewriting.Term a (Term_Rewriting.Trans_var c, b))) ->
      Transition_removal_info [Term_Rewriting.Term a (c, b)] b e f d ->
        Term_Rewriting.Lts_impl a c b (Term_Rewriting.Sharp e) f ->
          (f, Term_Rewriting.Transition_rule a c b (Term_Rewriting.Sharp e)) ->
            Sum_Type.Sum (String -> String) ();
check_lex_weak type_of_fun bool_types showsl_atom logic_checker normalize_lit
  less_eq_formula less_formula info pi (tr, Term_Rewriting.Transition l r phi) =
  let {
    psi = lex_leq_formula less_eq_formula less_formula
            (map (Term_Rewriting.rename_vars_exp Term_Rewriting.Pre)
              (bound_exp info))
            (map (Term_Rewriting.rename_vars_exp Term_Rewriting.Post)
              (rank info r))
            (map (Term_Rewriting.rename_vars_exp Term_Rewriting.Pre)
              (rank info l));
  } in Error_Monad.bind
         (Check_Monad.check
           (Term_Rewriting.formula
             (Term_Rewriting.is_bool type_of_fun bool_types) psi)
           ((Shows_Literal.showsl_lit "lex-leq does not encode valid formula" .
              Shows_Literal.showsl_literal "\n") .
             Term_Rewriting.showsl_formulaa psi))
         (\ _ ->
           Term_Rewriting.check_valid_formula showsl_atom logic_checker
             normalize_lit (hinter info tr)
             (Term_Rewriting.Disjunction
               [psi, Term_Rewriting.form_not
                       (Term_Rewriting.map_formula
                         (Term_Rewriting.rename_vars_exp Term_Rewriting.Pre)
                         (Term_Rewriting.assertion_of pi l)),
                 Term_Rewriting.form_not phi]));

lex_processor ::
  forall a b c d e f.
    (Eq a, Shows_Literal.Showl a, Arith.Ceq b, Arith.Ccompare b, Eq b,
      Shows_Literal.Showl b, Eq c, Shows_Literal.Showl c, HOL.Default d,
      Shows_Literal.Showl d, Arith.Ccompare e, Eq e, Shows_Literal.Showl e,
      Arith.Ceq f, Arith.Ccompare f, Eq f, Arith.Set_impl f,
      Shows_Literal.Showl f) => (a -> ([b], b)) ->
                                  Arith.Set b ->
                                    (Term_Rewriting.Term a
                                       (Term_Rewriting.Trans_var c, b) ->
                                      String -> String) ->
                                      (d ->
Term_Rewriting.Formula
  (Term_Rewriting.Term a (Term_Rewriting.Trans_var c, b)) ->
  Sum_Type.Sum (String -> String) ()) ->
(Bool ->
  Term_Rewriting.Term a (Term_Rewriting.Trans_var c, b) ->
    Term_Rewriting.Formula
      (Term_Rewriting.Term a (Term_Rewriting.Trans_var c, b))) ->
  b -> (Term_Rewriting.Term a (Term_Rewriting.Trans_var c, b) ->
         Term_Rewriting.Term a (Term_Rewriting.Trans_var c, b) ->
           Term_Rewriting.Formula
             (Term_Rewriting.Term a (Term_Rewriting.Trans_var c, b))) ->
         (Term_Rewriting.Term a (Term_Rewriting.Trans_var c, b) ->
           Term_Rewriting.Term a (Term_Rewriting.Trans_var c, b) ->
             Term_Rewriting.Formula
               (Term_Rewriting.Term a (Term_Rewriting.Trans_var c, b))) ->
           (Term_Rewriting.Term a (Term_Rewriting.Trans_var c, b) -> Bool) ->
             Transition_removal_info [Term_Rewriting.Term a (c, b)] b e f d ->
               Term_Rewriting.Lts_impl a c b (Term_Rewriting.Sharp e) f ->
                 Sum_Type.Sum (String -> String)
                   (Term_Rewriting.Lts_impl a c b (Term_Rewriting.Sharp e) f);
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
                  (Term_Rewriting.has_type type_of_fun e dom_type)
                  (Shows_Literal.showsl_lit "Unexpected type of expression:\n" .
                    Term_Rewriting.showsl_terma e))
              (rank info l))
            (\ x -> Sum_Type.Inl (snd x)))
        (Term_Rewriting.nodes_lts_impl pi))
      (\ x -> Sum_Type.Inl (snd x)))
    (\ _ ->
      Error_Monad.bind
        (Error_Monad.catch_error
          (Error_Monad.forallM
            (\ e ->
              Check_Monad.check (Term_Rewriting.has_type type_of_fun e dom_type)
                (Shows_Literal.showsl_lit "Unexpected type of bound: " .
                  Term_Rewriting.showsl_terma e))
            (bound_exp info))
          (\ x -> Sum_Type.Inl (snd x)))
        (\ _ ->
          Error_Monad.bind
            (Error_Monad.catch_error
              (Error_Monad.forallM
                (\ e ->
                  Check_Monad.check (is_constant e)
                    (Shows_Literal.showsl_lit "Non-constant bound: " .
                      Term_Rewriting.showsl_terma e))
                (map (Term_Rewriting.rename_vars_exp Term_Rewriting.Pre)
                  (bound_exp info)))
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
