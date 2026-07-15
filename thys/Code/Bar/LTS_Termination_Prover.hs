{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  LTS_Termination_Prover(Cooperation_proof(..), Termination_proof(..), check)
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
import qualified Initial_Cooperation_Program;
import qualified Invariants_To_Assertions;
import qualified Call_Graph_Scc_Decomp;
import qualified Cut_Transition_Split;
import qualified Show_LTS;
import qualified Check_Monad;
import qualified FOR_Preliminaries;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Mapping;
import qualified Compare;
import qualified Shows_Literal;
import qualified HOL;
import qualified Fresh_Variable_Addition;
import qualified Transition_Removal;
import qualified Location_Addition;
import qualified Invariant_Proof_Checkers;
import qualified Arith;
import qualified Term_Rewriting;

data Cooperation_proof a b c d e f = Trivial
  | Invariants_Update
      (Invariant_Proof_Checkers.Invariant_proof a b c (Term_Rewriting.Sharp d)
        [Arith.Char] e f)
      (Cooperation_proof a b c d e f)
  | Location_Addition
      (Location_Addition.Location_addition_info a b c (Term_Rewriting.Sharp d)
        e)
      (Cooperation_proof a b c d e f)
  | Fresh_Variable_Addition
      (Fresh_Variable_Addition.Fresh_variable_addition_info a b c e)
      (Cooperation_proof a b c d e f)
  | Transition_Removal
      (Transition_Removal.Transition_removal_info [Term_Rewriting.Term a (b, c)]
        c d e f)
      (Cooperation_proof a b c d e f)
  | Scc_Decomp [([Term_Rewriting.Sharp d], Cooperation_proof a b c d e f)]
  | Cut_Transition_Split [([e], Cooperation_proof a b c d e f)];

data Termination_proof a b c d e f = Triviala
  | Via_Cooperation
      [([(Term_Rewriting.Sharp e,
           Term_Rewriting.Transition_rule a b c (Term_Rewriting.Sharp d))],
         Cooperation_proof a b c d (Term_Rewriting.Sharp e) f)]
  | Invariants_Update_LTS
      (Invariant_Proof_Checkers.Invariant_proof a b c d [Arith.Char] e f)
      (Termination_proof a b c d e f);

trivial_termination_checker ::
  forall a b c d e.
    (Shows_Literal.Showl d,
      Shows_Literal.Showl e) => (Term_Rewriting.Term a (b, c) ->
                                  String -> String) ->
                                  (Term_Rewriting.Term a
                                     (Term_Rewriting.Trans_var b, c) ->
                                    String -> String) ->
                                    Term_Rewriting.Lts_impl a b c
                                      (Term_Rewriting.Sharp d) e ->
                                      Sum_Type.Sum (String -> String) ();
trivial_termination_checker showsl_atom showsl_tatom p =
  Check_Monad.check
    (null (filter (\ tau -> Term_Rewriting.is_sharp (Term_Rewriting.source tau))
            (map snd (Term_Rewriting.transitions_impl p))))
    (Shows_Literal.showsl_lit "there are remaining sharp transitions in " .
      Show_LTS.showsl_lts showsl_atom showsl_tatom p);

check_cooperation_proof ::
  forall a b c d e f.
    (Arith.Ccompare a, Eq a, Shows_Literal.Showl a, Arith.Ceq b,
      Arith.Ccompare b, Eq b, Shows_Literal.Showl b, HOL.Default c,
      Shows_Literal.Showl c, Arith.Ccompare d, Eq d, Shows_Literal.Showl d,
      Arith.Ccompare e, Compare.Compare_order e, Eq e, Shows_Literal.Showl e,
      Arith.Ceq f, Arith.Ccompare f, Eq f, Mapping.Mapping_impl f,
      Arith.Set_impl f,
      Shows_Literal.Showl f) => (a -> ([b], b)) ->
                                  Arith.Set b ->
                                    (c -> Term_Rewriting.Formula
    (Term_Rewriting.Term a (d, b)) ->
    Sum_Type.Sum (String -> String) ()) ->
                                      (c ->
Term_Rewriting.Formula
  (Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b)) ->
  Sum_Type.Sum (String -> String) ()) ->
(Term_Rewriting.Term a (d, b) -> String -> String) ->
  (Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b) -> String -> String) ->
    (Bool ->
      Term_Rewriting.Term a (d, b) ->
        Term_Rewriting.Formula (Term_Rewriting.Term a (d, b))) ->
      (Bool ->
        Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b) ->
          Term_Rewriting.Formula
            (Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b))) ->
        b -> (Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b) ->
               Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b) ->
                 Term_Rewriting.Formula
                   (Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b))) ->
               (Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b) ->
                 Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b) ->
                   Term_Rewriting.Formula
                     (Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b))) ->
                 (Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b) ->
                   Bool) ->
                   (Term_Rewriting.Trans_var d ->
                     b -> Term_Rewriting.Formula
                            (Term_Rewriting.Term a
                              (Term_Rewriting.Trans_var d, b)) ->
                            Sum_Type.Sum (String -> String) ()) ->
                     (String -> String) ->
                       Term_Rewriting.Lts_impl a d b (Term_Rewriting.Sharp e)
                         f ->
                         Cooperation_proof a d b e f c ->
                           Sum_Type.Sum (String -> String) ();
check_cooperation_proof type_of_fun bool_types tc tc2 sa sa2 ne ne2 dom_type
  less_eq_formula less_formula is_constant definability_checker i cPi Trivial =
  FOR_Preliminaries.debug i "Trivial CP"
    (Error_Monad.catch_error (trivial_termination_checker sa sa2 cPi)
      (\ x ->
        Sum_Type.Inl
          ((i . Shows_Literal.showsl_lit
                  ": error in trivial cooperation termination checker\n") .
            x)));
check_cooperation_proof type_of_fun bool_types tc tc2 sa sa2 ne ne2 dom_type
  less_eq_formula less_formula is_constant definability_checker i cPi
  (Invariants_Update iproof cproof) =
  FOR_Preliminaries.debug i "Invariants_Update"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Invariant_Proof_Checkers.invariant_proof_checker type_of_fun bool_types
          tc tc2 sa sa2 ne ne2 cPi iproof)
        (\ x ->
          Sum_Type.Inl
            (((i . Shows_Literal.showsl_lit ": error in invariant update\n") .
               Show_LTS.showsl_cooperation_program cPi) .
              x)))
      (\ ia ->
        Error_Monad.bind (Invariants_To_Assertions.fix_invariants cPi ia)
          (\ q ->
            Error_Monad.catch_error
              (check_cooperation_proof type_of_fun bool_types tc tc2 sa sa2 ne
                ne2 dom_type less_eq_formula less_formula is_constant
                definability_checker (Shows_Literal.add_index i Arith.one_nat) q
                cproof)
              (\ x ->
                Sum_Type.Inl
                  ((i . Shows_Literal.showsl_lit
                          ": error below invariant update\n") .
                    x)))));
check_cooperation_proof type_of_fun bool_types tc tc2 sa sa2 ne ne2 dom_type
  less_eq_formula less_formula is_constant definability_checker i cPi
  (Transition_Removal info iproof) =
  FOR_Preliminaries.debug i "Transition Removal"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Transition_Removal.lex_processor type_of_fun bool_types sa2 tc2 ne2
          dom_type less_eq_formula less_formula is_constant info cPi)
        (\ x ->
          Sum_Type.Inl
            (((i . Shows_Literal.showsl_lit ": error in transition removal\n") .
               Show_LTS.showsl_cooperation_program cPi) .
              x)))
      (\ cPia ->
        Error_Monad.catch_error
          (check_cooperation_proof type_of_fun bool_types tc tc2 sa sa2 ne ne2
            dom_type less_eq_formula less_formula is_constant
            definability_checker (Shows_Literal.add_index i Arith.one_nat) cPia
            iproof)
          (\ x ->
            Sum_Type.Inl
              ((i . Shows_Literal.showsl_lit
                      ": error below transition removal\n") .
                x))));
check_cooperation_proof type_of_fun bool_types tc tc2 sa sa2 ne ne2 dom_type
  less_eq_formula less_formula is_constant definability_checker i cPi
  (Location_Addition info iproof) =
  FOR_Preliminaries.debug i "Location Addition"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Location_Addition.location_addition type_of_fun bool_types sa tc ne cPi
          info)
        (\ x ->
          Sum_Type.Inl
            (((i . Shows_Literal.showsl_literal
                     ": error in location addition\n") .
               Show_LTS.showsl_cooperation_program cPi) .
              x)))
      (\ q ->
        Error_Monad.catch_error
          (check_cooperation_proof type_of_fun bool_types tc tc2 sa sa2 ne ne2
            dom_type less_eq_formula less_formula is_constant
            definability_checker (Shows_Literal.add_index i Arith.one_nat) q
            iproof)
          (\ x ->
            Sum_Type.Inl
              ((i . Shows_Literal.showsl_literal
                      ": error below location addition\n") .
                x))));
check_cooperation_proof type_of_fun bool_types tc tc2 sa sa2 ne ne2 dom_type
  less_eq_formula less_formula is_constant definability_checker i cPi
  (Fresh_Variable_Addition info iproof) =
  FOR_Preliminaries.debug i "Fresh Variable Addition"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Fresh_Variable_Addition.fresh_variable_addition type_of_fun bool_types
          definability_checker sa2 cPi info)
        (\ x ->
          Sum_Type.Inl
            (((i . Shows_Literal.showsl_lit
                     ": error in fresh variable addition\n") .
               Show_LTS.showsl_cooperation_program cPi) .
              x)))
      (\ q ->
        Error_Monad.catch_error
          (check_cooperation_proof type_of_fun bool_types tc tc2 sa sa2 ne ne2
            dom_type less_eq_formula less_formula is_constant
            definability_checker (Shows_Literal.add_index i Arith.one_nat) q
            iproof)
          (\ x ->
            Sum_Type.Inl
              ((i . Shows_Literal.showsl_lit
                      ": error below fresh variable addition\n") .
                x))));
check_cooperation_proof type_of_fun bool_types tc tc2 sa sa2 ne ne2 dom_type
  less_eq_formula less_formula is_constant definability_checker i cPi
  (Scc_Decomp scc_proofs) =
  FOR_Preliminaries.debug i "SCC Decomp"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Call_Graph_Scc_Decomp.scc_decomposition cPi (map fst scc_proofs))
        (\ x ->
          Sum_Type.Inl
            (((i . Shows_Literal.showsl_lit ": error in Scc decomposition\n") .
               Show_LTS.showsl_cooperation_program cPi) .
              x)))
      (\ sccs ->
        Error_Monad.catch_error
          (Error_Monad.forallM_index
            (\ (scc, prof) j ->
              Error_Monad.catch_error
                (check_cooperation_proof type_of_fun bool_types tc tc2 sa sa2 ne
                  ne2 dom_type less_eq_formula less_formula is_constant
                  definability_checker (Shows_Literal.add_index i (Arith.suc j))
                  scc prof)
                (\ x ->
                  Sum_Type.Inl
                    ((i . Shows_Literal.showsl_lit
                            ": error below Scc decomposition\n") .
                      x)))
            (zip sccs (map snd scc_proofs)))
          (\ x -> Sum_Type.Inl (snd x))));
check_cooperation_proof type_of_fun bool_types tc tc2 sa sa2 ne ne2 dom_type
  less_eq_formula less_formula is_constant definability_checker i cPi
  (Cut_Transition_Split scc_proofs) =
  FOR_Preliminaries.debug i "Cut Transition Split"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Cut_Transition_Split.cut_transition_split
          (Cut_Transition_Split.Cut_Transition_Split_Info (map fst scc_proofs))
          cPi)
        (\ x ->
          Sum_Type.Inl
            (((i . Shows_Literal.showsl_lit
                     ": error in cut-transition split\n") .
               Show_LTS.showsl_cooperation_program cPi) .
              x)))
      (\ sccs ->
        Error_Monad.catch_error
          (Error_Monad.forallM_index
            (\ (scc, prof) j ->
              Error_Monad.catch_error
                (check_cooperation_proof type_of_fun bool_types tc tc2 sa sa2 ne
                  ne2 dom_type less_eq_formula less_formula is_constant
                  definability_checker (Shows_Literal.add_index i (Arith.suc j))
                  scc prof)
                (\ x ->
                  Sum_Type.Inl
                    ((i . Shows_Literal.showsl_lit
                            ": error below cut-transition split\n") .
                      x)))
            (zip sccs (map snd scc_proofs)))
          (\ x -> Sum_Type.Inl (snd x))));

check_termination_proof ::
  forall a b c d e f.
    (Arith.Ccompare a, Eq a, Shows_Literal.Showl a, Arith.Ceq b,
      Arith.Ccompare b, Eq b, Shows_Literal.Showl b, HOL.Default c,
      Shows_Literal.Showl c, Arith.Ccompare d, Eq d, Shows_Literal.Showl d,
      Arith.Cenum e, Arith.Ceq e, Arith.Ccompare e, Compare.Compare_order e,
      Eq e, Mapping.Mapping_impl e, Arith.Set_impl e, Shows_Literal.Showl e,
      Arith.Ceq f, Arith.Ccompare f, Eq f, Mapping.Mapping_impl f,
      Arith.Set_impl f,
      Shows_Literal.Showl f) => (a -> ([b], b)) ->
                                  Arith.Set b ->
                                    (c -> Term_Rewriting.Formula
    (Term_Rewriting.Term a (d, b)) ->
    Sum_Type.Sum (String -> String) ()) ->
                                      (c ->
Term_Rewriting.Formula
  (Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b)) ->
  Sum_Type.Sum (String -> String) ()) ->
(Term_Rewriting.Term a (d, b) -> String -> String) ->
  (Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b) -> String -> String) ->
    (Bool ->
      Term_Rewriting.Term a (d, b) ->
        Term_Rewriting.Formula (Term_Rewriting.Term a (d, b))) ->
      (Bool ->
        Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b) ->
          Term_Rewriting.Formula
            (Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b))) ->
        b -> (Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b) ->
               Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b) ->
                 Term_Rewriting.Formula
                   (Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b))) ->
               (Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b) ->
                 Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b) ->
                   Term_Rewriting.Formula
                     (Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b))) ->
                 (Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b) ->
                   Bool) ->
                   (Term_Rewriting.Trans_var d ->
                     b -> Term_Rewriting.Formula
                            (Term_Rewriting.Term a
                              (Term_Rewriting.Trans_var d, b)) ->
                            Sum_Type.Sum (String -> String) ()) ->
                     (String -> String) ->
                       Term_Rewriting.Lts_impl a d b e f ->
                         Termination_proof a d b e f c ->
                           Sum_Type.Sum (String -> String) ();
check_termination_proof type_of_fun bool_types tc tc2 sa sa2 ne ne2 dom_type
  less_eq_formula less_formula is_constant definability_checker i pi Triviala =
  FOR_Preliminaries.debug i "Trivial Termination"
    (Error_Monad.catch_error
      (Check_Monad.check (null (Term_Rewriting.transitions_impl pi))
        (Shows_Literal.showsl_lit
          "transition rules remains at trivial termination proof"))
      (\ x ->
        Sum_Type.Inl
          ((i . Shows_Literal.showsl_lit
                  ": error in trivial termination checker\n") .
            x)));
check_termination_proof type_of_fun bool_types tc tc2 sa sa2 ne ne2 dom_type
  less_eq_formula less_formula is_constant definability_checker i pi
  (Invariants_Update_LTS iproof cproof) =
  FOR_Preliminaries.debug i "Invariant Update"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Invariant_Proof_Checkers.invariant_proof_checker type_of_fun bool_types
          tc tc2 sa sa2 ne ne2 pi iproof)
        (\ x ->
          Sum_Type.Inl
            ((i . Shows_Literal.showsl_lit ": error in invariant update\n") .
              x)))
      (\ ia ->
        Error_Monad.bind (Invariants_To_Assertions.fix_invariants pi ia)
          (\ q ->
            Error_Monad.catch_error
              (check_termination_proof type_of_fun bool_types tc tc2 sa sa2 ne
                ne2 dom_type less_eq_formula less_formula is_constant
                definability_checker (Shows_Literal.add_index i Arith.one_nat) q
                cproof)
              (\ x ->
                Sum_Type.Inl
                  ((i . Shows_Literal.showsl_lit
                          ": error below invariant update\n") .
                    x)))));
check_termination_proof type_of_fun bool_types tc tc2 sa sa2 ne ne2 dom_type
  less_eq_formula less_formula is_constant definability_checker i pi
  (Via_Cooperation cp_proofs) =
  FOR_Preliminaries.debug i "Switch to Cooperation Program"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Initial_Cooperation_Program.create_initial_cp_prog type_of_fun
          bool_types sa tc ne pi (map fst cp_proofs))
        (\ x ->
          Sum_Type.Inl
            ((i . Shows_Literal.showsl_lit
                    ": error in creating initial cooperation program\n") .
              x)))
      (\ cPi ->
        Error_Monad.catch_error
          (Error_Monad.forallM_index
            (\ (r, prf) n ->
              Error_Monad.catch_error
                (check_cooperation_proof type_of_fun bool_types tc tc2 sa sa2 ne
                  ne2 dom_type less_eq_formula less_formula is_constant
                  definability_checker (Shows_Literal.add_index i n) r prf)
                (\ x ->
                  Sum_Type.Inl
                    ((i . Shows_Literal.showsl_lit
                            ": error below switching to initial cooperation program\n") .
                      x)))
            (zip cPi (map snd cp_proofs)))
          (\ x -> Sum_Type.Inl (snd x))));

check ::
  forall a b c d e f.
    (Arith.Ccompare a, Eq a, Shows_Literal.Showl a, Arith.Ceq b,
      Arith.Ccompare b, Eq b, Shows_Literal.Showl b, HOL.Default c,
      Shows_Literal.Showl c, Arith.Ccompare d, Eq d, Shows_Literal.Showl d,
      Arith.Cenum e, Arith.Ceq e, Arith.Ccompare e, Compare.Compare_order e,
      Eq e, Mapping.Mapping_impl e, Arith.Set_impl e, Shows_Literal.Showl e,
      Arith.Ceq f, Arith.Ccompare f, Eq f, Mapping.Mapping_impl f,
      Arith.Set_impl f,
      Shows_Literal.Showl f) => (a -> ([b], b)) ->
                                  Arith.Set b ->
                                    (c -> Term_Rewriting.Formula
    (Term_Rewriting.Term a (d, b)) ->
    Sum_Type.Sum (String -> String) ()) ->
                                      (c ->
Term_Rewriting.Formula
  (Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b)) ->
  Sum_Type.Sum (String -> String) ()) ->
(Term_Rewriting.Term a (d, b) -> String -> String) ->
  (Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b) -> String -> String) ->
    (Bool ->
      Term_Rewriting.Term a (d, b) ->
        Term_Rewriting.Formula (Term_Rewriting.Term a (d, b))) ->
      (Bool ->
        Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b) ->
          Term_Rewriting.Formula
            (Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b))) ->
        b -> (Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b) ->
               Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b) ->
                 Term_Rewriting.Formula
                   (Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b))) ->
               (Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b) ->
                 Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b) ->
                   Term_Rewriting.Formula
                     (Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b))) ->
                 (Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b) ->
                   Bool) ->
                   (Term_Rewriting.Trans_var d ->
                     b -> Term_Rewriting.Formula
                            (Term_Rewriting.Term a
                              (Term_Rewriting.Trans_var d, b)) ->
                            Sum_Type.Sum (String -> String) ()) ->
                     Term_Rewriting.Lts_impl a d b e f ->
                       Termination_proof a d b e f c ->
                         Sum_Type.Sum (String -> String) ();
check type_of_fun bool_types tc tc2 sa sa2 ne ne2 dom_type less_eq_formula
  less_formula is_constant definability_checker pi prf =
  Error_Monad.bind
    (FOR_Preliminaries.debug id "init - Check well-formedness"
      (Error_Monad.catch_error
        (Term_Rewriting.check_lts_impl type_of_fun bool_types pi)
        (\ x ->
          Sum_Type.Inl
            (Shows_Literal.showsl_lit "input LTS is not well-formed" . x))))
    (\ _ ->
      check_termination_proof type_of_fun bool_types tc tc2 sa sa2 ne ne2
        dom_type less_eq_formula less_formula is_constant definability_checker
        id pi prf);

}
