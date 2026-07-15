{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module LTS_Safety_Prover(Safety_proof(..), check_safety) where {

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
import qualified Invariants_To_Assertions;
import qualified FOR_Preliminaries;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Term_Rewriting;
import qualified Mapping;
import qualified Shows_Literal;
import qualified Arith;
import qualified HOL;
import qualified Invariant_Proof_Checkers;

data Safety_proof a b c d e f g = Trivial
  | Invariant_Assertion (Invariant_Proof_Checkers.Invariant_proof a b c d e f g)
      (Safety_proof a b c d e f g);

safe_by_assertion_checker ::
  forall a b c d e f.
    (Eq a, Eq b, Shows_Literal.Showl b, Eq c, HOL.Default d,
      Shows_Literal.Showl d, Arith.Ccompare e, Eq e, Mapping.Mapping_impl e,
      Shows_Literal.Showl e) => (Term_Rewriting.Term a (b, c) ->
                                  String -> String) ->
                                  (d -> Term_Rewriting.Formula
  (Term_Rewriting.Term a (b, c)) ->
  Sum_Type.Sum (String -> String) ()) ->
                                    (Bool ->
                                      Term_Rewriting.Term a (b, c) ->
Term_Rewriting.Formula (Term_Rewriting.Term a (b, c))) ->
                                      Term_Rewriting.Lts_impl a b c e f ->
[e] -> Sum_Type.Sum (String -> String) ();
safe_by_assertion_checker showsl_atom logic_checker normalize_lit pi err =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ l ->
        Error_Monad.catch_error
          (Term_Rewriting.check_valid_formula showsl_atom logic_checker
            normalize_lit HOL.defaulta
            (Term_Rewriting.form_not (Term_Rewriting.assertion_of pi l)))
          (\ _ ->
            Sum_Type.Inl
              ((Shows_Literal.showsl_lit
                  "could not deduce from assertion that " .
                 Shows_Literal.showsl l) .
                Shows_Literal.showsl_lit " is unreachable")))
      err)
    (\ x -> Sum_Type.Inl (snd x));

check_safety_proof ::
  forall a b c d e f g.
    (Arith.Ccompare a, Eq a, Shows_Literal.Showl a, Arith.Ceq b,
      Arith.Ccompare b, Eq b, Shows_Literal.Showl b, HOL.Default c,
      Shows_Literal.Showl c, Arith.Ccompare d, Eq d, Shows_Literal.Showl d,
      Arith.Cenum e, Arith.Ceq e, Arith.Ccompare e, Eq e,
      Mapping.Mapping_impl e, Arith.Set_impl e, Shows_Literal.Showl e,
      Arith.Ceq f, Arith.Ccompare f, Eq f, Mapping.Mapping_impl f,
      Arith.Set_impl f, Shows_Literal.Showl f, Arith.Ccompare g, Eq g,
      Mapping.Mapping_impl g,
      Shows_Literal.Showl g) => (a -> ([b], b)) ->
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
        Term_Rewriting.Lts_impl a d b e f ->
          [e] ->
            Safety_proof a d b e g f c -> Sum_Type.Sum (String -> String) ();
check_safety_proof type_of_fun bool_types tc tc2 sa sa2 ne ne2 pi err Trivial =
  FOR_Preliminaries.debug id "Unsatisfiable Error states"
    (safe_by_assertion_checker sa tc ne pi err);
check_safety_proof type_of_fun bool_types tc tc2 sa sa2 ne ne2 pi err
  (Invariant_Assertion inv_prf inner) =
  FOR_Preliminaries.debug id "Add Invariants"
    (Error_Monad.bind
      (Invariant_Proof_Checkers.invariant_proof_checker type_of_fun bool_types
        tc tc2 sa sa2 ne ne2 pi inv_prf)
      (\ i ->
        Error_Monad.bind (Invariants_To_Assertions.fix_invariants pi i)
          (\ qi ->
            check_safety_proof type_of_fun bool_types tc tc2 sa sa2 ne ne2 qi
              err inner)));

check_safety ::
  forall a b c d e f g.
    (Arith.Ccompare a, Eq a, Shows_Literal.Showl a, Arith.Ceq b,
      Arith.Ccompare b, Eq b, Shows_Literal.Showl b, HOL.Default c,
      Shows_Literal.Showl c, Arith.Ccompare d, Eq d, Shows_Literal.Showl d,
      Arith.Cenum e, Arith.Ceq e, Arith.Ccompare e, Eq e,
      Mapping.Mapping_impl e, Arith.Set_impl e, Shows_Literal.Showl e,
      Arith.Ceq f, Arith.Ccompare f, Eq f, Mapping.Mapping_impl f,
      Arith.Set_impl f, Shows_Literal.Showl f, Arith.Ccompare g, Eq g,
      Mapping.Mapping_impl g,
      Shows_Literal.Showl g) => (a -> ([b], b)) ->
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
        Term_Rewriting.Lts_impl a d b e f ->
          [e] ->
            Safety_proof a d b e g f c -> Sum_Type.Sum (String -> String) ();
check_safety type_of_fun bool_types tc tc2 sa sa2 ne ne2 pi err prf =
  Error_Monad.bind
    (FOR_Preliminaries.debug id "init - Check well-formedness"
      (Term_Rewriting.check_lts_impl type_of_fun bool_types pi))
    (\ _ ->
      check_safety_proof type_of_fun bool_types tc tc2 sa sa2 ne ne2 pi err
        prf);

}
