{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Check_Termination_Common(Problem, Assm(..), Generic_assm_proof(..), missing,
                            toomuch, assm_proof_to_problem)
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
import qualified Arith;
import qualified Term_Rewriting;
import qualified Labelings;
import qualified HOL;

default_list :: forall a. [a];
default_list = [];

instance HOL.Default [a] where {
  defaulta = default_list;
};

default_lab :: forall a b. (HOL.Default a) => Labelings.Lab a b;
default_lab = Labelings.UnLab HOL.defaulta;

instance (HOL.Default a) => HOL.Default (Labelings.Lab a b) where {
  defaulta = default_lab;
};

data Problem a b c =
  SN_TRS
    (Bool,
      ([Term_Rewriting.Term (Labelings.Lab a b) c],
        ([(Term_Rewriting.Term (Labelings.Lab a b) c,
            Term_Rewriting.Term (Labelings.Lab a b) c)],
          [(Term_Rewriting.Term (Labelings.Lab a b) c,
             Term_Rewriting.Term (Labelings.Lab a b) c)])))
  | SN_FP_TRS
      ([(Term_Rewriting.Actxt (Labelings.Lab a b)
           (Term_Rewriting.Term (Labelings.Lab a b) c),
          (Term_Rewriting.Term (Labelings.Lab a b) c,
            Term_Rewriting.Location))],
        [(Term_Rewriting.Term (Labelings.Lab a b) c,
           Term_Rewriting.Term (Labelings.Lab a b) c)])
  | Finite_DPP
      (Bool,
        (Bool,
          ([(Term_Rewriting.Term (Labelings.Lab a b) c,
              Term_Rewriting.Term (Labelings.Lab a b) c)],
            ([(Term_Rewriting.Term (Labelings.Lab a b) c,
                Term_Rewriting.Term (Labelings.Lab a b) c)],
              ([Term_Rewriting.Term (Labelings.Lab a b) c],
                ([(Term_Rewriting.Term (Labelings.Lab a b) c,
                    Term_Rewriting.Term (Labelings.Lab a b) c)],
                  [(Term_Rewriting.Term (Labelings.Lab a b) c,
                     Term_Rewriting.Term (Labelings.Lab a b) c)]))))))
  | Unknown_Problem [Arith.Char]
  | Not_SN_TRS
      (Bool,
        ([Term_Rewriting.Term (Labelings.Lab a b) c],
          [(Term_Rewriting.Term (Labelings.Lab a b) c,
             Term_Rewriting.Term (Labelings.Lab a b) c)]))
  | Not_RelSN_TRS
      (Bool,
        ([Term_Rewriting.Term (Labelings.Lab a b) c],
          ([(Term_Rewriting.Term (Labelings.Lab a b) c,
              Term_Rewriting.Term (Labelings.Lab a b) c)],
            [(Term_Rewriting.Term (Labelings.Lab a b) c,
               Term_Rewriting.Term (Labelings.Lab a b) c)])))
  | Infinite_DPP
      (Bool,
        (Bool,
          ([(Term_Rewriting.Term (Labelings.Lab a b) c,
              Term_Rewriting.Term (Labelings.Lab a b) c)],
            ([(Term_Rewriting.Term (Labelings.Lab a b) c,
                Term_Rewriting.Term (Labelings.Lab a b) c)],
              ([Term_Rewriting.Term (Labelings.Lab a b) c],
                ([(Term_Rewriting.Term (Labelings.Lab a b) c,
                    Term_Rewriting.Term (Labelings.Lab a b) c)],
                  [(Term_Rewriting.Term (Labelings.Lab a b) c,
                     Term_Rewriting.Term (Labelings.Lab a b) c)]))))))
  | Not_SN_FP_TRS
      ([(Term_Rewriting.Actxt (Labelings.Lab a b)
           (Term_Rewriting.Term (Labelings.Lab a b) c),
          (Term_Rewriting.Term (Labelings.Lab a b) c,
            Term_Rewriting.Location))],
        [(Term_Rewriting.Term (Labelings.Lab a b) c,
           Term_Rewriting.Term (Labelings.Lab a b) c)])
  | Complexity_Problem
      ([Term_Rewriting.Term (Labelings.Lab a b) c],
        ([(Term_Rewriting.Term (Labelings.Lab a b) c,
            Term_Rewriting.Term (Labelings.Lab a b) c)],
          ([(Term_Rewriting.Term (Labelings.Lab a b) c,
              Term_Rewriting.Term (Labelings.Lab a b) c)],
            (Term_Rewriting.Complexity_measure (Labelings.Lab a b) c,
              Term_Rewriting.Complexity_class))));

data Assm a b c =
  SN_assm [Problem a b c]
    (Bool,
      ([Term_Rewriting.Term (Labelings.Lab a b) c],
        ([(Term_Rewriting.Term (Labelings.Lab a b) c,
            Term_Rewriting.Term (Labelings.Lab a b) c)],
          [(Term_Rewriting.Term (Labelings.Lab a b) c,
             Term_Rewriting.Term (Labelings.Lab a b) c)])))
  | SN_FP_assm [Problem a b c]
      ([(Term_Rewriting.Actxt (Labelings.Lab a b)
           (Term_Rewriting.Term (Labelings.Lab a b) c),
          (Term_Rewriting.Term (Labelings.Lab a b) c,
            Term_Rewriting.Location))],
        [(Term_Rewriting.Term (Labelings.Lab a b) c,
           Term_Rewriting.Term (Labelings.Lab a b) c)])
  | Finite_assm [Problem a b c]
      (Bool,
        (Bool,
          ([(Term_Rewriting.Term (Labelings.Lab a b) c,
              Term_Rewriting.Term (Labelings.Lab a b) c)],
            ([(Term_Rewriting.Term (Labelings.Lab a b) c,
                Term_Rewriting.Term (Labelings.Lab a b) c)],
              ([Term_Rewriting.Term (Labelings.Lab a b) c],
                ([(Term_Rewriting.Term (Labelings.Lab a b) c,
                    Term_Rewriting.Term (Labelings.Lab a b) c)],
                  [(Term_Rewriting.Term (Labelings.Lab a b) c,
                     Term_Rewriting.Term (Labelings.Lab a b) c)]))))))
  | Unknown_assm [Problem a b c] [Arith.Char]
  | Not_SN_assm [Problem a b c]
      (Bool,
        ([Term_Rewriting.Term (Labelings.Lab a b) c],
          [(Term_Rewriting.Term (Labelings.Lab a b) c,
             Term_Rewriting.Term (Labelings.Lab a b) c)]))
  | Not_RelSN_assm [Problem a b c]
      (Bool,
        ([Term_Rewriting.Term (Labelings.Lab a b) c],
          ([(Term_Rewriting.Term (Labelings.Lab a b) c,
              Term_Rewriting.Term (Labelings.Lab a b) c)],
            [(Term_Rewriting.Term (Labelings.Lab a b) c,
               Term_Rewriting.Term (Labelings.Lab a b) c)])))
  | Not_SN_FP_assm [Problem a b c]
      ([(Term_Rewriting.Actxt (Labelings.Lab a b)
           (Term_Rewriting.Term (Labelings.Lab a b) c),
          (Term_Rewriting.Term (Labelings.Lab a b) c,
            Term_Rewriting.Location))],
        [(Term_Rewriting.Term (Labelings.Lab a b) c,
           Term_Rewriting.Term (Labelings.Lab a b) c)])
  | Infinite_assm [Problem a b c]
      (Bool,
        (Bool,
          ([(Term_Rewriting.Term (Labelings.Lab a b) c,
              Term_Rewriting.Term (Labelings.Lab a b) c)],
            ([(Term_Rewriting.Term (Labelings.Lab a b) c,
                Term_Rewriting.Term (Labelings.Lab a b) c)],
              ([Term_Rewriting.Term (Labelings.Lab a b) c],
                ([(Term_Rewriting.Term (Labelings.Lab a b) c,
                    Term_Rewriting.Term (Labelings.Lab a b) c)],
                  [(Term_Rewriting.Term (Labelings.Lab a b) c,
                     Term_Rewriting.Term (Labelings.Lab a b) c)]))))))
  | Complexity_assm [Problem a b c]
      ([Term_Rewriting.Term (Labelings.Lab a b) c],
        ([(Term_Rewriting.Term (Labelings.Lab a b) c,
            Term_Rewriting.Term (Labelings.Lab a b) c)],
          ([(Term_Rewriting.Term (Labelings.Lab a b) c,
              Term_Rewriting.Term (Labelings.Lab a b) c)],
            (Term_Rewriting.Complexity_measure (Labelings.Lab a b) c,
              Term_Rewriting.Complexity_class))));

data Generic_assm_proof a b c d e f g h =
  SN_assm_proof
    (Bool,
      ([Term_Rewriting.Term (Labelings.Lab a b) c],
        ([(Term_Rewriting.Term (Labelings.Lab a b) c,
            Term_Rewriting.Term (Labelings.Lab a b) c)],
          [(Term_Rewriting.Term (Labelings.Lab a b) c,
             Term_Rewriting.Term (Labelings.Lab a b) c)])))
    d
  | Finite_assm_proof
      (Bool,
        (Bool,
          ([(Term_Rewriting.Term (Labelings.Lab a b) c,
              Term_Rewriting.Term (Labelings.Lab a b) c)],
            ([(Term_Rewriting.Term (Labelings.Lab a b) c,
                Term_Rewriting.Term (Labelings.Lab a b) c)],
              ([Term_Rewriting.Term (Labelings.Lab a b) c],
                ([(Term_Rewriting.Term (Labelings.Lab a b) c,
                    Term_Rewriting.Term (Labelings.Lab a b) c)],
                  [(Term_Rewriting.Term (Labelings.Lab a b) c,
                     Term_Rewriting.Term (Labelings.Lab a b) c)]))))))
      e
  | SN_FP_assm_proof
      ([(Term_Rewriting.Actxt (Labelings.Lab a b)
           (Term_Rewriting.Term (Labelings.Lab a b) c),
          (Term_Rewriting.Term (Labelings.Lab a b) c,
            Term_Rewriting.Location))],
        [(Term_Rewriting.Term (Labelings.Lab a b) c,
           Term_Rewriting.Term (Labelings.Lab a b) c)])
      f
  | Not_SN_assm_proof
      (Bool,
        ([Term_Rewriting.Term (Labelings.Lab a b) c],
          [(Term_Rewriting.Term (Labelings.Lab a b) c,
             Term_Rewriting.Term (Labelings.Lab a b) c)]))
      d
  | Infinite_assm_proof
      (Bool,
        (Bool,
          ([(Term_Rewriting.Term (Labelings.Lab a b) c,
              Term_Rewriting.Term (Labelings.Lab a b) c)],
            ([(Term_Rewriting.Term (Labelings.Lab a b) c,
                Term_Rewriting.Term (Labelings.Lab a b) c)],
              ([Term_Rewriting.Term (Labelings.Lab a b) c],
                ([(Term_Rewriting.Term (Labelings.Lab a b) c,
                    Term_Rewriting.Term (Labelings.Lab a b) c)],
                  [(Term_Rewriting.Term (Labelings.Lab a b) c,
                     Term_Rewriting.Term (Labelings.Lab a b) c)]))))))
      e
  | Not_RelSN_assm_proof
      (Bool,
        ([Term_Rewriting.Term (Labelings.Lab a b) c],
          ([(Term_Rewriting.Term (Labelings.Lab a b) c,
              Term_Rewriting.Term (Labelings.Lab a b) c)],
            [(Term_Rewriting.Term (Labelings.Lab a b) c,
               Term_Rewriting.Term (Labelings.Lab a b) c)])))
      f
  | Not_SN_FP_assm_proof
      ([(Term_Rewriting.Actxt (Labelings.Lab a b)
           (Term_Rewriting.Term (Labelings.Lab a b) c),
          (Term_Rewriting.Term (Labelings.Lab a b) c,
            Term_Rewriting.Location))],
        [(Term_Rewriting.Term (Labelings.Lab a b) c,
           Term_Rewriting.Term (Labelings.Lab a b) c)])
      g
  | Complexity_assm_proof
      ([Term_Rewriting.Term (Labelings.Lab a b) c],
        ([(Term_Rewriting.Term (Labelings.Lab a b) c,
            Term_Rewriting.Term (Labelings.Lab a b) c)],
          ([(Term_Rewriting.Term (Labelings.Lab a b) c,
              Term_Rewriting.Term (Labelings.Lab a b) c)],
            (Term_Rewriting.Complexity_measure (Labelings.Lab a b) c,
              Term_Rewriting.Complexity_class))))
      d
  | Unknown_assm_proof [Arith.Char] h;

missing :: String -> (String -> String) -> String -> String;
missing s x =
  (((Term_Rewriting.showsl_literal "the " . Term_Rewriting.showsl_literal s) .
     Term_Rewriting.showsl_literal " ") .
    x) .
    Term_Rewriting.showsl_literal " is missing";

toomuch :: String -> (String -> String) -> String -> String;
toomuch s x =
  ((Term_Rewriting.showsl_lit "superfluous " . Term_Rewriting.showsl_lit s) .
    Term_Rewriting.showsl_lit " ") .
    x;

assm_proof_to_problem ::
  forall a b c d e f g h. Generic_assm_proof a b c d e f g h -> Problem a b c;
assm_proof_to_problem (SN_assm_proof t prf) = SN_TRS t;
assm_proof_to_problem (SN_FP_assm_proof t prf) = SN_FP_TRS t;
assm_proof_to_problem (Finite_assm_proof d prf) = Finite_DPP d;
assm_proof_to_problem (Unknown_assm_proof p prf) = Unknown_Problem p;
assm_proof_to_problem (Not_SN_assm_proof t prf) = Not_SN_TRS t;
assm_proof_to_problem (Not_RelSN_assm_proof t prf) = Not_RelSN_TRS t;
assm_proof_to_problem (Infinite_assm_proof d prf) = Infinite_DPP d;
assm_proof_to_problem (Not_SN_FP_assm_proof t prf) = Not_SN_FP_TRS t;
assm_proof_to_problem (Complexity_assm_proof t prf) = Complexity_Problem t;

}
