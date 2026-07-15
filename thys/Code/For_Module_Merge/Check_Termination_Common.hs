{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Check_Termination_Common(Generic_assm_proof(..), missing, toomuch)
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
import qualified Shows_Literal;
import qualified Forbidden_Patterns;
import qualified Complexity;
import qualified Subterm_and_Context;
import qualified Str;
import qualified Term;
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

data Generic_assm_proof a b c d e f g h =
  SN_assm_proof
    (Bool,
      ([Term.Term (Labelings.Lab a b) c],
        ([(Term.Term (Labelings.Lab a b) c, Term.Term (Labelings.Lab a b) c)],
          [(Term.Term (Labelings.Lab a b) c,
             Term.Term (Labelings.Lab a b) c)])))
    d
  | Finite_assm_proof
      (Bool,
        (Bool,
          ([(Term.Term (Labelings.Lab a b) c, Term.Term (Labelings.Lab a b) c)],
            ([(Term.Term (Labelings.Lab a b) c,
                Term.Term (Labelings.Lab a b) c)],
              ([Term.Term (Labelings.Lab a b) c],
                ([(Term.Term (Labelings.Lab a b) c,
                    Term.Term (Labelings.Lab a b) c)],
                  [(Term.Term (Labelings.Lab a b) c,
                     Term.Term (Labelings.Lab a b) c)]))))))
      e
  | SN_FP_assm_proof
      ([(Subterm_and_Context.Actxt (Labelings.Lab a b)
           (Term.Term (Labelings.Lab a b) c),
          (Term.Term (Labelings.Lab a b) c, Forbidden_Patterns.Location))],
        [(Term.Term (Labelings.Lab a b) c, Term.Term (Labelings.Lab a b) c)])
      f
  | Not_SN_assm_proof
      (Bool,
        ([Term.Term (Labelings.Lab a b) c],
          [(Term.Term (Labelings.Lab a b) c, Term.Term (Labelings.Lab a b) c)]))
      d
  | Infinite_assm_proof
      (Bool,
        (Bool,
          ([(Term.Term (Labelings.Lab a b) c, Term.Term (Labelings.Lab a b) c)],
            ([(Term.Term (Labelings.Lab a b) c,
                Term.Term (Labelings.Lab a b) c)],
              ([Term.Term (Labelings.Lab a b) c],
                ([(Term.Term (Labelings.Lab a b) c,
                    Term.Term (Labelings.Lab a b) c)],
                  [(Term.Term (Labelings.Lab a b) c,
                     Term.Term (Labelings.Lab a b) c)]))))))
      e
  | Not_RelSN_assm_proof
      (Bool,
        ([Term.Term (Labelings.Lab a b) c],
          ([(Term.Term (Labelings.Lab a b) c, Term.Term (Labelings.Lab a b) c)],
            [(Term.Term (Labelings.Lab a b) c,
               Term.Term (Labelings.Lab a b) c)])))
      f
  | Not_SN_FP_assm_proof
      ([(Subterm_and_Context.Actxt (Labelings.Lab a b)
           (Term.Term (Labelings.Lab a b) c),
          (Term.Term (Labelings.Lab a b) c, Forbidden_Patterns.Location))],
        [(Term.Term (Labelings.Lab a b) c, Term.Term (Labelings.Lab a b) c)])
      g
  | Complexity_assm_proof
      ([Term.Term (Labelings.Lab a b) c],
        ([(Term.Term (Labelings.Lab a b) c, Term.Term (Labelings.Lab a b) c)],
          ([(Term.Term (Labelings.Lab a b) c, Term.Term (Labelings.Lab a b) c)],
            (Complexity.Complexity_measure (Labelings.Lab a b) c,
              Complexity.Complexity_class))))
      d
  | Unknown_assm_proof [Str.Char] h;

missing :: String -> (String -> String) -> String -> String;
missing s x =
  (((Shows_Literal.showsl_literal "the " . Shows_Literal.showsl_literal s) .
     Shows_Literal.showsl_literal " ") .
    x) .
    Shows_Literal.showsl_literal " is missing";

toomuch :: String -> (String -> String) -> String -> String;
toomuch s x =
  ((Shows_Literal.showsl_lit "superfluous " . Shows_Literal.showsl_lit s) .
    Shows_Literal.showsl_lit " ") .
    x;

}
