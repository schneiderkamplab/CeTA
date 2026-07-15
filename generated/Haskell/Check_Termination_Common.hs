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

}
