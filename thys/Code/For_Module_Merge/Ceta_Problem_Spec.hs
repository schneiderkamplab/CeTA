{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Ceta_Problem_Spec(Fp_strategy(..), Strategy(..), Input(..), Answer(..),
                     ComplexityMeasure(..), Property(..), strategy_to_Q,
                     input_to_string, default_nfs_flag, strategy_to_nfs,
                     answer_to_string, property_to_string,
                     complexity_measure_of, fp_strategy_to_fp_impl)
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
import qualified Outermost_Forbidden_Patterns;
import qualified Context_Sensitive_Impl;
import qualified Product_Type;
import qualified Option;
import qualified Trs_Impl;
import qualified Trs;
import qualified HOL;
import qualified Complexity;
import qualified List;
import qualified Forbidden_Patterns;
import qualified Subterm_and_Context;
import qualified Ordered_Completion_Impl;
import qualified Tree_Automata_Impl;
import qualified Integer_Arithmetic;
import qualified LTS;
import qualified Str;
import qualified Term;
import qualified Arith;

data Fp_strategy a b = Outermost
  | Context_Sensitive [((a, Arith.Nat), [Arith.Nat])]
  | Forbidden_Patterns
      [(Subterm_and_Context.Actxt a (Term.Term a b),
         (Term.Term a b, Forbidden_Patterns.Location))];

data Strategy a b = No_Strategy | Innermost Bool
  | Innermost_Q Bool [Term.Term a b];

data Input a b =
  DP_input Bool [(Term.Term a b, Term.Term a b)] (Strategy a b)
    [(Term.Term a b, Term.Term a b)]
  | Inn_TRS_input (Strategy a b) [(Term.Term a b, Term.Term a b)]
      [(Term.Term a b, Term.Term a b)]
  | FP_TRS_input (Fp_strategy a b) [(Term.Term a b, Term.Term a b)]
  | AC_input [(Term.Term a b, Term.Term a b)] [a] [a]
  | LTS_input
      (LTS.Lts_impl Integer_Arithmetic.Sig b Integer_Arithmetic.Ty [Str.Char]
        [Str.Char])
  | LTS_safety_input
      (LTS.Lts_impl Integer_Arithmetic.Sig b Integer_Arithmetic.Ty [Str.Char]
        [Str.Char])
      [[Str.Char]]
  | CTRS_input
      [((Term.Term a b, Term.Term a b), [(Term.Term a b, Term.Term a b)])]
  | EQ_input [(Term.Term a b, Term.Term a b)]
  | EQ_RO_input [(Term.Term a b, Term.Term a b)]
      (Ordered_Completion_Impl.Reduction_order_input a)
  | EQ_reasoning_input [(Term.Term a b, Term.Term a b)]
      (Term.Term a b, Term.Term a b)
  | TA_input (Tree_Automata_Impl.Tree_automaton [Str.Char] a)
      [(Term.Term a b, Term.Term a b)]
  | Infeasibility_input
      [((Term.Term a b, Term.Term a b), [(Term.Term a b, Term.Term a b)])]
      [(Term.Term a b, Term.Term a b)]
  | Single_TRS_input [(a, Arith.Nat)] [(Term.Term a b, Term.Term a b)]
  | Two_TRS_input [(a, Arith.Nat)] [(Term.Term a b, Term.Term a b)]
      [(Term.Term a b, Term.Term a b)]
  | Unknown_input [Str.Char];

data Answer a b = Decision Bool | Upperbound_Poly Arith.Nat
  | Completed_System [(Term.Term a b, Term.Term a b)]
  | Order_Completed_System [(Term.Term a b, Term.Term a b)]
      [(Term.Term a b, Term.Term a b)];

data ComplexityMeasure a b = Derivational (Maybe [(a, Arith.Nat)])
  | Runtime (Maybe ([(a, Arith.Nat)], [(a, Arith.Nat)]));

data Property a b = Termination | Confluence | Commutation | Completion | Safety
  | Entailment | Complexity (ComplexityMeasure a b) | Closed_Under_Rewriting
  | Infeasibility | Unknown_Property;

strategy_to_Q ::
  forall a b.
    (Eq a,
      Eq b) => Strategy a b ->
                 [(Term.Term a b, Term.Term a b)] -> [Term.Term a b];
strategy_to_Q No_Strategy uu = [];
strategy_to_Q (Innermost uv) r = List.remdups (map fst r);
strategy_to_Q (Innermost_Q uw q) ux = q;

input_to_string :: forall a b. Input a b -> String;
input_to_string (DP_input uu uv uw ux) = "dependency pair problem";
input_to_string (Inn_TRS_input uy uz va) =
  "(innermost) (relative) rewrite system(s)";
input_to_string (FP_TRS_input vb vc) =
  "rewrite system with evaluation strategy";
input_to_string (AC_input vd ve vf) = "AC rewrite system";
input_to_string (LTS_input vg) = "integer transition system";
input_to_string (LTS_safety_input vh vi) =
  "integer transition system with potential error states";
input_to_string (CTRS_input vj) = "conditional TRS";
input_to_string (EQ_input vk) = "equational system";
input_to_string (EQ_RO_input vl vm) = "equational system and reduction order";
input_to_string (EQ_reasoning_input vn vo) =
  "equational system and explicit equation";
input_to_string (TA_input vp vq) = "tree automation and rewrite system";
input_to_string (Infeasibility_input vr vs) =
  "conditional TRS and list of term pairs";
input_to_string (Two_TRS_input vt vu vv) = "two rewrite systems with signature";
input_to_string (Single_TRS_input vw vx) = "rewrite system with signature";
input_to_string (Unknown_input vy) = "unspecified input";

default_nfs_flag :: Bool;
default_nfs_flag = False;

strategy_to_nfs :: forall a b. Strategy a b -> Bool;
strategy_to_nfs No_Strategy = default_nfs_flag;
strategy_to_nfs (Innermost nfs) = nfs;
strategy_to_nfs (Innermost_Q nfs uu) = nfs;

answer_to_string :: forall a b. Answer a b -> String;
answer_to_string (Decision b) = (if b then "YES" else "NO");
answer_to_string (Upperbound_Poly uu) = "O(n^something)";
answer_to_string (Completed_System uv) = "some complete TRS";
answer_to_string (Order_Completed_System uw ux) =
  "some order-complete system (E,R)";

property_to_string :: forall a b. Property a b -> String;
property_to_string Termination = "termination";
property_to_string Confluence = "confluence";
property_to_string Commutation = "commutation";
property_to_string Completion = "completion";
property_to_string Safety = "safety";
property_to_string Entailment = "entailment";
property_to_string (Complexity uu) = "upperbound on complexity";
property_to_string Closed_Under_Rewriting = "closed under rewriting";
property_to_string Infeasibility = "infeasibility";
property_to_string Unknown_Property = "unknown property";

complexity_measure_of ::
  forall a b c d.
    (Eq a) => [(Term.Term a b, Term.Term a b)] ->
                [(Term.Term a b, Term.Term a b)] ->
                  ComplexityMeasure a c -> Complexity.Complexity_measure a d;
complexity_measure_of r s cm =
  let {
    f = Trs.funas_trs_list (r ++ s);
    d = Trs_Impl.defined_list (r ++ s);
    c = filter (\ fa -> not (List.member d fa)) f;
  } in (case cm of {
         Derivational Nothing -> Complexity.Derivational_Complexity f;
         Derivational (Just a) -> Complexity.Derivational_Complexity a;
         Runtime Nothing -> Complexity.Runtime_Complexity c d;
         Runtime (Just (a, b)) -> Complexity.Runtime_Complexity a b;
       });

fp_strategy_to_fp_impl ::
  forall a b.
    (Eq a) => Fp_strategy a [Str.Char] ->
                [(Term.Term a [Str.Char], b)] ->
                  [(Subterm_and_Context.Actxt a (Term.Term a [Str.Char]),
                     (Term.Term a [Str.Char], Forbidden_Patterns.Location))];
fp_strategy_to_fp_impl strat r =
  (case strat of {
    Outermost -> Outermost_Forbidden_Patterns.o_to_fp_impl (map fst r);
    Context_Sensitive a -> Context_Sensitive_Impl.mu_to_fp_impl a;
    Forbidden_Patterns fp -> fp;
  });

}
