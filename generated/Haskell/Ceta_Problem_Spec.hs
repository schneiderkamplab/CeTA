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
import qualified HOL;
import qualified Ordered_Completion_Impl;
import qualified Tree_Automata_Impl;
import qualified Term_Rewriting;
import qualified Arith;

data Fp_strategy a b = Outermost
  | Context_Sensitive [((a, Arith.Nat), [Arith.Nat])]
  | Forbidden_Patterns
      [(Term_Rewriting.Actxt a (Term_Rewriting.Term a b),
         (Term_Rewriting.Term a b, Term_Rewriting.Location))];

data Strategy a b = No_Strategy | Innermost Bool
  | Innermost_Q Bool [Term_Rewriting.Term a b];

data Input a b =
  DP_input Bool [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]
    (Strategy a b) [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]
  | Relative_DP_input Bool Bool
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]
      [Term_Rewriting.Term a b]
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]
  | CSR_Improved_DP_input Bool a [((a, Arith.Nat), [Arith.Nat])]
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]
  | Inn_TRS_input (Strategy a b)
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]
  | FP_TRS_input (Fp_strategy a b)
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]
  | AC_input [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] [a] [a]
  | LTS_input
      (Term_Rewriting.Lts_impl Term_Rewriting.Sig b Term_Rewriting.Ty
        [Arith.Char] [Arith.Char])
  | LTS_safety_input
      (Term_Rewriting.Lts_impl Term_Rewriting.Sig b Term_Rewriting.Ty
        [Arith.Char] [Arith.Char])
      [[Arith.Char]]
  | CTRS_input
      [((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
         [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)])]
  | EQ_input [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]
  | EQ_RO_input [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]
      (Ordered_Completion_Impl.Reduction_order_input a)
  | EQ_reasoning_input [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]
      (Term_Rewriting.Term a b, Term_Rewriting.Term a b)
  | TA_input (Tree_Automata_Impl.Tree_automaton [Arith.Char] a)
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]
  | Infeasibility_input
      [((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
         [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)])]
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]
  | Single_TRS_input [(a, Arith.Nat)]
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]
  | Two_TRS_input [(a, Arith.Nat)]
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]
  | Unknown_input [Arith.Char];

data Answer a b = Decision Bool | Upperbound_Poly Arith.Nat
  | Completed_System [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]
  | Order_Completed_System [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];

data ComplexityMeasure a b = Derivational (Maybe [(a, Arith.Nat)])
  | Runtime (Maybe ([(a, Arith.Nat)], [(a, Arith.Nat)]));

data Property a b = Termination | Confluence | Commutation | Completion | Safety
  | Entailment | Complexity (ComplexityMeasure a b) | Closed_Under_Rewriting
  | Infeasibility | Unknown_Property;

strategy_to_Q ::
  forall a b.
    (Eq a,
      Eq b) => Strategy a b ->
                 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                   [Term_Rewriting.Term a b];
strategy_to_Q No_Strategy uu = [];
strategy_to_Q (Innermost uv) r = Arith.remdups (map fst r);
strategy_to_Q (Innermost_Q uw q) ux = q;

input_to_string :: forall a b. Input a b -> String;
input_to_string (DP_input uu uv uw ux) = "dependency pair problem";
input_to_string (Relative_DP_input uy uz va vb vc vd ve) =
  "relative dependency pair problem";
input_to_string (CSR_Improved_DP_input vf vg vh vi vj) =
  "minimal improved CSR dependency pair problem";
input_to_string (Inn_TRS_input vk vl vm) =
  "(innermost) (relative) rewrite system(s)";
input_to_string (FP_TRS_input vn vo) =
  "rewrite system with evaluation strategy";
input_to_string (AC_input vp vq vr) = "AC rewrite system";
input_to_string (LTS_input vs) = "integer transition system";
input_to_string (LTS_safety_input vt vu) =
  "integer transition system with potential error states";
input_to_string (CTRS_input vv) = "conditional TRS";
input_to_string (EQ_input vw) = "equational system";
input_to_string (EQ_RO_input vx vy) = "equational system and reduction order";
input_to_string (EQ_reasoning_input vz wa) =
  "equational system and explicit equation";
input_to_string (TA_input wb wc) = "tree automation and rewrite system";
input_to_string (Infeasibility_input wd we) =
  "conditional TRS and list of term pairs";
input_to_string (Two_TRS_input wf wg wh) = "two rewrite systems with signature";
input_to_string (Single_TRS_input wi wj) = "rewrite system with signature";
input_to_string (Unknown_input wk) = "unspecified input";

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
    (Eq a) => [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                  ComplexityMeasure a c ->
                    Term_Rewriting.Complexity_measure a d;
complexity_measure_of r s cm =
  let {
    f = Term_Rewriting.funas_trs_list (r ++ s);
    d = Term_Rewriting.defined_list (r ++ s);
    c = filter (\ fa -> not (Arith.membera d fa)) f;
  } in (case cm of {
         Derivational Nothing -> Term_Rewriting.Derivational_Complexity f;
         Derivational (Just a) -> Term_Rewriting.Derivational_Complexity a;
         Runtime Nothing -> Term_Rewriting.Runtime_Complexity c d;
         Runtime (Just (a, b)) -> Term_Rewriting.Runtime_Complexity a b;
       });

fp_strategy_to_fp_impl ::
  forall a b.
    (Eq a) => Fp_strategy a [Arith.Char] ->
                [(Term_Rewriting.Term a [Arith.Char], b)] ->
                  [(Term_Rewriting.Actxt a (Term_Rewriting.Term a [Arith.Char]),
                     (Term_Rewriting.Term a [Arith.Char],
                       Term_Rewriting.Location))];
fp_strategy_to_fp_impl strat r =
  (case strat of {
    Outermost -> Outermost_Forbidden_Patterns.o_to_fp_impl (map fst r);
    Context_Sensitive a -> Context_Sensitive_Impl.mu_to_fp_impl a;
    Forbidden_Patterns fp -> fp;
  });

}
