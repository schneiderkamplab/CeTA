{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  CPF_Input_Parser(position, pos, plain_var, term, conditions, crule, rule,
                    symbols, cPFsignature, rules, state, final_states,
                    tree_automaton, ta_normal_lhs, kbo_input, replacement_map,
                    unknown_inputa, trs_input, dp_input, input, answer,
                    property, lookupTables, innermostLhss, strategy_to_fp)
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
import qualified Tree_Automata_Impl;
import qualified Outermost_Forbidden_Patterns;
import qualified Context_Sensitive_Impl;
import qualified Phantom_Type;
import qualified HOL;
import qualified Ordered_Completion_Impl;
import qualified Sum_Type;
import qualified LTS_Parser;
import qualified Ceta_Problem_Spec;
import qualified Mapping;
import qualified Term_Rewriting;
import qualified Strict_Sum;
import qualified Extended_Nat;
import qualified Xmlt;
import qualified Xml;
import qualified Arith;

list2position :: [Arith.Nat] -> [Arith.Nat];
list2position [] = [];
list2position (n : ns) = n : list2position ns;

position ::
  (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String) Arith.Nat;
position =
  Xmlt.xml_do "position"
    (Xmlt.xml_take_nat
      (\ n -> Xmlt.xml_return (Arith.minus_nat n Arith.one_nat)));

pos ::
  (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String) [Arith.Nat];
pos = Xmlt.xml_do "positionInTerm"
        (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
          position (\ lst -> Xmlt.xml_return (list2position lst)));

plain_var ::
  (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String) [Arith.Char];
plain_var = Xmlt.xml_text "var";

var ::
  forall a.
    (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
      Strict_Sum.Sum_bot (Xmlt.Xml_error String)
        (Term_Rewriting.Term a [Arith.Char]);
var = Xmlt.xml_change plain_var (Xmlt.xml_return . Term_Rewriting.Var);

term ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term a [Arith.Char]) ->
                                    (Xml.Xml,
                                      ([([Arith.Char], [Arith.Char])],
(Bool, ([String], [String])))) ->
                                      Strict_Sum.Sum_bot (Xmlt.Xml_error String)
(Term_Rewriting.Term a [Arith.Char]);
term xml2name termMap x =
  Xmlt.xml_or
    (Xmlt.xml_do "funapp"
      (Xmlt.xml_take xml2name
        (\ name ->
          Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
            (term xml2name termMap)
            (\ args -> Xmlt.xml_return (Term_Rewriting.Fun name args)))))
    (Xmlt.xml_or var
      (Xmlt.xml_change (Xmlt.xml_text "termIndex")
        (\ idx ->
          (case Mapping.lookup termMap idx of {
            Nothing ->
              Xmlt.xml_error
                (("term index " ++ Arith.implode idx) ++
                  " is unknown in term-index map");
            Just a -> Xmlt.xml_return a;
          }))))
    x;

conditions ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term a [Arith.Char]) ->
                                    String ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  [(Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char])];
conditions xml2name termMap tag =
  Xmlt.xml_do tag
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (Xmlt.xml_do "condition"
        (Xmlt.xml_take (term xml2name termMap)
          (\ l ->
            Xmlt.xml_take (term xml2name termMap)
              (\ r -> Xmlt.xml_return (l, r)))))
      Xmlt.xml_return);

crule ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term a [Arith.Char]) ->
                                    String ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  ((Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char]),
    [(Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char])]);
crule xml2name termMap tag =
  Xmlt.xml_do tag
    (Xmlt.xml_take (term xml2name termMap)
      (\ l ->
        Xmlt.xml_take (term xml2name termMap)
          (\ r ->
            Xmlt.xml_take_default [] (conditions xml2name termMap "conditions")
              (\ conds -> Xmlt.xml_return ((l, r), conds)))));

ctrs ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term a [Arith.Char]) ->
                                    (Xml.Xml,
                                      ([([Arith.Char], [Arith.Char])],
(Bool, ([String], [String])))) ->
                                      Strict_Sum.Sum_bot (Xmlt.Xml_error String)
[((Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char]),
   [(Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char])])];
ctrs xml2name termMap =
  Xmlt.xml_do "ctrs"
    (Xmlt.xml_take
      (Xmlt.xml_do "conditionType"
        (Xmlt.xml_take (Xmlt.xml_do "oriented" (Xmlt.xml_return ()))
          (\ _ -> Xmlt.xml_return ())))
      (\ _ ->
        Xmlt.xml_take
          (Xmlt.xml_do "rules"
            (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
              (crule xml2name termMap "rule") Xmlt.xml_return))
          Xmlt.xml_return));

full_rule ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term a [Arith.Char]) ->
                                    (Xml.Xml,
                                      ([([Arith.Char], [Arith.Char])],
(Bool, ([String], [String])))) ->
                                      Strict_Sum.Sum_bot (Xmlt.Xml_error String)
(Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char]);
full_rule xml2name termMap =
  Xmlt.xml_change (crule xml2name termMap "rule")
    (\ (lr, conds) ->
      (if null conds then Xmlt.xml_return lr
        else Xmlt.xml_error "conditional rule is not allowed here"));

rule ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term a [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term a [Arith.Char],
Term_Rewriting.Term a [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char]);
rule xml2name termMap ruleMap =
  Xmlt.xml_or
    (Xmlt.xml_change (Xmlt.xml_text "ruleIndex")
      (\ idx ->
        (case Mapping.lookup ruleMap idx of {
          Nothing ->
            Xmlt.xml_error
              (("rule index " ++ Arith.implode idx) ++
                " is unknown in rule map");
          Just a -> Xmlt.xml_return a;
        })))
    (full_rule xml2name termMap);

symbols ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  String ->
                                    (Xml.Xml,
                                      ([([Arith.Char], [Arith.Char])],
(Bool, ([String], [String])))) ->
                                      Strict_Sum.Sum_bot (Xmlt.Xml_error String)
[(a, Arith.Nat)];
symbols xml2name tagname =
  Xmlt.xml_do tagname
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (Xmlt.xml_do "symbol"
        (Xmlt.xml_take xml2name
          (\ a ->
            Xmlt.xml_take (Xmlt.xml_nat "arity")
              (\ b -> Xmlt.xml_return (a, b)))))
      Xmlt.xml_return);

cPFsignature ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  (Xml.Xml,
                                    ([([Arith.Char], [Arith.Char])],
                                      (Bool, ([String], [String])))) ->
                                    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                      [(a, Arith.Nat)];
cPFsignature xml2name = symbols xml2name "signature";

rules ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term a [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term a [Arith.Char],
Term_Rewriting.Term a [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  [(Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char])];
rules xml2name termMap ruleMap =
  Xmlt.xml_do "rules"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (rule xml2name termMap ruleMap) Xmlt.xml_return);

two_trs_with_signature_input ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term a [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term a [Arith.Char],
Term_Rewriting.Term a [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Ceta_Problem_Spec.Input a [Arith.Char]);
two_trs_with_signature_input xml2name termMap ruleMap =
  Xmlt.xml_do "twoTrsWithSignature"
    (Xmlt.xml_take (cPFsignature xml2name)
      (\ sig ->
        Xmlt.xml_take
          (Xmlt.xml_do "trs"
            (Xmlt.xml_take (rules xml2name termMap ruleMap) Xmlt.xml_return))
          (\ r ->
            Xmlt.xml_take
              (Xmlt.xml_do "trs"
                (Xmlt.xml_take (rules xml2name termMap ruleMap)
                  Xmlt.xml_return))
              (\ s ->
                Xmlt.xml_return (Ceta_Problem_Spec.Two_TRS_input sig r s)))));

equational_reasoning_input ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term a [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term a [Arith.Char],
Term_Rewriting.Term a [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Ceta_Problem_Spec.Input a [Arith.Char]);
equational_reasoning_input xml2name termMap ruleMap =
  Xmlt.xml_do "equationalReasoningInput"
    (Xmlt.xml_take
      (Xmlt.xml_do "equations"
        (Xmlt.xml_take (rules xml2name termMap ruleMap) Xmlt.xml_return))
      (\ eqs ->
        Xmlt.xml_take
          (Xmlt.xml_do "equation"
            (Xmlt.xml_take (term xml2name termMap)
              (\ a ->
                Xmlt.xml_take (term xml2name termMap)
                  (\ b -> Xmlt.xml_return (a, b)))))
          (\ goal ->
            Xmlt.xml_return (Ceta_Problem_Spec.EQ_reasoning_input eqs goal))));

trs_with_signature_input ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term a [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term a [Arith.Char],
Term_Rewriting.Term a [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Ceta_Problem_Spec.Input a [Arith.Char]);
trs_with_signature_input xml2name termMap ruleMap =
  Xmlt.xml_do "trsWithSignature"
    (Xmlt.xml_take (cPFsignature xml2name)
      (\ sig ->
        Xmlt.xml_take
          (Xmlt.xml_do "trs"
            (Xmlt.xml_take (rules xml2name termMap ruleMap) Xmlt.xml_return))
          (\ r -> Xmlt.xml_return (Ceta_Problem_Spec.Single_TRS_input sig r))));

state ::
  (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String) [Arith.Char];
state = Xmlt.xml_text "state";

final_states ::
  (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String) [[Arith.Char]];
final_states =
  Xmlt.xml_do "finalStates"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat state
      Xmlt.xml_return);

transition ::
  forall a b.
    ((Xml.Xml,
       ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
      Strict_Sum.Sum_bot (Xmlt.Xml_error String)
        (Sum_Type.Sum (a, [[Arith.Char]]) b)) ->
      (Xml.Xml,
        ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xmlt.Xml_error String)
          (Sum_Type.Sum (Term_Rewriting.Ta_rule [Arith.Char] a)
            (b, [Arith.Char]));
transition xml2lhs =
  Xmlt.xml_do "transition"
    (Xmlt.xml_take xml2lhs
      (\ lhs ->
        Xmlt.xml_take (Xmlt.xml_do "rhs" (Xmlt.xml_take state Xmlt.xml_return))
          (\ q ->
            Xmlt.xml_return
              (case lhs of {
                Sum_Type.Inl (f, qs) ->
                  Sum_Type.Inl (Term_Rewriting.TA_rule f qs q);
                Sum_Type.Inr qa -> Sum_Type.Inr (qa, q);
              }))));

transitions ::
  forall a b.
    ((Xml.Xml,
       ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
      Strict_Sum.Sum_bot (Xmlt.Xml_error String)
        (Sum_Type.Sum (a, [[Arith.Char]]) b)) ->
      (Xml.Xml,
        ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xmlt.Xml_error String)
          ([Term_Rewriting.Ta_rule [Arith.Char] a], [(b, [Arith.Char])]);
transitions xml2lhs =
  Xmlt.xml_do "transitions"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (transition xml2lhs)
      (\ rls ->
        (case Arith.partition (\ a -> (case a of {
Sum_Type.Inl _ -> True;
Sum_Type.Inr _ -> False;
                                      }))
                rls
          of {
          (rules, eps) -> let {
                            ruls = map (\ (Sum_Type.Inl r) -> r) rules;
                            ep = map (\ (Sum_Type.Inr e) -> e) eps;
                          } in Xmlt.xml_return (ruls, ep);
        })));

tree_automaton ::
  forall a.
    ((Xml.Xml,
       ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
      Strict_Sum.Sum_bot (Xmlt.Xml_error String)
        (Sum_Type.Sum (a, [[Arith.Char]]) [Arith.Char])) ->
      (Xml.Xml,
        ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xmlt.Xml_error String)
          (Tree_Automata_Impl.Tree_automaton [Arith.Char] a);
tree_automaton xml2lhs =
  Xmlt.xml_do "treeAutomaton"
    (Xmlt.xml_take final_states
      (\ f ->
        Xmlt.xml_take (transitions xml2lhs)
          (\ t_eps ->
            Xmlt.xml_return
              (Tree_Automata_Impl.Tree_Automaton f (fst t_eps) (snd t_eps)))));

ta_normal_lhs ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  (Xml.Xml,
                                    ([([Arith.Char], [Arith.Char])],
                                      (Bool, ([String], [String])))) ->
                                    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                      (Sum_Type.Sum (a, [[Arith.Char]])
[Arith.Char]);
ta_normal_lhs xml2name =
  Xmlt.xml_do "lhs"
    (Xmlt.xml_or (Xmlt.xml_take state (\ a -> Xmlt.xml_return (Sum_Type.Inr a)))
      (Xmlt.xml_take xml2name
        (\ a ->
          Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
            state (\ b -> Xmlt.xml_return (Sum_Type.Inl (a, b))))));

tree_automaton_and_trs ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term a [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term a [Arith.Char],
Term_Rewriting.Term a [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Ceta_Problem_Spec.Input a [Arith.Char]);
tree_automaton_and_trs xml2name termMap ruleMap =
  Xmlt.xml_do "treeAutomatonAndTrs"
    (Xmlt.xml_take (tree_automaton (ta_normal_lhs xml2name))
      (\ ta ->
        Xmlt.xml_take
          (Xmlt.xml_do "trs"
            (Xmlt.xml_take (rules xml2name termMap ruleMap) Xmlt.xml_return))
          (\ r -> Xmlt.xml_return (Ceta_Problem_Spec.TA_input ta r))));

precedence_weight ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  (Xml.Xml,
                                    ([([Arith.Char], [Arith.Char])],
                                      (Bool, ([String], [String])))) ->
                                    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                      (Arith.Nat ->
([((a, Arith.Nat), (Arith.Nat, (Arith.Nat, Maybe [Arith.Nat])))], Arith.Nat));
precedence_weight xml2name =
  Xmlt.xml_do "precedenceWeight"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (Xmlt.xml_do "precedenceWeightEntry"
        (Xmlt.xml_take xml2name
          (\ f ->
            Xmlt.xml_take (Xmlt.xml_nat "arity")
              (\ a ->
                Xmlt.xml_take (Xmlt.xml_nat "precedence")
                  (\ p ->
                    Xmlt.xml_take (Xmlt.xml_nat "weight")
                      (\ w ->
                        Xmlt.xml_take_optional
                          (Xmlt.xml_do "subtermCoefficientEntries"
                            (Xmlt.xml_take_many_sub [] Arith.zero_nat
                              Extended_Nat.Infinity_enat (Xmlt.xml_nat "entry")
                              Xmlt.xml_return))
                          (\ e -> Xmlt.xml_return ((f, a), (p, (w, e))))))))))
      (\ ret -> Xmlt.xml_return (\ a -> (ret, a))));

kbo_input ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  (Xml.Xml,
                                    ([([Arith.Char], [Arith.Char])],
                                      (Bool, ([String], [String])))) ->
                                    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                      (Ordered_Completion_Impl.Reduction_order_input
a);
kbo_input xml2name =
  Xmlt.xml_do "knuthBendixOrder"
    (Xmlt.xml_take (Xmlt.xml_nat "w0")
      (\ w0 ->
        Xmlt.xml_take (precedence_weight xml2name)
          (\ prw ->
            Xmlt.xml_return (Ordered_Completion_Impl.KBO_Input (prw w0)))));

equations_and_ro_input ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term a [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term a [Arith.Char],
Term_Rewriting.Term a [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Ceta_Problem_Spec.Input a [Arith.Char]);
equations_and_ro_input xml2name termMap ruleMap =
  Xmlt.xml_do "equationsAndRedorderInput"
    (Xmlt.xml_take
      (Xmlt.xml_do "equations"
        (Xmlt.xml_take (rules xml2name termMap ruleMap) Xmlt.xml_return))
      (\ es0 ->
        Xmlt.xml_take (kbo_input xml2name)
          (\ ro -> Xmlt.xml_return (Ceta_Problem_Spec.EQ_RO_input es0 ro))));

replacement_map ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  (Xml.Xml,
                                    ([([Arith.Char], [Arith.Char])],
                                      (Bool, ([String], [String])))) ->
                                    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                      [((a, Arith.Nat), [Arith.Nat])];
replacement_map xml2name =
  Xmlt.xml_do "contextSensitive"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (Xmlt.xml_do "replacementMapEntry"
        (Xmlt.xml_take xml2name
          (\ f ->
            Xmlt.xml_take (Xmlt.xml_nat "arity")
              (\ a ->
                Xmlt.xml_take_many_sub [] Arith.zero_nat
                  Extended_Nat.Infinity_enat position
                  (\ is -> Xmlt.xml_return ((f, a), is))))))
      Xmlt.xml_return);

csr_improved_dp_input ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term a [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term a [Arith.Char],
Term_Rewriting.Term a [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Ceta_Problem_Spec.Input a [Arith.Char]);
csr_improved_dp_input xml2name termMap ruleMap =
  Xmlt.xml_do "csrImprovedDpInput"
    (Xmlt.xml_take
      (Xmlt.xml_do "trs"
        (Xmlt.xml_take (rules xml2name termMap ruleMap) Xmlt.xml_return))
      (\ r ->
        Xmlt.xml_take
          (Xmlt.xml_do "dps"
            (Xmlt.xml_take (rules xml2name termMap ruleMap) Xmlt.xml_return))
          (\ p ->
            Xmlt.xml_take
              (Xmlt.xml_do "strategy"
                (Xmlt.xml_take (replacement_map xml2name) Xmlt.xml_return))
              (\ mu ->
                Xmlt.xml_take (Xmlt.xml_bool "minimal")
                  (\ m ->
                    Xmlt.xml_take
                      (Xmlt.xml_do "unhidingSymbol"
                        (Xmlt.xml_take xml2name Xmlt.xml_return))
                      (\ u ->
                        Xmlt.xml_return
                          (Ceta_Problem_Spec.CSR_Improved_DP_input m u mu p
                            r)))))));

infeasibility_input ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term a [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term a [Arith.Char],
Term_Rewriting.Term a [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Ceta_Problem_Spec.Input a [Arith.Char]);
infeasibility_input xml2name termMap ruleMap =
  Xmlt.xml_do "infeasibilityInput"
    (Xmlt.xml_take (ctrs xml2name termMap)
      (\ c ->
        Xmlt.xml_take
          (Xmlt.xml_do "infeasibilityQuery"
            (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
              (rule xml2name termMap ruleMap) Xmlt.xml_return))
          (\ r ->
            Xmlt.xml_return (Ceta_Problem_Spec.Infeasibility_input c r))));

nfs_def :: Maybe Bool -> Bool;
nfs_def nfs_opt = (case nfs_opt of {
                    Nothing -> Ceta_Problem_Spec.default_nfs_flag;
                    Just nfs -> nfs;
                  });

innermostLhssStrategy ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term a [Arith.Char]) ->
                                    (Xml.Xml,
                                      ([([Arith.Char], [Arith.Char])],
(Bool, ([String], [String])))) ->
                                      Strict_Sum.Sum_bot (Xmlt.Xml_error String)
(Ceta_Problem_Spec.Strategy a [Arith.Char]);
innermostLhssStrategy xml2name termMap =
  Xmlt.xml_do "innermostLhss"
    (Xmlt.xml_take_optional (Xmlt.xml_bool "nfs")
      (\ nfs ->
        Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
          (term xml2name termMap)
          (\ ret ->
            Xmlt.xml_return
              (Ceta_Problem_Spec.Innermost_Q (nfs_def nfs) ret))));

forbidden_pattern ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term a [Arith.Char]) ->
                                    (Xml.Xml,
                                      ([([Arith.Char], [Arith.Char])],
(Bool, ([String], [String])))) ->
                                      Strict_Sum.Sum_bot (Xmlt.Xml_error String)
(Term_Rewriting.Actxt a (Term_Rewriting.Term a [Arith.Char]),
  (Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Location));
forbidden_pattern xml2name termMap =
  Xmlt.xml_do "forbiddenPattern"
    (Xmlt.xml_take (term xml2name termMap)
      (\ t ->
        Xmlt.xml_take pos
          (\ p ->
            Xmlt.xml_take
              (Xmlt.xml_or (Xmlt.xml_leaf "here" Term_Rewriting.H)
                (Xmlt.xml_or (Xmlt.xml_leaf "above" Term_Rewriting.A)
                  (Xmlt.xml_or (Xmlt.xml_leaf "below" Term_Rewriting.B)
                    (Xmlt.xml_leaf "below" Term_Rewriting.R))))
              (\ l ->
                (if Term_Rewriting.in_poss p t
                  then Xmlt.xml_return
                         (Term_Rewriting.ctxt_of_pos_term p t,
                           (Term_Rewriting.subt_at t p, l))
                  else Xmlt.xml_error "position does not exist in term")))));

forbidden_patterns ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term a [Arith.Char]) ->
                                    (Xml.Xml,
                                      ([([Arith.Char], [Arith.Char])],
(Bool, ([String], [String])))) ->
                                      Strict_Sum.Sum_bot (Xmlt.Xml_error String)
[(Term_Rewriting.Actxt a (Term_Rewriting.Term a [Arith.Char]),
   (Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Location))];
forbidden_patterns xml2name termMap =
  Xmlt.xml_do "forbiddenPatterns"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (forbidden_pattern xml2name termMap) Xmlt.xml_return);

innermost ::
  forall a.
    (Term_Rewriting.Showl a) => (Xml.Xml,
                                  ([([Arith.Char], [Arith.Char])],
                                    (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Ceta_Problem_Spec.Strategy a [Arith.Char]);
innermost =
  Xmlt.xml_do "innermost"
    (Xmlt.xml_take_optional (Xmlt.xml_bool "nfs")
      (\ nfs -> Xmlt.xml_return (Ceta_Problem_Spec.Innermost (nfs_def nfs))));

inn_fp_strategy ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term a [Arith.Char]) ->
                                    (Xml.Xml,
                                      ([([Arith.Char], [Arith.Char])],
(Bool, ([String], [String])))) ->
                                      Strict_Sum.Sum_bot (Xmlt.Xml_error String)
(Sum_Type.Sum (Ceta_Problem_Spec.Strategy a [Arith.Char])
  (Ceta_Problem_Spec.Fp_strategy a [Arith.Char]));
inn_fp_strategy xml2name termMap =
  Xmlt.xml_do "strategy"
    (Xmlt.xml_take
      (Xmlt.xml_or
        (Xmlt.xml_change
          (Xmlt.xml_or innermost (innermostLhssStrategy xml2name termMap))
          (\ s -> Xmlt.xml_return (Sum_Type.Inl s)))
        (Xmlt.xml_or
          (Xmlt.xml_leaf "outermost" (Sum_Type.Inr Ceta_Problem_Spec.Outermost))
          (Xmlt.xml_or
            (Xmlt.xml_change (replacement_map xml2name)
              (\ p ->
                Xmlt.xml_return
                  (Sum_Type.Inr (Ceta_Problem_Spec.Context_Sensitive p))))
            (Xmlt.xml_change (forbidden_patterns xml2name termMap)
              (\ p ->
                Xmlt.xml_return
                  (Sum_Type.Inr (Ceta_Problem_Spec.Forbidden_Patterns p)))))))
      Xmlt.xml_return);

relative_dp_input ::
  forall a.
    (Eq a,
      Term_Rewriting.Showl a) => ((Xml.Xml,
                                    ([([Arith.Char], [Arith.Char])],
                                      (Bool, ([String], [String])))) ->
                                   Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                     a) ->
                                   Mapping.Mapping [Arith.Char]
                                     (Term_Rewriting.Term a [Arith.Char]) ->
                                     Mapping.Mapping [Arith.Char]
                                       (Term_Rewriting.Term a [Arith.Char],
 Term_Rewriting.Term a [Arith.Char]) ->
                                       (Xml.Xml,
 ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
 Strict_Sum.Sum_bot (Xmlt.Xml_error String)
   (Ceta_Problem_Spec.Input a [Arith.Char]);
relative_dp_input xml2name termMap ruleMap =
  Xmlt.xml_do "relativeDpInput"
    (Xmlt.xml_take
      (Xmlt.xml_do "trs"
        (Xmlt.xml_take (rules xml2name termMap ruleMap) Xmlt.xml_return))
      (\ r ->
        Xmlt.xml_take
          (Xmlt.xml_do "dps"
            (Xmlt.xml_take (rules xml2name termMap ruleMap) Xmlt.xml_return))
          (\ p ->
            Xmlt.xml_take
              (Xmlt.xml_do "weakDps"
                (Xmlt.xml_take (rules xml2name termMap ruleMap)
                  Xmlt.xml_return))
              (\ pw ->
                Xmlt.xml_take
                  (Xmlt.xml_do "strictRules"
                    (Xmlt.xml_take (rules xml2name termMap ruleMap)
                      Xmlt.xml_return))
                  (\ rs ->
                    Xmlt.xml_take (inn_fp_strategy xml2name termMap)
                      (\ str ->
                        Xmlt.xml_take (Xmlt.xml_bool "minimal")
                          (\ m ->
                            (case str of {
                              Sum_Type.Inl s ->
                                Xmlt.xml_return
                                  (Ceta_Problem_Spec.Relative_DP_input
                                    (Ceta_Problem_Spec.strategy_to_nfs s) m p pw
                                    (Ceta_Problem_Spec.strategy_to_Q s
                                      (rs ++ r))
                                    rs r);
                              Sum_Type.Inr _ ->
                                Xmlt.xml_error
                                  "relative DP input requires an explicit Q strategy";
                            }))))))));

symbols_wo_arity ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  String ->
                                    (Xml.Xml,
                                      ([([Arith.Char], [Arith.Char])],
(Bool, ([String], [String])))) ->
                                      Strict_Sum.Sum_bot (Xmlt.Xml_error String)
[a];
symbols_wo_arity xml2name tagname =
  Xmlt.xml_do tagname
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      xml2name Xmlt.xml_return);

ac_rewrite_system ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term a [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term a [Arith.Char],
Term_Rewriting.Term a [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Ceta_Problem_Spec.Input a [Arith.Char]);
ac_rewrite_system xml2name termMap ruleMap =
  Xmlt.xml_do "acRewriteSystem"
    (Xmlt.xml_take
      (Xmlt.xml_do "trs"
        (Xmlt.xml_take (rules xml2name termMap ruleMap) Xmlt.xml_return))
      (\ r ->
        Xmlt.xml_take (symbols_wo_arity xml2name "Asymbols")
          (\ asym ->
            Xmlt.xml_take (symbols_wo_arity xml2name "Csymbols")
              (\ csym ->
                Xmlt.xml_return (Ceta_Problem_Spec.AC_input r asym csym)))));

equations_input ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term a [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term a [Arith.Char],
Term_Rewriting.Term a [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Ceta_Problem_Spec.Input a [Arith.Char]);
equations_input xml2name termMap ruleMap =
  Xmlt.xml_do "equations"
    (Xmlt.xml_take (rules xml2name termMap ruleMap)
      (\ ret -> Xmlt.xml_return (Ceta_Problem_Spec.EQ_input ret)));

unknown_inputa ::
  (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String) [Arith.Char];
unknown_inputa = Xmlt.xml_text "unknownInput";

unknown_input ::
  forall a.
    (Term_Rewriting.Showl a) => (Xml.Xml,
                                  ([([Arith.Char], [Arith.Char])],
                                    (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Ceta_Problem_Spec.Input a [Arith.Char]);
unknown_input =
  Xmlt.xml_change unknown_inputa
    (\ s -> Xmlt.xml_return (Ceta_Problem_Spec.Unknown_input s));

ctrs_input ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term a [Arith.Char]) ->
                                    (Xml.Xml,
                                      ([([Arith.Char], [Arith.Char])],
(Bool, ([String], [String])))) ->
                                      Strict_Sum.Sum_bot (Xmlt.Xml_error String)
(Ceta_Problem_Spec.Input a [Arith.Char]);
ctrs_input xml2name termMap =
  Xmlt.xml_do "ctrsInput"
    (Xmlt.xml_take (ctrs xml2name termMap)
      (\ a -> Xmlt.xml_return (Ceta_Problem_Spec.CTRS_input a)));

trs_input ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term a [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term a [Arith.Char],
Term_Rewriting.Term a [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Ceta_Problem_Spec.Input a [Arith.Char]);
trs_input xml2name termMap ruleMap =
  Xmlt.xml_do "trsInput"
    (Xmlt.xml_take
      (Xmlt.xml_do "trs"
        (Xmlt.xml_take (rules xml2name termMap ruleMap) Xmlt.xml_return))
      (\ r ->
        Xmlt.xml_take_default (Sum_Type.Inl Ceta_Problem_Spec.No_Strategy)
          (inn_fp_strategy xml2name termMap)
          (\ str ->
            Xmlt.xml_take_default []
              (Xmlt.xml_do "relativeRules"
                (Xmlt.xml_take (rules xml2name termMap ruleMap)
                  Xmlt.xml_return))
              (\ rel ->
                (case str of {
                  Sum_Type.Inl istrat ->
                    Xmlt.xml_return
                      (Ceta_Problem_Spec.Inn_TRS_input istrat r rel);
                  Sum_Type.Inr fpstrat ->
                    (if null rel
                      then Xmlt.xml_return
                             (Ceta_Problem_Spec.FP_TRS_input fpstrat r)
                      else Xmlt.xml_error
                             "the combination of relative rules with strategies is only supported for innermost");
                })))));

dp_input ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term a [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term a [Arith.Char],
Term_Rewriting.Term a [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Ceta_Problem_Spec.Input a [Arith.Char]);
dp_input xml2name termMap ruleMap =
  Xmlt.xml_do "dpInput"
    (Xmlt.xml_take
      (Xmlt.xml_do "trs"
        (Xmlt.xml_take (rules xml2name termMap ruleMap) Xmlt.xml_return))
      (\ r ->
        Xmlt.xml_take
          (Xmlt.xml_do "dps"
            (Xmlt.xml_take (rules xml2name termMap ruleMap) Xmlt.xml_return))
          (\ p ->
            Xmlt.xml_take_default (Sum_Type.Inl Ceta_Problem_Spec.No_Strategy)
              (inn_fp_strategy xml2name termMap)
              (\ str ->
                Xmlt.xml_take (Xmlt.xml_bool "minimal")
                  (\ m ->
                    (case str of {
                      Sum_Type.Inl s ->
                        Xmlt.xml_return (Ceta_Problem_Spec.DP_input m p s r);
                      Sum_Type.Inr _ ->
                        Xmlt.xml_error
                          "ordinary dpInput cannot discard replacement-map or outermost context; use a typed CSR-DP input";
                    }))))));

input ::
  forall a.
    (Eq a,
      Term_Rewriting.Showl a) => ((Xml.Xml,
                                    ([([Arith.Char], [Arith.Char])],
                                      (Bool, ([String], [String])))) ->
                                   Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                     a) ->
                                   Mapping.Mapping [Arith.Char]
                                     (Term_Rewriting.Term a [Arith.Char]) ->
                                     Mapping.Mapping [Arith.Char]
                                       (Term_Rewriting.Term a [Arith.Char],
 Term_Rewriting.Term a [Arith.Char]) ->
                                       (Xml.Xml,
 ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
 Strict_Sum.Sum_bot (Xmlt.Xml_error String)
   (Ceta_Problem_Spec.Input a [Arith.Char]);
input xml2name termMap ruleMap =
  Xmlt.xml_do "input"
    (Xmlt.xml_take
      (Xmlt.xml_or (trs_input xml2name termMap ruleMap)
        (Xmlt.xml_or (trs_with_signature_input xml2name termMap ruleMap)
          (Xmlt.xml_or (two_trs_with_signature_input xml2name termMap ruleMap)
            (Xmlt.xml_or (ctrs_input xml2name termMap)
              (Xmlt.xml_or (equational_reasoning_input xml2name termMap ruleMap)
                (Xmlt.xml_or (equations_and_ro_input xml2name termMap ruleMap)
                  (Xmlt.xml_or (infeasibility_input xml2name termMap ruleMap)
                    (Xmlt.xml_or (equations_input xml2name termMap ruleMap)
                      (Xmlt.xml_or (ac_rewrite_system xml2name termMap ruleMap)
                        (Xmlt.xml_or (dp_input xml2name termMap ruleMap)
                          (Xmlt.xml_or
                            (csr_improved_dp_input xml2name termMap ruleMap)
                            (Xmlt.xml_or
                              (relative_dp_input xml2name termMap ruleMap)
                              (Xmlt.xml_or
                                (Xmlt.xml_change LTS_Parser.lts_input_parser
                                  (\ lts ->
                                    Xmlt.xml_return
                                      (Ceta_Problem_Spec.LTS_input lts)))
                                (Xmlt.xml_or
                                  (Xmlt.xml_change
                                    LTS_Parser.lts_safety_input_parser
                                    (\ (lts, err) ->
                                      Xmlt.xml_return
(Ceta_Problem_Spec.LTS_safety_input lts err)))
                                  (Xmlt.xml_or
                                    (tree_automaton_and_trs xml2name termMap
                                      ruleMap)
                                    unknown_input)))))))))))))))
      Xmlt.xml_return);

answer ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term a [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term a [Arith.Char],
Term_Rewriting.Term a [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Ceta_Problem_Spec.Answer a [Arith.Char]);
answer xml2name termMap ruleMap =
  Xmlt.xml_do "answer"
    (Xmlt.xml_take
      (Xmlt.xml_or
        (Xmlt.xml_do "yes" (Xmlt.xml_return (Ceta_Problem_Spec.Decision True)))
        (Xmlt.xml_or
          (Xmlt.xml_do "no"
            (Xmlt.xml_return (Ceta_Problem_Spec.Decision False)))
          (Xmlt.xml_or
            (Xmlt.xml_do "upperBound"
              (Xmlt.xml_take (Xmlt.xml_nat "polynomial")
                (\ n -> Xmlt.xml_return (Ceta_Problem_Spec.Upperbound_Poly n))))
            (Xmlt.xml_or
              (Xmlt.xml_do "completedTrs"
                (Xmlt.xml_take
                  (Xmlt.xml_do "trs"
                    (Xmlt.xml_take (rules xml2name termMap ruleMap)
                      Xmlt.xml_return))
                  (\ r ->
                    Xmlt.xml_return (Ceta_Problem_Spec.Completed_System r))))
              (Xmlt.xml_do "orderCompletedSystem"
                (Xmlt.xml_take
                  (Xmlt.xml_do "equations"
                    (Xmlt.xml_take (rules xml2name termMap ruleMap)
                      Xmlt.xml_return))
                  (\ e ->
                    Xmlt.xml_take
                      (Xmlt.xml_do "trs"
                        (Xmlt.xml_take (rules xml2name termMap ruleMap)
                          Xmlt.xml_return))
                      (\ r ->
                        Xmlt.xml_return
                          (Ceta_Problem_Spec.Order_Completed_System e r)))))))))
      Xmlt.xml_return);

complexity_measure ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  (Xml.Xml,
                                    ([([Arith.Char], [Arith.Char])],
                                      (Bool, ([String], [String])))) ->
                                    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                      (Ceta_Problem_Spec.ComplexityMeasure a
[Arith.Char]);
complexity_measure xml2name =
  Xmlt.xml_or
    (Xmlt.xml_do "derivationalComplexity"
      (Xmlt.xml_take_optional (cPFsignature xml2name)
        (\ a -> Xmlt.xml_return (Ceta_Problem_Spec.Derivational a))))
    (Xmlt.xml_do "runtimeComplexity"
      (Xmlt.xml_take_optional (cPFsignature xml2name)
        (\ a ->
          Xmlt.xml_take_optional (cPFsignature xml2name)
            (\ b ->
              (case (a, b) of {
                (Nothing, Nothing) ->
                  Xmlt.xml_return (Ceta_Problem_Spec.Runtime Nothing);
                (Nothing, Just _) ->
                  Xmlt.xml_error
                    "runtimeComplexity must provide 0 or 2 signatures";
                (Just _, Nothing) ->
                  Xmlt.xml_error
                    "runtimeComplexity must provide 0 or 2 signatures";
                (Just c, Just d) ->
                  Xmlt.xml_return (Ceta_Problem_Spec.Runtime (Just (c, d)));
              })))));

property ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  (Xml.Xml,
                                    ([([Arith.Char], [Arith.Char])],
                                      (Bool, ([String], [String])))) ->
                                    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                      (Ceta_Problem_Spec.Property a
[Arith.Char]);
property xml2name =
  Xmlt.xml_do "property"
    (Xmlt.xml_take
      (Xmlt.xml_or
        (Xmlt.xml_do "termination"
          (Xmlt.xml_return Ceta_Problem_Spec.Termination))
        (Xmlt.xml_or
          (Xmlt.xml_do "confluence"
            (Xmlt.xml_return Ceta_Problem_Spec.Confluence))
          (Xmlt.xml_or
            (Xmlt.xml_do "commutation"
              (Xmlt.xml_return Ceta_Problem_Spec.Commutation))
            (Xmlt.xml_or
              (Xmlt.xml_do "completion"
                (Xmlt.xml_return Ceta_Problem_Spec.Completion))
              (Xmlt.xml_or
                (Xmlt.xml_do "complexity"
                  (Xmlt.xml_take (complexity_measure xml2name)
                    (\ cm ->
                      Xmlt.xml_return (Ceta_Problem_Spec.Complexity cm))))
                (Xmlt.xml_or
                  (Xmlt.xml_do "safety"
                    (Xmlt.xml_return Ceta_Problem_Spec.Safety))
                  (Xmlt.xml_or
                    (Xmlt.xml_do "entailment"
                      (Xmlt.xml_return Ceta_Problem_Spec.Entailment))
                    (Xmlt.xml_or
                      (Xmlt.xml_do "infeasibility"
                        (Xmlt.xml_return Ceta_Problem_Spec.Infeasibility))
                      (Xmlt.xml_or
                        (Xmlt.xml_do "closedUnderRewriting"
                          (Xmlt.xml_return
                            Ceta_Problem_Spec.Closed_Under_Rewriting))
                        (Xmlt.xml_do "unknownProperty"
                          (Xmlt.xml_return
                            Ceta_Problem_Spec.Unknown_Property)))))))))))
      Xmlt.xml_return);

ruleTable ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term a [Arith.Char]) ->
                                    (Xml.Xml,
                                      ([([Arith.Char], [Arith.Char])],
(Bool, ([String], [String])))) ->
                                      Strict_Sum.Sum_bot (Xmlt.Xml_error String)
(Mapping.Mapping [Arith.Char]
  (Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char]));
ruleTable xml2name termMap =
  Xmlt.xml_do "ruleTable"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (Xmlt.xml_do "indexToRule"
        (Xmlt.xml_take (Xmlt.xml_text "index")
          (\ idx ->
            Xmlt.xml_take (full_rule xml2name termMap)
              (\ rule -> Xmlt.xml_return (idx, rule)))))
      (\ entries ->
        (if Arith.distinct (map fst entries)
          then Xmlt.xml_return (Mapping.of_alist entries)
          else Xmlt.xml_error "rule table contains duplicate index")));

indexToTerm ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term a [Arith.Char]) ->
                                    (Xml.Xml,
                                      ([([Arith.Char], [Arith.Char])],
(Bool, ([String], [String])))) ->
                                      Strict_Sum.Sum_bot (Xmlt.Xml_error String)
([Arith.Char], Term_Rewriting.Term a [Arith.Char]);
indexToTerm xml2name termMap =
  Xmlt.xml_do "indexToTerm"
    (Xmlt.xml_take (Xmlt.xml_text "index")
      (\ idx ->
        Xmlt.xml_take (term xml2name termMap)
          (\ t ->
            (case Mapping.lookup termMap idx of {
              Nothing -> Xmlt.xml_return (idx, t);
              Just _ ->
                Xmlt.xml_error "term index table contains duplicate index";
            }))));

termIndexTable ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  (Xml.Xml,
                                    ([([Arith.Char], [Arith.Char])],
                                      (Bool, ([String], [String])))) ->
                                    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                      (Mapping.Mapping [Arith.Char]
(Term_Rewriting.Term a [Arith.Char]));
termIndexTable xml2name =
  Xmlt.xml_do "termIndexTable"
    (Xmlt.xml_foldl (indexToTerm xml2name)
      (\ termMap (idx, t) -> Mapping.update idx t termMap)
      (Mapping.mapping_empty
        (Phantom_Type.of_phantom Mapping.mapping_impl_list)));

lookupTables ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  (Xml.Xml,
                                    ([([Arith.Char], [Arith.Char])],
                                      (Bool, ([String], [String])))) ->
                                    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                      (Mapping.Mapping [Arith.Char]
 (Term_Rewriting.Term a [Arith.Char]),
Mapping.Mapping [Arith.Char]
  (Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char]));
lookupTables xml2name =
  Xmlt.xml_do "lookupTables"
    (Xmlt.xml_take_default
      (Mapping.mapping_empty
        (Phantom_Type.of_phantom Mapping.mapping_impl_list))
      (termIndexTable xml2name)
      (\ termIndexMap ->
        Xmlt.xml_take_default
          (Mapping.mapping_empty
            (Phantom_Type.of_phantom Mapping.mapping_impl_list))
          (ruleTable xml2name termIndexMap)
          (\ ruleMap -> Xmlt.xml_return (termIndexMap, ruleMap))));

innermostLhss ::
  forall a.
    (Term_Rewriting.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term a [Arith.Char]) ->
                                    (Xml.Xml,
                                      ([([Arith.Char], [Arith.Char])],
(Bool, ([String], [String])))) ->
                                      Strict_Sum.Sum_bot (Xmlt.Xml_error String)
[Term_Rewriting.Term a [Arith.Char]];
innermostLhss xml2name termMap =
  Xmlt.xml_do "innermostLhss"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (term xml2name termMap) Xmlt.xml_return);

strategy_to_fp ::
  forall a.
    (Eq a) => Ceta_Problem_Spec.Fp_strategy a [Arith.Char] ->
                [(Term_Rewriting.Term a [Arith.Char],
                   Term_Rewriting.Term a [Arith.Char])] ->
                  [(Term_Rewriting.Actxt a (Term_Rewriting.Term a [Arith.Char]),
                     (Term_Rewriting.Term a [Arith.Char],
                       Term_Rewriting.Location))];
strategy_to_fp (Ceta_Problem_Spec.Forbidden_Patterns p) r = p;
strategy_to_fp Ceta_Problem_Spec.Outermost r =
  Outermost_Forbidden_Patterns.o_to_fp_impl (map fst r);
strategy_to_fp (Ceta_Problem_Spec.Context_Sensitive mu) r =
  Context_Sensitive_Impl.mu_to_fp_impl mu;

}
