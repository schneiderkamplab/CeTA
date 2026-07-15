{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  CPF_Proof_Parser(symbol_parser, input_parser, proof_parser, answer_parser,
                    property_parser)
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
import qualified Uncurry_Impl;
import qualified Q_Reduction_Nonterm_Impl;
import qualified Instantiation_Impl;
import qualified Nontermination_Impl;
import qualified Rewriting_Impl;
import qualified Narrowing_Impl;
import qualified Loops_Impl;
import qualified Exact_Tree_Automata_Completion_Impl;
import qualified Monadic_Rewriting_Impl;
import qualified Complex_Constant_Removal_Impl;
import qualified AC_Dependency_Pairs_Impl;
import qualified Check_Nonreachability;
import qualified Bounded_Increase_Impl;
import qualified Check_Level_Confluence;
import qualified DT_Transformation_Impl;
import qualified WDP_Transformation_Impl;
import qualified Complexity;
import qualified Check_AL94;
import qualified Generalized_Usable_Rules;
import qualified Ordered_Semiring;
import qualified Non_Confluence_Impl;
import qualified Defaults;
import qualified Map;
import qualified Check_Termination_Common;
import qualified Forbidden_Patterns;
import qualified Equational_Reasoning;
import qualified Rule_Labeling_Impl;
import qualified Parallel_Critical_Pairs_Impl;
import qualified Ceta_Problem_Spec;
import qualified HOL;
import qualified Nonloop_SRS;
import qualified Matchbounds_Impl;
import qualified Critical_Pairs_Impl;
import qualified Check_Joins;
import qualified List_Order_Implementations;
import qualified Max_Polynomial;
import qualified Max_Monus;
import qualified WPO;
import qualified Not_WN_Tree_Automaton_Impl;
import qualified Sum_Type;
import qualified Semantic_Labeling_Carrier;
import qualified NthRoot;
import qualified Congruence;
import qualified Group;
import qualified Ring;
import qualified Nonloop_Impl;
import qualified LTS_Parser;
import qualified Ordered_Completion_Impl;
import qualified Reduction_Pair_Implementations;
import qualified Check_Quasi_Reductive;
import qualified Check_Conditional_CRP;
import qualified Check_AC_Termination;
import qualified LTS_Termination_Prover;
import qualified Check_Equational_Proof;
import qualified Check_Completion_Proof;
import qualified Check_Nontermination;
import qualified Check_Infeasibility;
import qualified Check_Complexity;
import qualified Check_Termination;
import qualified Tree_Automata_Impl;
import qualified LTS_Safety_Prover;
import qualified Proof_Checker;
import qualified Check_CRP;
import qualified IA_Checker;
import qualified Compare_Order_Instances;
import qualified Conditional_Rewriting_Impl;
import qualified Labelings;
import qualified Compare;
import qualified Labelings_Impl;
import qualified Subterm_Criterion;
import qualified Subterm_Criterion_Impl;
import qualified Mapping;
import qualified CPF_Input_Parser;
import qualified Term_Rewriting;
import qualified Strict_Sum;
import qualified Extended_Nat;
import qualified Xmlt;
import qualified Xml;
import qualified Shows_Literal;
import qualified SN_Order_Carrier;
import qualified Polynomials;
import qualified Matrix;
import qualified Matrix_TRS_Impl;
import qualified Real;
import qualified Rat;
import qualified Arith;

data Domain = Natural Arith.Nat | Integera | NegativeInteger | Arctic
  | Arctic_rat | Int_mat Arith.Nat Arith.Nat | Arctic_mat Arith.Nat
  | Arctic_rat_mat Arith.Nat | Rational Rat.Rat Arith.Nat
  | Rat_mat Arith.Nat Arith.Nat | Mini_Alg Real.Real Arith.Nat
  | Mini_Alg_mat Arith.Nat Arith.Nat
  | Int_core_mat Arith.Nat [Arith.Nat] Matrix_TRS_Impl.Core_matrix_mode
  | Real_core_mat Real.Real Arith.Nat [Arith.Nat]
      Matrix_TRS_Impl.Core_matrix_mode;

data Interpretation a =
  Int_linear_poly ((a, Arith.Nat), (Arith.Int, [Arith.Int]))
  | Rat_linear_poly ((a, Arith.Nat), (Rat.Rat, [Rat.Rat]))
  | Arctic_linear_poly
      ((a, Arith.Nat), (SN_Order_Carrier.Arctic, [SN_Order_Carrier.Arctic]))
  | Arctic_rat_linear_poly
      ((a, Arith.Nat),
        (SN_Order_Carrier.Arctic_delta Rat.Rat,
          [SN_Order_Carrier.Arctic_delta Rat.Rat]))
  | Real_linear_poly ((a, Arith.Nat), (Real.Real, [Real.Real]))
  | Int_matrix ((a, Arith.Nat), (Matrix.Mat Arith.Int, [Matrix.Mat Arith.Int]))
  | Rat_matrix ((a, Arith.Nat), (Matrix.Mat Rat.Rat, [Matrix.Mat Rat.Rat]))
  | Arctic_matrix
      ((a, Arith.Nat),
        (Matrix.Mat SN_Order_Carrier.Arctic,
          [Matrix.Mat SN_Order_Carrier.Arctic]))
  | Arctic_rat_matrix
      ((a, Arith.Nat),
        (Matrix.Mat (SN_Order_Carrier.Arctic_delta Rat.Rat),
          [Matrix.Mat (SN_Order_Carrier.Arctic_delta Rat.Rat)]))
  | Real_matrix ((a, Arith.Nat), (Matrix.Mat Real.Real, [Matrix.Mat Real.Real]))
  | Int_core_matrix
      ((a, Arith.Nat), (Matrix.Mat Arith.Int, [Matrix.Mat Arith.Int]))
  | Real_core_matrix Real.Real
      ((a, Arith.Nat), (Matrix.Mat Real.Real, [Matrix.Mat Real.Real]))
  | Int_non_linear_poly
      ((a, Arith.Nat), [(Polynomials.Monom Arith.Nat, Arith.Int)])
  | Rat_non_linear_poly
      ((a, Arith.Nat), [(Polynomials.Monom Arith.Nat, Rat.Rat)])
  | Real_non_linear_poly
      ((a, Arith.Nat), [(Polynomials.Monom Arith.Nat, Real.Real)]);

afs ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
                                  ([([Arith.Char], [Arith.Char])],
                                    (Bool, ([String], [String])))) ->
                                 Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                   a) ->
                                 (Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                   Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                     [((a, Arith.Nat),
Term_Rewriting.Af_entry)];
afs xml2name =
  Xmlt.xml_do "argumentFilter"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (Xmlt.xml_do "argumentFilterEntry"
        (Xmlt.xml_take xml2name
          (\ name ->
            Xmlt.xml_take (Xmlt.xml_nat "arity")
              (\ arity ->
                Xmlt.xml_take
                  (Xmlt.xml_or
                    (Xmlt.xml_change (Xmlt.xml_nat "collapsing")
                      (\ n ->
                        Xmlt.xml_return
                          (Term_Rewriting.Collapse
                            (Arith.minus_nat n Arith.one_nat))))
                    (Xmlt.xml_do "nonCollapsing"
                      (Xmlt.xml_take_many_sub [] Arith.zero_nat
                        Extended_Nat.Infinity_enat CPF_Input_Parser.position
                        (\ ls -> Xmlt.xml_return (Term_Rewriting.AFList ls)))))
                  (\ main -> Xmlt.xml_return ((name, arity), main))))))
      Xmlt.xml_return);

scg_position ::
  (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String) Arith.Nat;
scg_position = Xmlt.xml_nat "position";

scg ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
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
                                       ([([Arith.Char], [Arith.Char])],
 (Bool, ([String], [String])))) ->
                                       Strict_Sum.Sum_bot
 (Xmlt.Xml_error String)
 ((Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char]),
   ([(Arith.Nat, Arith.Nat)], [(Arith.Nat, Arith.Nat)]));
scg xml2name termIndexMap ruleMap =
  Xmlt.xml_do "sizeChangeGraph"
    (Xmlt.xml_take (CPF_Input_Parser.rule xml2name termIndexMap ruleMap)
      (\ lr ->
        Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
          (Xmlt.xml_do "edge"
            (Xmlt.xml_take scg_position
              (\ p ->
                Xmlt.xml_take (Xmlt.xml_bool "strict")
                  (\ s ->
                    Xmlt.xml_take scg_position
                      (\ q -> Xmlt.xml_return (s, (p, q)))))))
          (\ edges ->
            Xmlt.xml_return
              (lr, (Arith.map_filter
                      (\ x -> (if fst x then Just (snd x) else Nothing)) edges,
                     Arith.map_filter
                       (\ x -> (if not (fst x) then Just (snd x) else Nothing))
                       edges)))));

ctxt ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
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
                                       (Term_Rewriting.Actxt a
 (Term_Rewriting.Term a [Arith.Char]));
ctxt xml2name termIndexMap x =
  Xmlt.xml_or (Xmlt.xml_do "box" (Xmlt.xml_return Term_Rewriting.Hole))
    (Xmlt.xml_do "funContext"
      (Xmlt.xml_take xml2name
        (\ name ->
          Xmlt.xml_take
            (Xmlt.xml_do "before"
              (Xmlt.xml_take_many_sub [] Arith.zero_nat
                Extended_Nat.Infinity_enat
                (CPF_Input_Parser.term xml2name termIndexMap) Xmlt.xml_return))
            (\ left ->
              Xmlt.xml_take (ctxt xml2name termIndexMap)
                (\ mid ->
                  Xmlt.xml_take
                    (Xmlt.xml_do "after"
                      (Xmlt.xml_take_many_sub [] Arith.zero_nat
                        Extended_Nat.Infinity_enat
                        (CPF_Input_Parser.term xml2name termIndexMap)
                        Xmlt.xml_return))
                    (\ right ->
                      Xmlt.xml_return
                        (Term_Rewriting.More name left mid right)))))))
    x;

relstep ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
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
                                       ([([Arith.Char], [Arith.Char])],
 (Bool, ([String], [String])))) ->
                                       Strict_Sum.Sum_bot
 (Xmlt.Xml_error String)
 ([Arith.Nat],
   ((Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char]),
     (Bool, Term_Rewriting.Term a [Arith.Char])));
relstep xml2name termIndexMap ruleMap =
  Xmlt.xml_do "rewriteStep"
    (Xmlt.xml_take CPF_Input_Parser.pos
      (\ p ->
        Xmlt.xml_take (CPF_Input_Parser.rule xml2name termIndexMap ruleMap)
          (\ r ->
            Xmlt.xml_take_optional (Xmlt.xml_leaf "relative" ())
              (\ rel ->
                Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
                  (\ t -> Xmlt.xml_return (p, (r, (Arith.is_none rel, t))))))));

relsteps ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
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
                                       ([([Arith.Char], [Arith.Char])],
 (Bool, ([String], [String])))) ->
                                       Strict_Sum.Sum_bot
 (Xmlt.Xml_error String)
 (Term_Rewriting.Term a [Arith.Char],
   [([Arith.Nat],
      ((Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char]),
        (Bool, Term_Rewriting.Term a [Arith.Char])))]);
relsteps xml2name termIndexMap ruleMap =
  Xmlt.xml_do "rewriteSequence"
    (Xmlt.xml_take
      (Xmlt.xml_do "startTerm"
        (Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
          (\ x -> Xmlt.xml_return (id x))))
      (\ start ->
        Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
          (relstep xml2name termIndexMap ruleMap)
          (\ steps -> Xmlt.xml_return (start, steps))));

subst ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
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
                                       [([Arith.Char],
  Term_Rewriting.Term a [Arith.Char])];
subst xml2name termIndexMap =
  Xmlt.xml_do "substitution"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (Xmlt.xml_do "substEntry"
        (Xmlt.xml_take (Xmlt.xml_do "var" (Xmlt.xml_take_text Xmlt.xml_return))
          (\ var ->
            Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
              (\ trm -> Xmlt.xml_return (var, trm)))))
      Xmlt.xml_return);

loop ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
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
                                       ([([Arith.Char], [Arith.Char])],
 (Bool, ([String], [String])))) ->
                                       Strict_Sum.Sum_bot
 (Xmlt.Xml_error String)
 (Term_Rewriting.Term a [Arith.Char],
   ([([Arith.Nat],
       ((Term_Rewriting.Term a [Arith.Char],
          Term_Rewriting.Term a [Arith.Char]),
         (Bool, Term_Rewriting.Term a [Arith.Char])))],
     ([([Arith.Char], Term_Rewriting.Term a [Arith.Char])],
       Term_Rewriting.Actxt a (Term_Rewriting.Term a [Arith.Char]))));
loop xml2name termIndexMap ruleMap =
  Xmlt.xml_do "loop"
    (Xmlt.xml_take (relsteps xml2name termIndexMap ruleMap)
      (\ (s, rseq) ->
        Xmlt.xml_take (subst xml2name termIndexMap)
          (\ sigma ->
            Xmlt.xml_take (ctxt xml2name termIndexMap)
              (\ c -> Xmlt.xml_return (s, (rseq, (sigma, c)))))));

proj ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
                                  ([([Arith.Char], [Arith.Char])],
                                    (Bool, ([String], [String])))) ->
                                 Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                   a) ->
                                 (Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                   Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                     (Subterm_Criterion_Impl.ProjL a);
proj xml2name =
  Xmlt.xml_change (afs xml2name)
    (\ afl ->
      Xmlt.xml_return
        (Subterm_Criterion_Impl.Projection
          (map (\ a -> (case a of {
                         (fa, Term_Rewriting.Collapse aa) -> (fa, aa);
                         (fa, Term_Rewriting.AFList _) -> (fa, snd fa);
                       }))
            afl)));

start_term ::
  forall a.
    (Eq a,
      Shows_Literal.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term a [Arith.Char]) ->
                                    Term_Rewriting.Term a [Arith.Char] ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String) (Term_Rewriting.Term a [Arith.Char]);
start_term xml2name termIndexMap t =
  Xmlt.xml_do "startTerm"
    (Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
      (\ s ->
        (if Term_Rewriting.equal_term s t then Xmlt.xml_return t
          else Xmlt.xml_error "<startTerm> does not match lhs")));

rstep ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
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
                                       ([([Arith.Char], [Arith.Char])],
 (Bool, ([String], [String])))) ->
                                       Strict_Sum.Sum_bot
 (Xmlt.Xml_error String)
 ([Arith.Nat],
   ((Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char]),
     Term_Rewriting.Term a [Arith.Char]));
rstep xml2name termIndexMap ruleMap =
  Xmlt.xml_do "rewriteStep"
    (Xmlt.xml_take CPF_Input_Parser.pos
      (\ p ->
        Xmlt.xml_take (CPF_Input_Parser.rule xml2name termIndexMap ruleMap)
          (\ r ->
            Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
              (\ t -> Xmlt.xml_return (p, (r, t))))));

rseq ::
  forall a.
    (Eq a,
      Shows_Literal.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term a [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term a [Arith.Char],
Term_Rewriting.Term a [Arith.Char]) ->
                                      ((a, Arith.Nat) -> Arith.Nat) ->
(Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char]) ->
  (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
      ((Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char]),
        [([Arith.Nat],
           ((Term_Rewriting.Term a [Arith.Char],
              Term_Rewriting.Term a [Arith.Char]),
             Term_Rewriting.Term a [Arith.Char]))]);
rseq xml2name termIndexMap ruleMap pi r =
  Xmlt.xml_do "rewriteSequence"
    (Xmlt.xml_take
      (start_term xml2name termIndexMap
        (Subterm_Criterion.proj_term pi (fst r)))
      (\ _ ->
        Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
          (rstep xml2name termIndexMap ruleMap)
          (\ rseq -> Xmlt.xml_return (r, rseq))));

cstep ::
  forall a b.
    (Compare.Compare_order a, Shows_Literal.Showl a, Compare.Compare_order b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    (Xml.Xml,
                                      ([([Arith.Char], [Arith.Char])],
(Bool, ([String], [String])))) ->
                                      Strict_Sum.Sum_bot (Xmlt.Xml_error String)
(Conditional_Rewriting_Impl.Cstep_proof (Labelings.Lab a b) [Arith.Char]);
cstep xml2name termIndexMap x =
  Xmlt.xml_do "conditionalRewriteStep"
    (Xmlt.xml_take (CPF_Input_Parser.crule xml2name termIndexMap "rule")
      (\ a ->
        Xmlt.xml_take CPF_Input_Parser.pos
          (\ b ->
            Xmlt.xml_take (subst xml2name termIndexMap)
              (\ c ->
                Xmlt.xml_take
                  (Xmlt.xml_do "source"
                    (Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
                      (\ xa -> Xmlt.xml_return (id xa))))
                  (\ d ->
                    Xmlt.xml_take
                      (Xmlt.xml_do "target"
                        (Xmlt.xml_take
                          (CPF_Input_Parser.term xml2name termIndexMap)
                          (\ xa -> Xmlt.xml_return (id xa))))
                      (\ e ->
                        Xmlt.xml_take
                          (Xmlt.xml_do "conditions"
                            (Xmlt.xml_take_many_sub [] Arith.zero_nat
                              Extended_Nat.Infinity_enat
                              (csteps xml2name termIndexMap)
                              (\ aa -> Xmlt.xml_return (id aa))))
                          (\ f ->
                            Xmlt.xml_return
                              (Conditional_Rewriting_Impl.Cstep_step a b
                                (Term_Rewriting.mk_subst Term_Rewriting.Var c) d
                                e f))))))))
    x;

csteps ::
  forall a b.
    (Compare.Compare_order a, Shows_Literal.Showl a, Compare.Compare_order b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    (Xml.Xml,
                                      ([([Arith.Char], [Arith.Char])],
(Bool, ([String], [String])))) ->
                                      Strict_Sum.Sum_bot (Xmlt.Xml_error String)
[Conditional_Rewriting_Impl.Cstep_proof (Labelings.Lab a b) [Arith.Char]];
csteps xml2name termIndexMap x =
  Xmlt.xml_do "conditionalRewritingSequence"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (cstep xml2name termIndexMap) (\ a -> Xmlt.xml_return (id a)))
    x;

xml2dp_input ::
  forall a b c.
    (Eq a,
      Shows_Literal.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term a [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term a [Arith.Char],
Term_Rewriting.Term a [Arith.Char]) ->
                                      Bool ->
(Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
    (Bool,
      (Bool,
        ([(Term_Rewriting.Term a [Arith.Char],
            Term_Rewriting.Term a [Arith.Char])],
          ([b], ([Term_Rewriting.Term a [Arith.Char]],
                  ([c], [(Term_Rewriting.Term a [Arith.Char],
                           Term_Rewriting.Term a [Arith.Char])]))))));
xml2dp_input xml2name termIndexMap ruleMap termination =
  Xmlt.xml_change (CPF_Input_Parser.dp_input xml2name termIndexMap ruleMap)
    (\ (Ceta_Problem_Spec.DP_input m p q r) ->
      Xmlt.xml_return
        ((if termination then Defaults.default_nfs_dp
           else Defaults.default_nfs_nt_dp),
          (m, (p, ([], (Ceta_Problem_Spec.strategy_to_Q q r, ([], r)))))));

xml2crit_pair_info ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
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
                                       (Check_Joins.Crit_pair_info a
 [Arith.Char]);
xml2crit_pair_info xml2name termIndexMap =
  Xmlt.xml_do "critPairInfo"
    (Xmlt.xml_take
      (Xmlt.xml_do "left"
        (Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
          (\ x -> Xmlt.xml_return (id x))))
      (\ s ->
        Xmlt.xml_take_optional
          (Xmlt.xml_do "peak"
            (Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
              (\ x -> Xmlt.xml_return (id x))))
          (\ t ->
            Xmlt.xml_take
              (Xmlt.xml_do "right"
                (Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
                  (\ x -> Xmlt.xml_return (id x))))
              (\ u ->
                Xmlt.xml_take_optional
                  (Xmlt.xml_do "overlapPositions"
                    (Xmlt.xml_take_many_sub [] Arith.zero_nat
                      Extended_Nat.Infinity_enat CPF_Input_Parser.pos
                      Xmlt.xml_return))
                  (\ pos ->
                    Xmlt.xml_take_optional
                      (Xmlt.xml_do "labels"
                        (Xmlt.xml_take (Xmlt.xml_nat "maxLeft")
                          (\ left ->
                            Xmlt.xml_take (Xmlt.xml_nat "right")
                              (\ right -> Xmlt.xml_return (left, right)))))
                      (\ labels ->
                        Xmlt.xml_take
                          (Xmlt.xml_do "intermediateTerms"
                            (Xmlt.xml_take_many_sub [] Arith.zero_nat
                              Extended_Nat.Infinity_enat
                              (CPF_Input_Parser.term xml2name termIndexMap)
                              Xmlt.xml_return))
                          (\ joins ->
                            Xmlt.xml_return
                              (Check_Joins.Crit_Pair_Info s t u joins pos
                                labels))))))));

joinSequences ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
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
                                       [Check_Joins.Crit_pair_info a
  [Arith.Char]];
joinSequences xml2name termIndexMap =
  Xmlt.xml_do "joinSequences"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (xml2crit_pair_info xml2name termIndexMap) Xmlt.xml_return);

joinAutoBfs ::
  (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String) (Maybe Arith.Nat);
joinAutoBfs =
  Xmlt.xml_change (Xmlt.xml_int "joinAutoBfs")
    (\ x ->
      Xmlt.xml_return
        (if Arith.less_int x Arith.zero_int then Nothing
          else Just (Arith.nat x)));

joinAutoBfs1 ::
  (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String) Arith.Nat;
joinAutoBfs1 =
  Xmlt.xml_change joinAutoBfs
    (\ x -> Xmlt.xml_return (case x of {
                              Nothing -> Arith.one_nat;
                              Just n -> n;
                            }));

xml2cp_join_info ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
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
                                       (Check_Joins.Cp_join_hints a
 [Arith.Char]);
xml2cp_join_info xml2name termIndexMap =
  Xmlt.xml_or
    (Xmlt.xml_change joinAutoBfs1 (Xmlt.xml_return . Check_Joins.CP_Auto))
    (Xmlt.xml_change (joinSequences xml2name termIndexMap)
      (\ joins -> Xmlt.xml_return (Check_Joins.CP_Sequences joins)));

wcr_proof ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
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
                                       (Critical_Pairs_Impl.Join_info a
 [Arith.Char]);
wcr_proof xml2name termIndexMap =
  Xmlt.xml_do "wcrProof"
    (Xmlt.xml_take
      (Xmlt.xml_or
        (Xmlt.xml_change (xml2cp_join_info xml2name termIndexMap)
          (Xmlt.xml_return . Critical_Pairs_Impl.Guided_BFS))
        (Xmlt.xml_leaf "joinAutoNF" Critical_Pairs_Impl.Join_NF))
      (\ x -> Xmlt.xml_return (id x)));

pat_eqv_prf ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
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
                                       (Nonloop_Impl.Pat_eqv_prf a
 [Arith.Char]);
pat_eqv_prf xml2name termIndexMap =
  let {
    sub = subst xml2name termIndexMap;
  } in Xmlt.xml_do "patternEquivalence"
         (Xmlt.xml_take
           (Xmlt.xml_or
             (Xmlt.xml_do "domainRenaming"
               (Xmlt.xml_take sub
                 (\ n -> Xmlt.xml_return (Nonloop_Impl.Pat_Dom_Renaming n))))
             (Xmlt.xml_or
               (Xmlt.xml_do "irrelevant"
                 (Xmlt.xml_take sub
                   (\ n ->
                     Xmlt.xml_take sub
                       (\ n2 ->
                         Xmlt.xml_return (Nonloop_Impl.Pat_Irrelevant n n2)))))
               (Xmlt.xml_do "simplification"
                 (Xmlt.xml_take sub
                   (\ n ->
                     Xmlt.xml_take sub
                       (\ n2 ->
                         Xmlt.xml_return (Nonloop_Impl.Pat_Simplify n n2)))))))
           (\ x -> Xmlt.xml_return (id x)));

pat_term ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
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
                                       (Term_Rewriting.Term a [Arith.Char],
 ([([Arith.Char], Term_Rewriting.Term a [Arith.Char])],
   [([Arith.Char], Term_Rewriting.Term a [Arith.Char])]));
pat_term xml2name termIndexMap =
  Xmlt.xml_do "patternTerm"
    (Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
      (\ t ->
        Xmlt.xml_take (subst xml2name termIndexMap)
          (\ s1 ->
            Xmlt.xml_take (subst xml2name termIndexMap)
              (\ s2 -> Xmlt.xml_return (t, (s1, s2))))));

rsteps ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
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
                                       ([([Arith.Char], [Arith.Char])],
 (Bool, ([String], [String])))) ->
                                       Strict_Sum.Sum_bot
 (Xmlt.Xml_error String)
 (Term_Rewriting.Term a [Arith.Char],
   [([Arith.Nat],
      ((Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char]),
        Term_Rewriting.Term a [Arith.Char]))]);
rsteps xml2name termIndexMap ruleMap =
  Xmlt.xml_do "rewriteSequence"
    (Xmlt.xml_take
      (Xmlt.xml_do "startTerm"
        (Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
          (\ x -> Xmlt.xml_return (id x))))
      (\ start ->
        Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
          (rstep xml2name termIndexMap ruleMap)
          (\ steps -> Xmlt.xml_return (start, steps))));

pat_rule_prf ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
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
                                       ([([Arith.Char], [Arith.Char])],
 (Bool, ([String], [String])))) ->
                                       Strict_Sum.Sum_bot
 (Xmlt.Xml_error String) (Nonloop_Impl.Pat_rule_prf a [Arith.Char]);
pat_rule_prf xml2name termIndexMap ruleMap x =
  let {
    pat = pat_rule_prf xml2name termIndexMap ruleMap;
    sub = subst xml2name termIndexMap;
    pt = pat_term xml2name termIndexMap;
    var = Xmlt.xml_text "var";
  } in Xmlt.xml_do "patternRule"
         (Xmlt.xml_take pt
           (\ _ ->
             Xmlt.xml_take pt
               (\ _ ->
                 Xmlt.xml_take
                   (Xmlt.xml_or
                     (Xmlt.xml_do "originalRule"
                       (Xmlt.xml_take
                         (CPF_Input_Parser.rule xml2name termIndexMap ruleMap)
                         (\ r ->
                           Xmlt.xml_take (Xmlt.xml_bool "isPair")
                             (\ b ->
                               Xmlt.xml_return
                                 (Nonloop_Impl.Pat_OrigRule r b)))))
                     (Xmlt.xml_or
                       (Xmlt.xml_do "initialPumping"
                         (Xmlt.xml_take pat
                           (\ a ->
                             Xmlt.xml_take sub
                               (\ b ->
                                 Xmlt.xml_take sub
                                   (\ c ->
                                     Xmlt.xml_return
                                       (Nonloop_Impl.Pat_InitPump a b c))))))
                       (Xmlt.xml_or
                         (Xmlt.xml_do "initialPumpingContext"
                           (Xmlt.xml_take pat
                             (\ a ->
                               Xmlt.xml_take sub
                                 (\ b ->
                                   Xmlt.xml_take CPF_Input_Parser.pos
                                     (\ c ->
                                       Xmlt.xml_take var
 (\ d -> Xmlt.xml_return (Nonloop_Impl.Pat_InitPumpCtxt a b c d)))))))
                         (Xmlt.xml_or
                           (Xmlt.xml_do "equivalence"
                             (Xmlt.xml_take pat
                               (\ a ->
                                 Xmlt.xml_take
                                   (Xmlt.xml_or (Xmlt.xml_leaf "left" True)
                                     (Xmlt.xml_leaf "right" False))
                                   (\ b ->
                                     Xmlt.xml_take
                                       (pat_eqv_prf xml2name termIndexMap)
                                       (\ c ->
 Xmlt.xml_return (Nonloop_Impl.Pat_Equiv a b c))))))
                           (Xmlt.xml_or
                             (Xmlt.xml_do "narrowing"
                               (Xmlt.xml_take pat
                                 (\ a ->
                                   Xmlt.xml_take pat
                                     (\ b ->
                                       Xmlt.xml_take CPF_Input_Parser.pos
 (\ c -> Xmlt.xml_return (Nonloop_Impl.Pat_Narrow a b c))))))
                             (Xmlt.xml_or
                               (Xmlt.xml_do "instantiation"
                                 (Xmlt.xml_take pat
                                   (\ a ->
                                     Xmlt.xml_take sub
                                       (\ b ->
 Xmlt.xml_take
   (Xmlt.xml_or (Xmlt.xml_leaf "base" Nonloop_Impl.Pat_Base)
     (Xmlt.xml_or (Xmlt.xml_leaf "pumping" Nonloop_Impl.Pat_Pump)
       (Xmlt.xml_leaf "closing" Nonloop_Impl.Pat_Close)))
   (\ c -> Xmlt.xml_return (Nonloop_Impl.Pat_Inst a b c))))))
                               (Xmlt.xml_or
                                 (Xmlt.xml_do "instantiationPumping"
                                   (Xmlt.xml_take pat
                                     (\ a ->
                                       Xmlt.xml_take (Xmlt.xml_nat "power")
 (\ b -> Xmlt.xml_return (Nonloop_Impl.Pat_Exp_Sigma a b)))))
                                 (Xmlt.xml_do "rewriting"
                                   (Xmlt.xml_take pat
                                     (\ a ->
                                       Xmlt.xml_take
 (rsteps xml2name termIndexMap ruleMap)
 (\ b ->
   Xmlt.xml_take
     (Xmlt.xml_or (Xmlt.xml_leaf "base" (Nonloop_Impl.Pat_Base, []))
       (Xmlt.xml_or
         (Xmlt.xml_do "pumping"
           (Xmlt.xml_take var
             (\ v -> Xmlt.xml_return (Nonloop_Impl.Pat_Pump, v))))
         (Xmlt.xml_do "closing"
           (Xmlt.xml_take var
             (\ v -> Xmlt.xml_return (Nonloop_Impl.Pat_Close, v))))))
     (\ (po, va) ->
       Xmlt.xml_return (Nonloop_Impl.Pat_Rewr a b po va)))))))))))))
                   Xmlt.xml_return)))
         x;

nonloop ::
  forall a b.
    (Compare.Compare_order a, Shows_Literal.Showl a, Compare.Compare_order b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term (Labelings.Lab a b)
 [Arith.Char],
Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Nonloop_Impl.Non_loop_prf (Labelings.Lab a b) [Arith.Char]);
nonloop xml2name termIndexMap ruleMap =
  Xmlt.xml_do "nonLoop"
    (Xmlt.xml_take (pat_rule_prf xml2name termIndexMap ruleMap)
      (\ a ->
        Xmlt.xml_take (subst xml2name termIndexMap)
          (\ b ->
            Xmlt.xml_take (subst xml2name termIndexMap)
              (\ c ->
                Xmlt.xml_take (Xmlt.xml_nat "natural")
                  (\ d ->
                    Xmlt.xml_take (Xmlt.xml_nat "natural")
                      (\ e ->
                        Xmlt.xml_take CPF_Input_Parser.pos
                          (\ f ->
                            Xmlt.xml_return
                              (Nonloop_Impl.Non_loop_prf a b c d e f))))))));

xml2dp_nontermination_proof ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term (Labelings.Lab a b)
 [Arith.Char],
Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Check_Nontermination.Dp_nontermination_proof a b [Arith.Char]);
xml2dp_nontermination_proof xml2name termIndexMap ruleMap x =
  Xmlt.xml_do "dpNonterminationProof"
    (Xmlt.xml_take
      (Xmlt.xml_or
        (Xmlt.xml_do "dpRuleRemoval"
          (Xmlt.xml_take
            (Xmlt.xml_do "dps"
              (Xmlt.xml_take
                (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                (\ xa -> Xmlt.xml_return (id xa))))
            (\ p ->
              Xmlt.xml_take
                (Xmlt.xml_do "trs"
                  (Xmlt.xml_take
                    (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                    (\ xa -> Xmlt.xml_return (id xa))))
                (\ r ->
                  Xmlt.xml_take
                    (xml2dp_nontermination_proof xml2name termIndexMap ruleMap)
                    (\ prf ->
                      Xmlt.xml_return
                        (Check_Nontermination.DP_Rule_Removal
                          (Nontermination_Impl.Rule_removal_nonterm_dp_prf p r)
                          prf))))))
        (Xmlt.xml_or
          (Xmlt.xml_do "loop"
            (Xmlt.xml_take (relsteps xml2name termIndexMap ruleMap)
              (\ (s, rseq) ->
                Xmlt.xml_take (subst xml2name termIndexMap)
                  (\ sigma ->
                    Xmlt.xml_take (ctxt xml2name termIndexMap)
                      (\ c ->
                        Xmlt.xml_return
                          (Check_Nontermination.DP_Loop
                            (Loops_Impl.DP_loop_prf s rseq sigma c)))))))
          (Xmlt.xml_or
            (Xmlt.xml_change (nonloop xml2name termIndexMap ruleMap)
              (Xmlt.xml_return . Check_Nontermination.DP_Nonloop))
            (Xmlt.xml_or
              (Xmlt.xml_do "innermostLhssRemovalProc"
                (Xmlt.xml_take
                  (CPF_Input_Parser.innermostLhss xml2name termIndexMap)
                  (\ q ->
                    Xmlt.xml_take
                      (xml2dp_nontermination_proof xml2name termIndexMap
                        ruleMap)
                      (\ p ->
                        Xmlt.xml_return
                          (Check_Nontermination.DP_Q_Reduction
                            (Q_Reduction_Nonterm_Impl.DP_q_reduction_nonterm_prf
                              q)
                            p)))))
              (Xmlt.xml_or
                (Xmlt.xml_do "innermostLhssIncreaseProc"
                  (Xmlt.xml_take
                    (CPF_Input_Parser.innermostLhss xml2name termIndexMap)
                    (\ q ->
                      Xmlt.xml_take
                        (xml2dp_nontermination_proof xml2name termIndexMap
                          ruleMap)
                        (\ p ->
                          Xmlt.xml_return
                            (Check_Nontermination.DP_Q_Increase
                              (Nontermination_Impl.Q_increase_nonterm_dp_prf q)
                              p)))))
                (Xmlt.xml_or
                  (Xmlt.xml_do "instantiationProc"
                    (Xmlt.xml_take
                      (Xmlt.xml_do "dps"
                        (Xmlt.xml_take
                          (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                          (\ xa -> Xmlt.xml_return (id xa))))
                      (\ p ->
                        Xmlt.xml_take
                          (xml2dp_nontermination_proof xml2name termIndexMap
                            ruleMap)
                          (\ prf ->
                            Xmlt.xml_return
                              (Check_Nontermination.DP_Instantiation
                                (Instantiation_Impl.Instantiation_complete_proc_prf
                                  p)
                                prf)))))
                  (Xmlt.xml_or
                    (Xmlt.xml_do "narrowingProc"
                      (Xmlt.xml_take
                        (CPF_Input_Parser.rule xml2name termIndexMap ruleMap)
                        (\ st ->
                          Xmlt.xml_take CPF_Input_Parser.pos
                            (\ po ->
                              Xmlt.xml_take
                                (Xmlt.xml_do "narrowings"
                                  (Xmlt.xml_take
                                    (CPF_Input_Parser.rules xml2name
                                      termIndexMap ruleMap)
                                    (\ xa -> Xmlt.xml_return (id xa))))
                                (\ p ->
                                  Xmlt.xml_take
                                    (xml2dp_nontermination_proof xml2name
                                      termIndexMap ruleMap)
                                    (\ prf ->
                                      Xmlt.xml_return
(Check_Nontermination.DP_Narrowing
  (Narrowing_Impl.Narrowing_complete_proc_prf st po p) prf)))))))
                    (Xmlt.xml_or
                      (Xmlt.xml_do "rewritingProc"
                        (Xmlt.xml_take
                          (CPF_Input_Parser.rule xml2name termIndexMap ruleMap)
                          (\ (s, t) ->
                            Xmlt.xml_take (rstep xml2name termIndexMap ruleMap)
                              (\ (p, (lr, ta)) ->
                                Xmlt.xml_take
                                  (CPF_Input_Parser.rule xml2name termIndexMap
                                    ruleMap)
                                  (\ st ->
                                    Xmlt.xml_take
                                      (Xmlt.xml_do "usableRules"
(Xmlt.xml_take (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
  (\ xa -> Xmlt.xml_return (id xa))))
                                      (\ u ->
Xmlt.xml_take (xml2dp_nontermination_proof xml2name termIndexMap ruleMap)
  (\ prf ->
    Xmlt.xml_return
      (Check_Nontermination.DP_Rewriting
        (Rewriting_Impl.Rewriting_complete_proc_prf (Just u) (s, t) (s, ta) st
          lr p)
        prf))))))))
                      (Xmlt.xml_or
                        (Xmlt.xml_do "switchFullStrategyProc"
                          (Xmlt.xml_take (wcr_proof xml2name termIndexMap)
                            (\ a ->
                              Xmlt.xml_take
                                (xml2dp_nontermination_proof xml2name
                                  termIndexMap ruleMap)
                                (\ b ->
                                  Xmlt.xml_return
                                    (Check_Nontermination.DP_Termination_Switch
                                      a b)))))
                        (Xmlt.xml_or
                          (Xmlt.xml_do "infinitenessAssumption"
                            (Xmlt.xml_take
                              (xml2dp_input xml2name termIndexMap ruleMap False)
                              (\ qdp ->
                                Xmlt.xml_return
                                  (Check_Nontermination.DP_Assume_Infinite qdp
                                    []))))
                          (Xmlt.xml_do "unknownProof"
                            (Xmlt.xml_take (Xmlt.xml_text "description")
                              (\ _ ->
                                Xmlt.xml_take
                                  (xml2dp_input xml2name termIndexMap ruleMap
                                    False)
                                  (\ b ->
                                    Xmlt.xml_take_many_sub [] Arith.zero_nat
                                      Extended_Nat.Infinity_enat
                                      (\ xa -> Strict_Sum.right (fst xa))
                                      (\ _ ->
Xmlt.xml_return (Check_Nontermination.DP_Assume_Infinite b []))))))))))))))))
      (\ xa -> Xmlt.xml_return (id xa)))
    x;

xml2inn_nt_trs_assm :: forall a. a;
xml2inn_nt_trs_assm = error "undefined";

uncurry_info ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
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
                                       ([([Arith.Char], [Arith.Char])],
 (Bool, ([String], [String])))) ->
                                       Strict_Sum.Sum_bot
 (Xmlt.Xml_error String)
 (a, ([((a, Arith.Nat), [a])],
       ([(Term_Rewriting.Term a [Arith.Char],
           Term_Rewriting.Term a [Arith.Char])],
         [(Term_Rewriting.Term a [Arith.Char],
            Term_Rewriting.Term a [Arith.Char])])));
uncurry_info xml2name termIndexMap ruleMap =
  Xmlt.xml_do "uncurryInformation"
    (Xmlt.xml_take xml2name
      (\ a ->
        Xmlt.xml_take
          (Xmlt.xml_do "uncurriedSymbols"
            (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
              (Xmlt.xml_do "uncurriedSymbolEntry"
                (Xmlt.xml_take xml2name
                  (\ f ->
                    Xmlt.xml_take (Xmlt.xml_nat "arity")
                      (\ n ->
                        Xmlt.xml_take_many_sub [] Arith.zero_nat
                          Extended_Nat.Infinity_enat xml2name
                          (\ fs -> Xmlt.xml_return ((f, n), fs))))))
              Xmlt.xml_return))
          (\ sml ->
            Xmlt.xml_take
              (Xmlt.xml_do "uncurryRules"
                (Xmlt.xml_take
                  (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                  (\ x -> Xmlt.xml_return (id x))))
              (\ u ->
                Xmlt.xml_take
                  (Xmlt.xml_do "etaRules"
                    (Xmlt.xml_take
                      (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                      (\ x -> Xmlt.xml_return (id x))))
                  (\ e -> Xmlt.xml_return (a, (sml, (u, e))))))));

string ::
  forall a b.
    (Compare.Compare_order a, Shows_Literal.Showl a, Compare.Compare_order b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  (Xml.Xml,
                                    ([([Arith.Char], [Arith.Char])],
                                      (Bool, ([String], [String])))) ->
                                    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                      [Labelings.Lab a b];
string xml2name =
  Xmlt.xml_do "string"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      xml2name (\ a -> Xmlt.xml_return (id a)));

word_pattern ::
  forall a b.
    (Compare.Compare_order a, Shows_Literal.Showl a, Compare.Compare_order b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  (Xml.Xml,
                                    ([([Arith.Char], [Arith.Char])],
                                      (Bool, ([String], [String])))) ->
                                    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                      ([Labelings.Lab a b],
((Arith.Nat, (Arith.Nat, [Labelings.Lab a b])), [Labelings.Lab a b]));
word_pattern xml2name =
  Xmlt.xml_do "wordPattern"
    (Xmlt.xml_take (string xml2name)
      (\ l ->
        Xmlt.xml_take (string xml2name)
          (\ m ->
            Xmlt.xml_take (Xmlt.xml_nat "factor")
              (\ f ->
                Xmlt.xml_take (Xmlt.xml_nat "constant")
                  (\ c ->
                    Xmlt.xml_take (string xml2name)
                      (\ r -> Xmlt.xml_return (l, ((f, (c, m)), r))))))));

derivation_pattern ::
  forall a b.
    (Compare.Compare_order a, Shows_Literal.Showl a, Compare.Compare_order b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  (Xml.Xml,
                                    ([([Arith.Char], [Arith.Char])],
                                      (Bool, ([String], [String])))) ->
                                    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                      (([Labelings.Lab a b],
 ((Arith.Nat, (Arith.Nat, [Labelings.Lab a b])), [Labelings.Lab a b])),
([Labelings.Lab a b],
  ((Arith.Nat, (Arith.Nat, [Labelings.Lab a b])), [Labelings.Lab a b])));
derivation_pattern xml2name =
  Xmlt.xml_do "derivationPattern"
    (Xmlt.xml_take (word_pattern xml2name)
      (\ a ->
        Xmlt.xml_take (word_pattern xml2name) (\ b -> Xmlt.xml_return (a, b))));

oc_srs ::
  forall a b.
    (Compare.Compare_order a, Shows_Literal.Showl a, Compare.Compare_order b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  (Xml.Xml,
                                    ([([Arith.Char], [Arith.Char])],
                                      (Bool, ([String], [String])))) ->
                                    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                      ([Labelings.Lab a b],
[Labelings.Lab a b]);
oc_srs xml2name =
  Xmlt.xml_do "overlapClosureSRS"
    (Xmlt.xml_take (string xml2name)
      (\ a -> Xmlt.xml_take (string xml2name) (\ b -> Xmlt.xml_return (a, b))));

derivation_pattern_proof ::
  forall a b.
    (Compare.Compare_order a, Shows_Literal.Showl a, Compare.Compare_order b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  (Xml.Xml,
                                    ([([Arith.Char], [Arith.Char])],
                                      (Bool, ([String], [String])))) ->
                                    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                      (Nonloop_SRS.Dp_proof_step
(Labelings.Lab a b));
derivation_pattern_proof xml2name =
  let {
    oc = oc_srs xml2name;
    dp = derivation_pattern xml2name;
    s = string xml2name;
  } in Xmlt.xml_do "derivationPatternProof"
         (Xmlt.xml_take
           (Xmlt.xml_or
             (Xmlt.xml_do "OC1"
               (Xmlt.xml_take oc
                 (\ a ->
                   Xmlt.xml_take (Xmlt.xml_bool "isPair")
                     (\ b -> Xmlt.xml_return (Nonloop_SRS.OC1 a b)))))
             (Xmlt.xml_or
               (Xmlt.xml_do "OC2"
                 (Xmlt.xml_take oc
                   (\ a ->
                     Xmlt.xml_take oc
                       (\ b ->
                         Xmlt.xml_take oc
                           (\ c ->
                             Xmlt.xml_take s
                               (\ d ->
                                 Xmlt.xml_take s
                                   (\ e ->
                                     Xmlt.xml_take s
                                       (\ f ->
 Xmlt.xml_return (Nonloop_SRS.OC2 a b c d e f)))))))))
               (Xmlt.xml_or
                 (Xmlt.xml_do "OC2prime"
                   (Xmlt.xml_take oc
                     (\ a ->
                       Xmlt.xml_take oc
                         (\ b ->
                           Xmlt.xml_take oc
                             (\ c ->
                               Xmlt.xml_take s
                                 (\ d ->
                                   Xmlt.xml_take s
                                     (\ e ->
                                       Xmlt.xml_take s
 (\ f -> Xmlt.xml_return (Nonloop_SRS.OC2p a b c d e f)))))))))
                 (Xmlt.xml_or
                   (Xmlt.xml_do "OC3"
                     (Xmlt.xml_take oc
                       (\ a ->
                         Xmlt.xml_take oc
                           (\ b ->
                             Xmlt.xml_take oc
                               (\ c ->
                                 Xmlt.xml_take s
                                   (\ d ->
                                     Xmlt.xml_take s
                                       (\ e ->
 Xmlt.xml_return (Nonloop_SRS.OC3 a b c d e))))))))
                   (Xmlt.xml_or
                     (Xmlt.xml_do "OC3prime"
                       (Xmlt.xml_take oc
                         (\ a ->
                           Xmlt.xml_take oc
                             (\ b ->
                               Xmlt.xml_take oc
                                 (\ c ->
                                   Xmlt.xml_take s
                                     (\ d ->
                                       Xmlt.xml_take s
 (\ e -> Xmlt.xml_return (Nonloop_SRS.OC3p a b c d e))))))))
                     (Xmlt.xml_or
                       (Xmlt.xml_do "OCintoDP1"
                         (Xmlt.xml_take dp
                           (\ a ->
                             Xmlt.xml_take oc
                               (\ b ->
                                 Xmlt.xml_return (Nonloop_SRS.OCDP1 a b)))))
                       (Xmlt.xml_or
                         (Xmlt.xml_do "OCintoDP2"
                           (Xmlt.xml_take dp
                             (\ a ->
                               Xmlt.xml_take oc
                                 (\ b ->
                                   Xmlt.xml_return (Nonloop_SRS.OCDP2 a b)))))
                         (Xmlt.xml_or
                           (Xmlt.xml_do "equivalent"
                             (Xmlt.xml_take dp
                               (\ a ->
                                 Xmlt.xml_take dp
                                   (\ b ->
                                     Xmlt.xml_return (Nonloop_SRS.WPEQ a b)))))
                           (Xmlt.xml_or
                             (Xmlt.xml_do "lift"
                               (Xmlt.xml_take dp
                                 (\ a ->
                                   Xmlt.xml_take dp
                                     (\ b ->
                                       Xmlt.xml_return
 (Nonloop_SRS.Lift a b)))))
                             (Xmlt.xml_or
                               (Xmlt.xml_do "DP_OC_1_1"
                                 (Xmlt.xml_take dp
                                   (\ a ->
                                     Xmlt.xml_take dp
                                       (\ b ->
 Xmlt.xml_take oc
   (\ c ->
     Xmlt.xml_take s
       (\ d ->
         Xmlt.xml_take s
           (\ e -> Xmlt.xml_return (Nonloop_SRS.DPOC1_1 a b c d e))))))))
                               (Xmlt.xml_or
                                 (Xmlt.xml_do "DP_OC_1_2"
                                   (Xmlt.xml_take dp
                                     (\ a ->
                                       Xmlt.xml_take dp
 (\ b ->
   Xmlt.xml_take oc
     (\ c ->
       Xmlt.xml_take s
         (\ d ->
           Xmlt.xml_take s
             (\ e ->
               Xmlt.xml_take s
                 (\ f ->
                   Xmlt.xml_return (Nonloop_SRS.DPOC1_2 a b c d e f)))))))))
                                 (Xmlt.xml_or
                                   (Xmlt.xml_do "DP_OC_2"
                                     (Xmlt.xml_take dp
                                       (\ a ->
 Xmlt.xml_take dp
   (\ b ->
     Xmlt.xml_take oc
       (\ c ->
         Xmlt.xml_take s
           (\ d ->
             Xmlt.xml_take s
               (\ e -> Xmlt.xml_return (Nonloop_SRS.DPOC2 a b c d e))))))))
                                   (Xmlt.xml_or
                                     (Xmlt.xml_do "DP_OC_3_1"
                                       (Xmlt.xml_take dp
 (\ a ->
   Xmlt.xml_take dp
     (\ b ->
       Xmlt.xml_take oc
         (\ c ->
           Xmlt.xml_take s
             (\ d ->
               Xmlt.xml_take s
                 (\ e -> Xmlt.xml_return (Nonloop_SRS.DPOC3_1 a b c d e))))))))
                                     (Xmlt.xml_or
                                       (Xmlt.xml_do "DP_OC_3_2"
 (Xmlt.xml_take dp
   (\ a ->
     Xmlt.xml_take dp
       (\ b ->
         Xmlt.xml_take oc
           (\ c ->
             Xmlt.xml_take s
               (\ d ->
                 Xmlt.xml_take s
                   (\ e ->
                     Xmlt.xml_take s
                       (\ f ->
                         Xmlt.xml_return
                           (Nonloop_SRS.DPOC3_2 a b c d e f)))))))))
                                       (Xmlt.xml_or
 (Xmlt.xml_do "DP_DP_1_1"
   (Xmlt.xml_take dp
     (\ a ->
       Xmlt.xml_take dp
         (\ b ->
           Xmlt.xml_take dp
             (\ c ->
               Xmlt.xml_take s
                 (\ d ->
                   Xmlt.xml_take s
                     (\ e ->
                       Xmlt.xml_return (Nonloop_SRS.DPDP1_1 a b c d e))))))))
 (Xmlt.xml_or
   (Xmlt.xml_do "DP_DP_1_2"
     (Xmlt.xml_take dp
       (\ a ->
         Xmlt.xml_take dp
           (\ b ->
             Xmlt.xml_take dp
               (\ c ->
                 Xmlt.xml_take s
                   (\ d ->
                     Xmlt.xml_take s
                       (\ e ->
                         Xmlt.xml_return (Nonloop_SRS.DPDP1_2 a b c d e))))))))
   (Xmlt.xml_or
     (Xmlt.xml_do "DP_DP_2_1"
       (Xmlt.xml_take dp
         (\ a ->
           Xmlt.xml_take dp
             (\ b ->
               Xmlt.xml_take dp
                 (\ c ->
                   Xmlt.xml_take s
                     (\ d ->
                       Xmlt.xml_take s
                         (\ e ->
                           Xmlt.xml_return
                             (Nonloop_SRS.DPDP2_1 a b c d e))))))))
     (Xmlt.xml_do "DP_DP_2_2"
       (Xmlt.xml_take dp
         (\ a ->
           Xmlt.xml_take dp
             (\ b ->
               Xmlt.xml_take dp
                 (\ c ->
                   Xmlt.xml_take s
                     (\ d ->
                       Xmlt.xml_take s
                         (\ e ->
                           Xmlt.xml_return
                             (Nonloop_SRS.DPDP2_2 a b c d
                               e)))))))))))))))))))))))))
           (\ x -> Xmlt.xml_return (id x)));

nonloop_srs_reason ::
  forall a b.
    (Compare.Compare_order a, Shows_Literal.Showl a, Compare.Compare_order b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  (Xml.Xml,
                                    ([([Arith.Char], [Arith.Char])],
                                      (Bool, ([String], [String])))) ->
                                    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                      ([Nonloop_SRS.Dp_proof_step
  (Labelings.Lab a b)] ->
Nonloop_SRS.Non_loop_srs_proof (Labelings.Lab a b));
nonloop_srs_reason xml2name =
  Xmlt.xml_or
    (Xmlt.xml_do "selfEmbeddingOC"
      (Xmlt.xml_take (string xml2name)
        (\ a ->
          Xmlt.xml_take (string xml2name)
            (\ b ->
              Xmlt.xml_take (string xml2name)
                (\ c ->
                  Xmlt.xml_return (Nonloop_SRS.SE_OC (b, a ++ b ++ c) a c))))))
    (Xmlt.xml_do "selfEmbeddingDP"
      (Xmlt.xml_take (derivation_pattern xml2name)
        (\ a ->
          Xmlt.xml_take (string xml2name)
            (\ b ->
              Xmlt.xml_take (string xml2name)
                (\ c -> Xmlt.xml_return (Nonloop_SRS.SE_DP a b c))))));

nonloop_srs ::
  forall a b.
    (Compare.Compare_order a, Shows_Literal.Showl a, Compare.Compare_order b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  (Xml.Xml,
                                    ([([Arith.Char], [Arith.Char])],
                                      (Bool, ([String], [String])))) ->
                                    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                      (Nonloop_SRS.Non_loop_srs_proof
(Labelings.Lab a b));
nonloop_srs xml2name =
  Xmlt.xml_do "nonterminatingSRS"
    (Xmlt.xml_take
      (Xmlt.xml_do "derivationPatterns"
        (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
          (derivation_pattern_proof xml2name) (\ a -> Xmlt.xml_return (id a))))
      (\ a ->
        Xmlt.xml_take (nonloop_srs_reason xml2name)
          (\ b -> Xmlt.xml_return (b a))));

closed_criterion ::
  (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
      (Tree_Automata_Impl.Ta_relation [Arith.Char]);
closed_criterion =
  Xmlt.xml_do "criterion"
    (Xmlt.xml_take
      (Xmlt.xml_or
        (Xmlt.xml_leaf "compatibility" Tree_Automata_Impl.Id_Relation)
        (Xmlt.xml_or
          (Xmlt.xml_do "stateCompatibility"
            (Xmlt.xml_take
              (Xmlt.xml_do "relation"
                (Xmlt.xml_take_many_sub [] Arith.zero_nat
                  Extended_Nat.Infinity_enat
                  (Xmlt.xml_do "entry"
                    (Xmlt.xml_take CPF_Input_Parser.state
                      (\ a ->
                        Xmlt.xml_take CPF_Input_Parser.state
                          (\ b -> Xmlt.xml_return (a, b)))))
                  Xmlt.xml_return))
              (\ x -> Xmlt.xml_return (Tree_Automata_Impl.Some_Relation x))))
          (Xmlt.xml_or
            (Xmlt.xml_leaf "decisionProcedure" Tree_Automata_Impl.Decision_Proc)
            (Xmlt.xml_leaf "decisionProcedureOld"
              Tree_Automata_Impl.Decision_Proc_Old))))
      Xmlt.xml_return);

not_wn_ta ::
  forall a b.
    (Compare.Compare_order a, Shows_Literal.Showl a, Compare.Compare_order b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  (Xml.Xml,
                                    ([([Arith.Char], [Arith.Char])],
                                      (Bool, ([String], [String])))) ->
                                    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                      (Not_WN_Tree_Automaton_Impl.Not_wn_ta_prf
(Labelings.Lab a b) [Arith.Char]);
not_wn_ta xml2name =
  Xmlt.xml_do "notWNTreeAutomaton"
    (Xmlt.xml_take
      (CPF_Input_Parser.tree_automaton
        (CPF_Input_Parser.ta_normal_lhs xml2name))
      (\ a ->
        Xmlt.xml_take closed_criterion
          (\ b ->
            Xmlt.xml_return (Not_WN_Tree_Automaton_Impl.Not_wn_ta_prf a b))));

renaming ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
                                  ([([Arith.Char], [Arith.Char])],
                                    (Bool, ([String], [String])))) ->
                                 Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                   a) ->
                                 (Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                   Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                     [(a, a)];
renaming xml2name =
  Xmlt.xml_do "renaming"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (Xmlt.xml_do "renamingEntry"
        (Xmlt.xml_take xml2name
          (\ a -> Xmlt.xml_take xml2name (\ b -> Xmlt.xml_return (a, b)))))
      Xmlt.xml_return);

xml2trs_nontermination_proof ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term (Labelings.Lab a b)
 [Arith.Char],
Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Check_Nontermination.Trs_nontermination_proof a b [Arith.Char]);
xml2trs_nontermination_proof xml2name termIndexMap ruleMap x =
  Xmlt.xml_do "trsNonterminationProof"
    (Xmlt.xml_take
      (Xmlt.xml_or
        (Xmlt.xml_do "variableConditionViolated"
          (Xmlt.xml_return Check_Nontermination.TRS_Not_Well_Formed))
        (Xmlt.xml_or
          (Xmlt.xml_change (loop xml2name termIndexMap ruleMap)
            (\ (s, (rseq, (sigma, c))) ->
              Xmlt.xml_return
                (Check_Nontermination.TRS_Loop
                  (Loops_Impl.TRS_loop_prf s
                    (map (\ (xa, (y, (_, z))) -> (xa, (y, z))) rseq) sigma c))))
          (Xmlt.xml_or
            (Xmlt.xml_change (nonloop xml2name termIndexMap ruleMap)
              (Xmlt.xml_return . Check_Nontermination.TRS_Nonloop))
            (Xmlt.xml_or
              (Xmlt.xml_change (nonloop_srs xml2name)
                (Xmlt.xml_return . Check_Nontermination.TRS_Nonloop_SRS))
              (Xmlt.xml_or
                (Xmlt.xml_do "rightGroundNontermination"
                  (Xmlt.xml_return Check_Nontermination.TRS_Not_RG_Decision))
                (Xmlt.xml_or
                  (Xmlt.xml_do "ruleRemoval"
                    (Xmlt.xml_take
                      (Xmlt.xml_do "trs"
                        (Xmlt.xml_take
                          (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                          (\ xa -> Xmlt.xml_return (id xa))))
                      (\ r ->
                        Xmlt.xml_take
                          (xml2trs_nontermination_proof xml2name termIndexMap
                            ruleMap)
                          (\ p ->
                            Xmlt.xml_return
                              (Check_Nontermination.TRS_Rule_Removal
                                (Nontermination_Impl.Rule_removal_nonterm_trs_prf
                                  r)
                                p)))))
                  (Xmlt.xml_or
                    (Xmlt.xml_do "dpTrans"
                      (Xmlt.xml_take
                        (Xmlt.xml_do "dps"
                          (Xmlt.xml_take
                            (CPF_Input_Parser.rules xml2name termIndexMap
                              ruleMap)
                            (\ xa -> Xmlt.xml_return (id xa))))
                        (\ p ->
                          Xmlt.xml_take
                            (xml2dp_nontermination_proof xml2name termIndexMap
                              ruleMap)
                            (\ c ->
                              Xmlt.xml_return
                                (Check_Nontermination.TRS_DP_Trans
                                  (Nontermination_Impl.DP_trans_nontermination_tt_prf
                                    p)
                                  c)))))
                    (Xmlt.xml_or
                      (Xmlt.xml_do "stringReversal"
                        (Xmlt.xml_take
                          (Xmlt.xml_do "trs"
                            (Xmlt.xml_take
                              (CPF_Input_Parser.rules xml2name termIndexMap
                                ruleMap)
                              (\ xa -> Xmlt.xml_return (id xa))))
                          (\ _ ->
                            Xmlt.xml_take
                              (xml2trs_nontermination_proof xml2name
                                termIndexMap ruleMap)
                              (\ p ->
                                Xmlt.xml_return
                                  (Check_Nontermination.TRS_String_Reversal
                                    p)))))
                      (Xmlt.xml_or
                        (Xmlt.xml_do "constantToUnary"
                          (Xmlt.xml_take CPF_Input_Parser.plain_var
                            (\ v ->
                              Xmlt.xml_take (renaming xml2name)
                                (\ ren ->
                                  Xmlt.xml_take
                                    (Xmlt.xml_do "trs"
                                      (Xmlt.xml_take
(CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
(\ xa -> Xmlt.xml_return (id xa))))
                                    (\ s ->
                                      Xmlt.xml_take
(xml2trs_nontermination_proof xml2name termIndexMap ruleMap)
(\ p ->
  Xmlt.xml_return
    (Check_Nontermination.TRS_Constant_String
      (Monadic_Rewriting_Impl.Const_string_complete_proof v ren s) p)))))))
                        (Xmlt.xml_or
                          (Xmlt.xml_do "innermostLhssIncrease"
                            (Xmlt.xml_take
                              (CPF_Input_Parser.innermostLhss xml2name
                                termIndexMap)
                              (\ q ->
                                Xmlt.xml_take
                                  (xml2trs_nontermination_proof xml2name
                                    termIndexMap ruleMap)
                                  (\ r ->
                                    Xmlt.xml_return
                                      (Check_Nontermination.TRS_Q_Increase
(Nontermination_Impl.Q_increase_nonterm_trs_prf q) r)))))
                          (Xmlt.xml_or
                            (Xmlt.xml_do "switchFullStrategy"
                              (Xmlt.xml_take (wcr_proof xml2name termIndexMap)
                                (\ a ->
                                  Xmlt.xml_take
                                    (xml2trs_nontermination_proof xml2name
                                      termIndexMap ruleMap)
                                    (\ b ->
                                      Xmlt.xml_return
(Check_Nontermination.TRS_Termination_Switch a b)))))
                            (Xmlt.xml_or
                              (Xmlt.xml_do "uncurry"
                                (Xmlt.xml_take
                                  (uncurry_info xml2name termIndexMap ruleMap)
                                  (\ i ->
                                    Xmlt.xml_take
                                      (Xmlt.xml_do "trs"
(Xmlt.xml_take (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
  (\ xa -> Xmlt.xml_return (id xa))))
                                      (\ r ->
Xmlt.xml_take (xml2trs_nontermination_proof xml2name termIndexMap ruleMap)
  (\ p ->
    Xmlt.xml_return
      (Check_Nontermination.TRS_Uncurry (Uncurry_Impl.Uncurry_nt_proof i r)
        p))))))
                              (Xmlt.xml_or
                                (Xmlt.xml_change (not_wn_ta xml2name)
                                  (Xmlt.xml_return .
                                    Check_Nontermination.TRS_Not_WN_Tree_Automaton))
                                (Xmlt.xml_or
                                  (Xmlt.xml_do "nonterminationAssumption"
                                    (Xmlt.xml_take xml2inn_nt_trs_assm
                                      (\ qtrs ->
Xmlt.xml_return (Check_Nontermination.TRS_Assume_Not_SN qtrs []))))
                                  (Xmlt.xml_do "unknownProof"
                                    (Xmlt.xml_take (Xmlt.xml_text "description")
                                      (\ _ ->
Xmlt.xml_take xml2inn_nt_trs_assm
  (\ b ->
    Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (\ xa -> Strict_Sum.right (fst xa))
      (\ _ ->
        Xmlt.xml_return
          (Check_Nontermination.TRS_Assume_Not_SN b []))))))))))))))))))))
      (\ xa -> Xmlt.xml_return (id xa)))
    x;

xml2inn_rel_nt_trs_assm :: forall a. a;
xml2inn_rel_nt_trs_assm = error "undefined";

xml2reltrs_nontermination_proof ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term (Labelings.Lab a b)
 [Arith.Char],
Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Check_Nontermination.Reltrs_nontermination_proof a b [Arith.Char]);
xml2reltrs_nontermination_proof xml2name termIndexMap ruleMap x =
  Xmlt.xml_do "relativeNonterminationProof"
    (Xmlt.xml_take
      (Xmlt.xml_or
        (Xmlt.xml_do "variableConditionViolated"
          (Xmlt.xml_return Check_Nontermination.Rel_Not_Well_Formed))
        (Xmlt.xml_or
          (Xmlt.xml_change (loop xml2name termIndexMap ruleMap)
            (\ (s, (rseq, (sigma, c))) ->
              Xmlt.xml_return
                (Check_Nontermination.Rel_Loop
                  (Loops_Impl.Rel_trs_loop_prf s rseq sigma c))))
          (Xmlt.xml_or
            (Xmlt.xml_do "ignoreRelativePart"
              (Xmlt.xml_take
                (xml2trs_nontermination_proof xml2name termIndexMap ruleMap)
                (\ prf ->
                  Xmlt.xml_return (Check_Nontermination.Rel_R_Not_SN prf))))
            (Xmlt.xml_or
              (Xmlt.xml_do "ruleRemoval"
                (Xmlt.xml_take
                  (Xmlt.xml_do "trs"
                    (Xmlt.xml_take
                      (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                      (\ xa -> Xmlt.xml_return (id xa))))
                  (\ r ->
                    Xmlt.xml_take
                      (Xmlt.xml_do "trs"
                        (Xmlt.xml_take
                          (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                          (\ xa -> Xmlt.xml_return (id xa))))
                      (\ s ->
                        Xmlt.xml_take
                          (xml2reltrs_nontermination_proof xml2name termIndexMap
                            ruleMap)
                          (\ p ->
                            Xmlt.xml_return
                              (Check_Nontermination.Rel_Rule_Removal
                                (Nontermination_Impl.Rule_removal_nonterm_reltrs_prf
                                  r s)
                                p))))))
              (Xmlt.xml_or
                (Xmlt.xml_do "stringReversal"
                  (Xmlt.xml_take
                    (Xmlt.xml_do "trs"
                      (Xmlt.xml_take
                        (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                        (\ xa -> Xmlt.xml_return (Just xa))))
                    (\ _ ->
                      Xmlt.xml_take
                        (Xmlt.xml_do "trs"
                          (Xmlt.xml_take
                            (CPF_Input_Parser.rules xml2name termIndexMap
                              ruleMap)
                            (\ xa -> Xmlt.xml_return (Just xa))))
                        (\ _ ->
                          Xmlt.xml_take
                            (xml2reltrs_nontermination_proof xml2name
                              termIndexMap ruleMap)
                            (\ p ->
                              Xmlt.xml_return
                                (Check_Nontermination.Rel_TRS_String_Reversal
                                  p))))))
                (Xmlt.xml_or
                  (Xmlt.xml_do "nonterminationAssumption"
                    (Xmlt.xml_take xml2inn_rel_nt_trs_assm
                      (\ qtrs ->
                        Xmlt.xml_return
                          (Check_Nontermination.Rel_TRS_Assume_Not_SN qtrs
                            []))))
                  (Xmlt.xml_do "unknownProof"
                    (Xmlt.xml_take (Xmlt.xml_text "description")
                      (\ _ ->
                        Xmlt.xml_take xml2inn_rel_nt_trs_assm
                          (\ b ->
                            Xmlt.xml_take_many_sub [] Arith.zero_nat
                              Extended_Nat.Infinity_enat
                              (\ xa -> Strict_Sum.right (fst xa))
                              (\ _ ->
                                Xmlt.xml_return
                                  (Check_Nontermination.Rel_TRS_Assume_Not_SN b
                                    []))))))))))))
      (\ xa -> Xmlt.xml_return (id xa)))
    x;

xml2ordered_completion_step ::
  forall a b.
    (Compare.Compare_order a, Shows_Literal.Showl a, Compare.Compare_order b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    (Xml.Xml,
                                      ([([Arith.Char], [Arith.Char])],
(Bool, ([String], [String])))) ->
                                      Strict_Sum.Sum_bot (Xmlt.Xml_error String)
(Ordered_Completion_Impl.Oc_irule (Labelings.Lab a b) [Arith.Char]);
xml2ordered_completion_step xml2name termIndexMap =
  Xmlt.xml_or
    (Xmlt.xml_do "deduce"
      (Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
        (\ a ->
          Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
            (\ b ->
              Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
                (\ c ->
                  Xmlt.xml_return (Ordered_Completion_Impl.OC_Deduce a b c))))))
    (Xmlt.xml_or
      (Xmlt.xml_do "orientl"
        (Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
          (\ a ->
            Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
              (\ b ->
                Xmlt.xml_return (Ordered_Completion_Impl.OC_Orientl a b)))))
      (Xmlt.xml_or
        (Xmlt.xml_do "orientr"
          (Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
            (\ a ->
              Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
                (\ b ->
                  Xmlt.xml_return (Ordered_Completion_Impl.OC_Orientr a b)))))
        (Xmlt.xml_or
          (Xmlt.xml_do "delete"
            (Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
              (\ x -> Xmlt.xml_return (Ordered_Completion_Impl.OC_Delete x))))
          (Xmlt.xml_or
            (Xmlt.xml_do "compose"
              (Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
                (\ a ->
                  Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
                    (\ b ->
                      Xmlt.xml_take
                        (CPF_Input_Parser.term xml2name termIndexMap)
                        (\ c ->
                          Xmlt.xml_return
                            (Ordered_Completion_Impl.OC_Compose a b c))))))
            (Xmlt.xml_or
              (Xmlt.xml_do "simplifyl"
                (Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
                  (\ a ->
                    Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
                      (\ b ->
                        Xmlt.xml_take
                          (CPF_Input_Parser.term xml2name termIndexMap)
                          (\ c ->
                            Xmlt.xml_return
                              (Ordered_Completion_Impl.OC_Simplifyl a b c))))))
              (Xmlt.xml_or
                (Xmlt.xml_do "simplifyr"
                  (Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
                    (\ a ->
                      Xmlt.xml_take
                        (CPF_Input_Parser.term xml2name termIndexMap)
                        (\ b ->
                          Xmlt.xml_take
                            (CPF_Input_Parser.term xml2name termIndexMap)
                            (\ c ->
                              Xmlt.xml_return
                                (Ordered_Completion_Impl.OC_Simplifyr a b
                                  c))))))
                (Xmlt.xml_do "collapse"
                  (Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
                    (\ a ->
                      Xmlt.xml_take
                        (CPF_Input_Parser.term xml2name termIndexMap)
                        (\ b ->
                          Xmlt.xml_take
                            (CPF_Input_Parser.term xml2name termIndexMap)
                            (\ c ->
                              Xmlt.xml_return
                                (Ordered_Completion_Impl.OC_Collapse a b
                                  c))))))))))));

xml2ordered_completion_proof ::
  forall a b.
    (Compare.Compare_order a, Shows_Literal.Showl a, Compare.Compare_order b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    (Xml.Xml,
                                      ([([Arith.Char], [Arith.Char])],
(Bool, ([String], [String])))) ->
                                      Strict_Sum.Sum_bot (Xmlt.Xml_error String)
(Ordered_Completion_Impl.Ordered_completion_proof (Labelings.Lab a b)
  [Arith.Char]);
xml2ordered_completion_proof xml2name termIndexMap =
  Xmlt.xml_do "orderedCompletionProof"
    (Xmlt.xml_take
      (Xmlt.xml_do "run"
        (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
          (Xmlt.xml_do "orderedCompletionStep"
            (Xmlt.xml_take (xml2ordered_completion_step xml2name termIndexMap)
              (\ x -> Xmlt.xml_return (id x))))
          (\ a -> Xmlt.xml_return (id a))))
      (\ x -> Xmlt.xml_return (Ordered_Completion_Impl.OKB x)));

xml2cond_constraint ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
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
                                       (Generalized_Usable_Rules.Cond_constraint
 a [Arith.Char]);
xml2cond_constraint xml2name termIndexMap x =
  Xmlt.xml_do "conditionalConstraint"
    (Xmlt.xml_take
      (Xmlt.xml_or
        (Xmlt.xml_do "all"
          (Xmlt.xml_take (Xmlt.xml_text "var")
            (\ a ->
              Xmlt.xml_take (xml2cond_constraint xml2name termIndexMap)
                (\ b ->
                  Xmlt.xml_return (Generalized_Usable_Rules.CC_all a b)))))
        (Xmlt.xml_or
          (Xmlt.xml_do "implication"
            (Xmlt.xml_take (xml2cond_constraint xml2name termIndexMap)
              (\ c ->
                Xmlt.xml_take_many_sub [] Arith.zero_nat
                  Extended_Nat.Infinity_enat
                  (xml2cond_constraint xml2name termIndexMap)
                  (\ cs ->
                    let {
                      ccs = c : cs;
                    } in Xmlt.xml_return
                           (Generalized_Usable_Rules.CC_impl
                             (Arith.take (Arith.size_list cs) ccs)
                             (Arith.last ccs))))))
          (Xmlt.xml_do "constraint"
            (Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
              (\ s ->
                Xmlt.xml_take
                  (Xmlt.xml_or (Xmlt.xml_leaf "rewrite" Nothing)
                    (Xmlt.xml_or (Xmlt.xml_leaf "strict" (Just True))
                      (Xmlt.xml_leaf "nonStrict" (Just False))))
                  (\ rel ->
                    Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
                      (\ t ->
                        Xmlt.xml_return
                          (case rel of {
                            Nothing -> Generalized_Usable_Rules.CC_rewr s t;
                            Just stri ->
                              Generalized_Usable_Rules.CC_cond stri (s, t);
                          }))))))))
      (\ xa -> Xmlt.xml_return (id xa)))
    x;

xml2cond_constraint_prf ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
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
                                       ([([Arith.Char], [Arith.Char])],
 (Bool, ([String], [String])))) ->
                                       Strict_Sum.Sum_bot
 (Xmlt.Xml_error String)
 (Bounded_Increase_Impl.Cond_constraint_prf a [Arith.Char]);
xml2cond_constraint_prf xml2name termIndexMap ruleMap x =
  let {
    cc = xml2cond_constraint xml2name termIndexMap;
  } in Xmlt.xml_do "conditionalConstraintProof"
         (Xmlt.xml_take
           (Xmlt.xml_or (Xmlt.xml_leaf "final" Bounded_Increase_Impl.Final)
             (Xmlt.xml_or
               (Xmlt.xml_do "differentConstructor"
                 (Xmlt.xml_take cc
                   (\ a ->
                     Xmlt.xml_return
                       (Bounded_Increase_Impl.Different_Constructor a))))
               (Xmlt.xml_or
                 (Xmlt.xml_do "sameConstructor"
                   (Xmlt.xml_take cc
                     (\ a ->
                       Xmlt.xml_take cc
                         (\ b ->
                           Xmlt.xml_take
                             (xml2cond_constraint_prf xml2name termIndexMap
                               ruleMap)
                             (\ c ->
                               Xmlt.xml_return
                                 (Bounded_Increase_Impl.Same_Constructor a b
                                   c))))))
                 (Xmlt.xml_or
                   (Xmlt.xml_do "variableEquation"
                     (Xmlt.xml_take (Xmlt.xml_text "var")
                       (\ a ->
                         Xmlt.xml_take
                           (CPF_Input_Parser.term xml2name termIndexMap)
                           (\ b ->
                             Xmlt.xml_take cc
                               (\ c ->
                                 Xmlt.xml_take
                                   (xml2cond_constraint_prf xml2name
                                     termIndexMap ruleMap)
                                   (\ d ->
                                     Xmlt.xml_return
                                       (Bounded_Increase_Impl.Variable_Equation
 a b c d)))))))
                   (Xmlt.xml_or
                     (Xmlt.xml_do "funargIntoVar"
                       (Xmlt.xml_take cc
                         (\ a ->
                           Xmlt.xml_take CPF_Input_Parser.position
                             (\ b ->
                               Xmlt.xml_take (Xmlt.xml_text "var")
                                 (\ c ->
                                   Xmlt.xml_take cc
                                     (\ d ->
                                       Xmlt.xml_take
 (xml2cond_constraint_prf xml2name termIndexMap ruleMap)
 (\ e ->
   Xmlt.xml_return (Bounded_Increase_Impl.Funarg_Into_Var a b c d e))))))))
                     (Xmlt.xml_or
                       (Xmlt.xml_do "simplifyCondition"
                         (Xmlt.xml_take cc
                           (\ a ->
                             Xmlt.xml_take (subst xml2name termIndexMap)
                               (\ b ->
                                 Xmlt.xml_take cc
                                   (\ c ->
                                     Xmlt.xml_take
                                       (xml2cond_constraint_prf xml2name
 termIndexMap ruleMap)
                                       (\ d ->
 Xmlt.xml_return (Bounded_Increase_Impl.Simplify_Condition a b c d)))))))
                       (Xmlt.xml_or
                         (Xmlt.xml_do "induction"
                           (Xmlt.xml_take cc
                             (\ a ->
                               Xmlt.xml_take
                                 (Xmlt.xml_do "conjuncts"
                                   (Xmlt.xml_take_many_sub [] Arith.zero_nat
                                     Extended_Nat.Infinity_enat cc
                                     Xmlt.xml_return))
                                 (\ b ->
                                   Xmlt.xml_take
                                     (Xmlt.xml_do "ruleConstraintProofs"
                                       (Xmlt.xml_take_many_sub [] Arith.zero_nat
 Extended_Nat.Infinity_enat
 (Xmlt.xml_do "ruleConstraintProof"
   (Xmlt.xml_take (CPF_Input_Parser.rule xml2name termIndexMap ruleMap)
     (\ lr ->
       Xmlt.xml_take
         (Xmlt.xml_do "subtermVarEntries"
           (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
             (Xmlt.xml_do "subtermVarEntry"
               (Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
                 (\ aa ->
                   Xmlt.xml_take_many_sub [] Arith.zero_nat
                     Extended_Nat.Infinity_enat (Xmlt.xml_text "var")
                     (\ ba -> Xmlt.xml_return (aa, ba)))))
             Xmlt.xml_return))
         (\ rys ->
           Xmlt.xml_take cc
             (\ cca ->
               Xmlt.xml_take
                 (xml2cond_constraint_prf xml2name termIndexMap ruleMap)
                 (\ p -> Xmlt.xml_return (lr, (rys, (cca, p)))))))))
 Xmlt.xml_return))
                                     (\ c ->
                                       Xmlt.xml_return
 (Bounded_Increase_Impl.Induction a b c))))))
                         (Xmlt.xml_do "deleteCondition"
                           (Xmlt.xml_take cc
                             (\ a ->
                               Xmlt.xml_take
                                 (xml2cond_constraint_prf xml2name termIndexMap
                                   ruleMap)
                                 (\ b ->
                                   Xmlt.xml_return
                                     (Bounded_Increase_Impl.Delete_Condition a
                                       b))))))))))))
           (\ xa -> Xmlt.xml_return (id xa)))
         x;

xml2cond_red_pair_proof ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
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
                                       ([([Arith.Char], [Arith.Char])],
 (Bool, ([String], [String])))) ->
                                       Strict_Sum.Sum_bot
 (Xmlt.Xml_error String)
 (Bounded_Increase_Impl.Cond_red_pair_prf a [Arith.Char]);
xml2cond_red_pair_proof xml2name termIndexMap ruleMap =
  Xmlt.xml_do "condRedPairProof"
    (Xmlt.xml_take xml2name
      (\ c ->
        Xmlt.xml_take (Xmlt.xml_nat "before")
          (\ b ->
            Xmlt.xml_take (Xmlt.xml_nat "after")
              (\ a ->
                Xmlt.xml_take
                  (Xmlt.xml_do "conditions"
                    (Xmlt.xml_take_many_sub [] Arith.zero_nat
                      Extended_Nat.Infinity_enat
                      (Xmlt.xml_do "condition"
                        (Xmlt.xml_take
                          (xml2cond_constraint xml2name termIndexMap)
                          (\ ca ->
                            Xmlt.xml_take
                              (Xmlt.xml_do "dpSequence"
                                (Xmlt.xml_take
                                  (CPF_Input_Parser.rules xml2name termIndexMap
                                    ruleMap)
                                  (\ x -> Xmlt.xml_return (id x))))
                              (\ s ->
                                Xmlt.xml_take
                                  (xml2cond_constraint_prf xml2name termIndexMap
                                    ruleMap)
                                  (\ p -> Xmlt.xml_return (ca, (s, p)))))))
                      Xmlt.xml_return))
                  (\ ccs ->
                    Xmlt.xml_return
                      (Bounded_Increase_Impl.Cond_Red_Pair_Prf c ccs b a))))));

projected_rseq ::
  forall a.
    (Eq a,
      Shows_Literal.Showl a) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    a) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term a [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term a [Arith.Char],
Term_Rewriting.Term a [Arith.Char]) ->
                                      ((a, Arith.Nat) -> Arith.Nat) ->
(Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
    ((Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char]),
      [([Arith.Nat],
         ((Term_Rewriting.Term a [Arith.Char],
            Term_Rewriting.Term a [Arith.Char]),
           Term_Rewriting.Term a [Arith.Char]))]);
projected_rseq xml2name termIndexMap ruleMap pi =
  Xmlt.xml_do "projectedRewriteSequence"
    (Xmlt.xml_take (CPF_Input_Parser.rule xml2name termIndexMap ruleMap)
      (\ r ->
        Xmlt.xml_take (rseq xml2name termIndexMap ruleMap pi r)
          Xmlt.xml_return));

flat_contexts ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
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
                                       [Term_Rewriting.Actxt a
  (Term_Rewriting.Term a [Arith.Char])];
flat_contexts xml2name termIndexMap =
  Xmlt.xml_do "flatContexts"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (ctxt xml2name termIndexMap) Xmlt.xml_return);

xml2fp_trs_assm :: forall a. a;
xml2fp_trs_assm = error "undefined";

xml2inn_fp_trs_assm :: forall a. a;
xml2inn_fp_trs_assm = error "undefined";

multiset_af ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
                                  ([([Arith.Char], [Arith.Char])],
                                    (Bool, ([String], [String])))) ->
                                 Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                   a) ->
                                 (Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                   Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                     [((a, Arith.Nat), [Arith.Nat])];
multiset_af xml2name =
  Xmlt.xml_do "multisetArgumentFilter"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (Xmlt.xml_do "multisetArgumentFilterEntry"
        (Xmlt.xml_take xml2name
          (\ f ->
            Xmlt.xml_take (Xmlt.xml_nat "arity")
              (\ a ->
                Xmlt.xml_take
                  (Xmlt.xml_do "status"
                    (Xmlt.xml_take_many_sub [] Arith.zero_nat
                      Extended_Nat.Infinity_enat CPF_Input_Parser.position
                      Xmlt.xml_return))
                  (\ p -> Xmlt.xml_return ((f, a), p))))))
      Xmlt.xml_return);

arith_fun ::
  (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
      Semantic_Labeling_Carrier.ArithFun;
arith_fun xml =
  Xmlt.xml_do "arithFunction"
    (Xmlt.xml_take
      (Xmlt.xml_or
        (Xmlt.xml_change (Xmlt.xml_nat "natural")
          (\ n -> Xmlt.xml_return (Semantic_Labeling_Carrier.Const n)))
        (Xmlt.xml_or
          (Xmlt.xml_change (Xmlt.xml_nat "variable")
            (\ n ->
              Xmlt.xml_return
                (Semantic_Labeling_Carrier.Arg
                  (Arith.minus_nat n Arith.one_nat))))
          (Xmlt.xml_or
            (Xmlt.xml_do "sum"
              (Xmlt.xml_take_many_sub [] Arith.zero_nat
                Extended_Nat.Infinity_enat arith_fun
                (\ asa -> Xmlt.xml_return (Semantic_Labeling_Carrier.Sum asa))))
            (Xmlt.xml_or
              (Xmlt.xml_do "product"
                (Xmlt.xml_take_many_sub [] Arith.zero_nat
                  Extended_Nat.Infinity_enat arith_fun
                  (\ asa ->
                    Xmlt.xml_return (Semantic_Labeling_Carrier.Prod asa))))
              (Xmlt.xml_or
                (Xmlt.xml_do "max"
                  (Xmlt.xml_take_many_sub [] Arith.zero_nat
                    Extended_Nat.Infinity_enat arith_fun
                    (\ asa ->
                      Xmlt.xml_return (Semantic_Labeling_Carrier.Max asa))))
                (Xmlt.xml_or
                  (Xmlt.xml_do "min"
                    (Xmlt.xml_take_many_sub [] Arith.zero_nat
                      Extended_Nat.Infinity_enat arith_fun
                      (\ a ->
                        Xmlt.xml_return (Semantic_Labeling_Carrier.Min a))))
                  (Xmlt.xml_do "ifEqual"
                    (Xmlt.xml_take arith_fun
                      (\ a ->
                        Xmlt.xml_take arith_fun
                          (\ b ->
                            Xmlt.xml_take arith_fun
                              (\ c ->
                                Xmlt.xml_take arith_fun
                                  (\ d ->
                                    Xmlt.xml_return
                                      (Semantic_Labeling_Carrier.IfEqual a b c
d)))))))))))))
      Xmlt.xml_return)
    xml;

sl_variant ::
  forall a.
    ((Xml.Xml,
       ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
      Strict_Sum.Sum_bot (Xmlt.Xml_error String) a) ->
      (Xml.Xml,
        ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xmlt.Xml_error String)
          (Semantic_Labeling_Carrier.Sl_variant a [Arith.Char]);
sl_variant xml2name =
  Xmlt.xml_do "model"
    (Xmlt.xml_take
      (Xmlt.xml_or
        (Xmlt.xml_do "rootLabeling"
          (Xmlt.xml_take_optional xml2name
            (\ fo ->
              Xmlt.xml_return
                (Semantic_Labeling_Carrier.Rootlab
                  (case fo of {
                    Nothing -> Nothing;
                    Just f -> Just (f, Arith.one_nat);
                  })))))
        (Xmlt.xml_do "finiteModel"
          (Xmlt.xml_take
            (Xmlt.xml_change (Xmlt.xml_nat "carrierSize")
              (\ n -> Xmlt.xml_return (Arith.minus_nat n Arith.one_nat)))
            (\ n ->
              Xmlt.xml_take_optional
                (Xmlt.xml_do "tupleOrder"
                  (Xmlt.xml_take (Xmlt.xml_leaf "pointWise" ())
                    (\ x -> Xmlt.xml_return (id x))))
                (\ to ->
                  Xmlt.xml_take_many_sub [] Arith.zero_nat
                    Extended_Nat.Infinity_enat
                    (Xmlt.xml_do "interpret"
                      (Xmlt.xml_take xml2name
                        (\ a ->
                          Xmlt.xml_take (Xmlt.xml_nat "arity")
                            (\ b ->
                              Xmlt.xml_take arith_fun
                                (\ c -> Xmlt.xml_return ((a, b), c))))))
                    (\ inter ->
                      Xmlt.xml_return
                        (case to of {
                          Nothing ->
                            Semantic_Labeling_Carrier.Finitelab
                              (Semantic_Labeling_Carrier.SL_Inter n inter);
                          Just _ ->
                            Semantic_Labeling_Carrier.QuasiFinitelab
                              (Semantic_Labeling_Carrier.SL_Inter n inter) [];
                        })))))))
      (\ x -> Xmlt.xml_return (id x)));

precedence_weight_ac ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
                                  ([([Arith.Char], [Arith.Char])],
                                    (Bool, ([String], [String])))) ->
                                 Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                   a) ->
                                 (Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                   Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                     (Arith.Nat ->
                                       ([((a, Arith.Nat),
   (Arith.Nat, (Arith.Nat, Bool)))],
 Arith.Nat));
precedence_weight_ac xml2name =
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
                        Xmlt.xml_take_default False (Xmlt.xml_bool "isAC")
                          (\ e -> Xmlt.xml_return ((f, a), (p, (w, e))))))))))
      (\ ret -> Xmlt.xml_return (\ a -> (ret, a))));

ac_knuth_bendix_order ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
                                  ([([Arith.Char], [Arith.Char])],
                                    (Bool, ([String], [String])))) ->
                                 Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                   a) ->
                                 (Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                   Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                     (Reduction_Pair_Implementations.Redtriple_impl
                                       a);
ac_knuth_bendix_order xml2name =
  Xmlt.xml_do "ACKBO"
    (Xmlt.xml_take (Xmlt.xml_nat "w0")
      (\ w0 ->
        Xmlt.xml_take (precedence_weight_ac xml2name)
          (\ prw ->
            Xmlt.xml_take_default [] (afs xml2name)
              (\ afsa ->
                Xmlt.xml_return
                  (Reduction_Pair_Implementations.ACKBO (prw w0) afsa)))));

precedence_weight ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
                                  ([([Arith.Char], [Arith.Char])],
                                    (Bool, ([String], [String])))) ->
                                 Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                   a) ->
                                 (Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                   Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                     (Arith.Nat ->
                                       ([((a, Arith.Nat),
   (Arith.Nat, (Arith.Nat, Maybe [Arith.Nat])))],
 Arith.Nat));
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

knuth_bendix_order ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
                                  ([([Arith.Char], [Arith.Char])],
                                    (Bool, ([String], [String])))) ->
                                 Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                   a) ->
                                 (Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                   Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                     (Reduction_Pair_Implementations.Redtriple_impl
                                       a);
knuth_bendix_order xml2name =
  Xmlt.xml_do "knuthBendixOrder"
    (Xmlt.xml_take (Xmlt.xml_nat "w0")
      (\ w0 ->
        Xmlt.xml_take (precedence_weight xml2name)
          (\ prw ->
            Xmlt.xml_take_default [] (afs xml2name)
              (\ afsa ->
                Xmlt.xml_return
                  (Reduction_Pair_Implementations.KBO (prw w0) afsa)))));

max_monus_parser ::
  (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
      (Term_Rewriting.Term Max_Monus.Sig Arith.Nat);
max_monus_parser xml =
  Xmlt.xml_or
    (Xmlt.xml_do "sum"
      (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
        max_monus_parser
        (\ exps -> Xmlt.xml_return (Term_Rewriting.Fun Max_Monus.SumF exps))))
    (Xmlt.xml_or
      (Xmlt.xml_do "max"
        (Xmlt.xml_take_many_sub [] Arith.one_nat Extended_Nat.Infinity_enat
          max_monus_parser
          (\ exps -> Xmlt.xml_return (Term_Rewriting.Fun Max_Monus.MaxF exps))))
      (Xmlt.xml_or
        (Xmlt.xml_do "maxExt"
          (Xmlt.xml_take (Xmlt.xml_nat "min")
            (\ c0 ->
              Xmlt.xml_take_many_sub [] Arith.zero_nat
                Extended_Nat.Infinity_enat
                (Xmlt.xml_do "maxExtEntry"
                  (Xmlt.xml_take (Xmlt.xml_int "intercept")
                    (\ c ->
                      Xmlt.xml_take (Xmlt.xml_nat "slope")
                        (\ d ->
                          Xmlt.xml_take max_monus_parser
                            (\ e -> Xmlt.xml_return ((c, d), e))))))
                (\ cdes ->
                  Xmlt.xml_return
                    (Term_Rewriting.Fun (Max_Monus.MaxExtF c0 (map fst cdes))
                      (map snd cdes))))))
        (Xmlt.xml_or
          (Xmlt.xml_do "constant"
            (Xmlt.xml_take_nat
              (\ n ->
                Xmlt.xml_return (Term_Rewriting.Fun (Max_Monus.ConstF n) []))))
          (Xmlt.xml_do "variable"
            (Xmlt.xml_take_nat
              (\ n ->
                Xmlt.xml_return
                  (Term_Rewriting.Var (Arith.minus_nat n Arith.one_nat))))))))
    xml;

precedence_list ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
                                  ([([Arith.Char], [Arith.Char])],
                                    (Bool, ([String], [String])))) ->
                                 Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                   a) ->
                                 (Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                   Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                     [((a, Arith.Nat), Arith.Nat)];
precedence_list xml2name =
  Xmlt.xml_do "precedenceList"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (Xmlt.xml_do "precedenceListEntry"
        (Xmlt.xml_take xml2name
          (\ f ->
            Xmlt.xml_take (Xmlt.xml_nat "arity")
              (\ a ->
                Xmlt.xml_take (Xmlt.xml_nat "precedence")
                  (\ p -> Xmlt.xml_return ((f, a), p))))))
      Xmlt.xml_return);

max_poly_parser ::
  (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
      (Term_Rewriting.Term Max_Polynomial.Sig Arith.Nat);
max_poly_parser xml =
  Xmlt.xml_or
    (Xmlt.xml_do "product"
      (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
        max_poly_parser
        (\ exps ->
          Xmlt.xml_return (Term_Rewriting.Fun Max_Polynomial.ProdF exps))))
    (Xmlt.xml_or
      (Xmlt.xml_do "sum"
        (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
          max_poly_parser
          (\ exps ->
            Xmlt.xml_return (Term_Rewriting.Fun Max_Polynomial.SumF exps))))
      (Xmlt.xml_or
        (Xmlt.xml_do "max"
          (Xmlt.xml_take_many_sub [] Arith.one_nat Extended_Nat.Infinity_enat
            max_poly_parser
            (\ exps ->
              Xmlt.xml_return (Term_Rewriting.Fun Max_Polynomial.MaxF exps))))
        (Xmlt.xml_or
          (Xmlt.xml_do "constant"
            (Xmlt.xml_take_nat
              (\ n ->
                Xmlt.xml_return
                  (Term_Rewriting.Fun (Max_Polynomial.ConstF n) []))))
          (Xmlt.xml_do "variable"
            (Xmlt.xml_take_nat
              (\ n ->
                Xmlt.xml_return
                  (Term_Rewriting.Var (Arith.minus_nat n Arith.one_nat))))))))
    xml;

arctic_rat_linear_poly ::
  forall a.
    Interpretation a ->
      ((a, Arith.Nat),
        (SN_Order_Carrier.Arctic_delta Rat.Rat,
          [SN_Order_Carrier.Arctic_delta Rat.Rat]));
arctic_rat_linear_poly (Arctic_rat_linear_poly x4) = x4;

real_non_linear_poly ::
  forall a.
    Interpretation a ->
      ((a, Arith.Nat), [(Polynomials.Monom Arith.Nat, Real.Real)]);
real_non_linear_poly (Real_non_linear_poly x15) = x15;

rat_non_linear_poly ::
  forall a.
    Interpretation a ->
      ((a, Arith.Nat), [(Polynomials.Monom Arith.Nat, Rat.Rat)]);
rat_non_linear_poly (Rat_non_linear_poly x14) = x14;

int_non_linear_poly ::
  forall a.
    Interpretation a ->
      ((a, Arith.Nat), [(Polynomials.Monom Arith.Nat, Arith.Int)]);
int_non_linear_poly (Int_non_linear_poly x13) = x13;

arctic_linear_poly ::
  forall a.
    Interpretation a ->
      ((a, Arith.Nat), (SN_Order_Carrier.Arctic, [SN_Order_Carrier.Arctic]));
arctic_linear_poly (Arctic_linear_poly x3) = x3;

arctic_rat_matrix ::
  forall a.
    Interpretation a ->
      ((a, Arith.Nat),
        (Matrix.Mat (SN_Order_Carrier.Arctic_delta Rat.Rat),
          [Matrix.Mat (SN_Order_Carrier.Arctic_delta Rat.Rat)]));
arctic_rat_matrix (Arctic_rat_matrix x9) = x9;

real_linear_poly ::
  forall a. Interpretation a -> ((a, Arith.Nat), (Real.Real, [Real.Real]));
real_linear_poly (Real_linear_poly x5) = x5;

real_core_matrix ::
  forall a.
    Interpretation a ->
      ((a, Arith.Nat), (Matrix.Mat Real.Real, [Matrix.Mat Real.Real]));
real_core_matrix (Real_core_matrix x121 x122) = x122;

rat_linear_poly ::
  forall a. Interpretation a -> ((a, Arith.Nat), (Rat.Rat, [Rat.Rat]));
rat_linear_poly (Rat_linear_poly x2) = x2;

int_linear_poly ::
  forall a. Interpretation a -> ((a, Arith.Nat), (Arith.Int, [Arith.Int]));
int_linear_poly (Int_linear_poly x1) = x1;

int_core_matrix ::
  forall a.
    Interpretation a ->
      ((a, Arith.Nat), (Matrix.Mat Arith.Int, [Matrix.Mat Arith.Int]));
int_core_matrix (Int_core_matrix x11) = x11;

arctic_matrix ::
  forall a.
    Interpretation a ->
      ((a, Arith.Nat),
        (Matrix.Mat SN_Order_Carrier.Arctic,
          [Matrix.Mat SN_Order_Carrier.Arctic]));
arctic_matrix (Arctic_matrix x8) = x8;

real_matrix ::
  forall a.
    Interpretation a ->
      ((a, Arith.Nat), (Matrix.Mat Real.Real, [Matrix.Mat Real.Real]));
real_matrix (Real_matrix x10) = x10;

rat_matrix ::
  forall a.
    Interpretation a ->
      ((a, Arith.Nat), (Matrix.Mat Rat.Rat, [Matrix.Mat Rat.Rat]));
rat_matrix (Rat_matrix x7) = x7;

int_matrix ::
  forall a.
    Interpretation a ->
      ((a, Arith.Nat), (Matrix.Mat Arith.Int, [Matrix.Mat Arith.Int]));
int_matrix (Int_matrix x6) = x6;

xml_rat ::
  (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String) Rat.Rat;
xml_rat =
  Xmlt.xml_or
    (Xmlt.xml_change (Xmlt.xml_int "integer") (Xmlt.xml_return . Rat.of_int))
    (Xmlt.xml_do "rational"
      (Xmlt.xml_take (Xmlt.xml_int "numerator")
        (\ a ->
          Xmlt.xml_take (Xmlt.xml_int "denominator")
            (\ b ->
              Xmlt.xml_return
                (Rat.divide_rat (Rat.of_int a) (Rat.of_int b))))));

xml_real ::
  (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String) Real.Real;
xml_real =
  Xmlt.xml_or (Xmlt.xml_change xml_rat (Xmlt.xml_return . Real.ratreal))
    (Xmlt.xml_do "algebraic"
      (Xmlt.xml_take xml_rat
        (\ a ->
          Xmlt.xml_take xml_rat
            (\ b ->
              Xmlt.xml_take xml_rat
                (\ c ->
                  Xmlt.xml_return
                    (Real.plus_real (Real.ratreal a)
                      (Real.times_real (Real.ratreal b)
                        (NthRoot.sqrt (Real.ratreal c)))))))));

real_domain ::
  (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String) Real.Real;
real_domain =
  Xmlt.xml_do "algebraicNumbers"
    (Xmlt.xml_take
      (Xmlt.xml_do "delta"
        (Xmlt.xml_take xml_real (\ x -> Xmlt.xml_return (id x))))
      (\ x -> Xmlt.xml_return (id x)));

rat_domain ::
  (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String) Rat.Rat;
rat_domain =
  Xmlt.xml_do "rationals"
    (Xmlt.xml_take
      (Xmlt.xml_do "delta"
        (Xmlt.xml_take xml_rat (\ x -> Xmlt.xml_return (id x))))
      (\ x -> Xmlt.xml_return (id x)));

basic_domain ::
  (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String) (Arith.Nat -> Domain);
basic_domain =
  Xmlt.xml_or (Xmlt.xml_leaf "naturals" Natural)
    (Xmlt.xml_or (Xmlt.xml_leaf "integers" (\ _ -> Integera))
      (Xmlt.xml_or (Xmlt.xml_leaf "negativeIntegers" (\ _ -> NegativeInteger))
        (Xmlt.xml_or (Xmlt.xml_change rat_domain (Xmlt.xml_return . Rational))
          (Xmlt.xml_or
            (Xmlt.xml_change real_domain (Xmlt.xml_return . Mini_Alg))
            (Xmlt.xml_do "arctic"
              (Xmlt.xml_take
                (Xmlt.xml_do "domain"
                  (Xmlt.xml_take
                    (Xmlt.xml_or (Xmlt.xml_leaf "naturals" (\ _ -> Arctic))
                      (Xmlt.xml_or (Xmlt.xml_leaf "integers" (\ _ -> Arctic))
                        (Xmlt.xml_change rat_domain
                          (\ _ -> Xmlt.xml_return (\ _ -> Arctic_rat)))))
                    (\ x -> Xmlt.xml_return (id x))))
                (\ x -> Xmlt.xml_return (id x))))))));

nat_coeff ::
  (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String) Arith.Nat;
nat_coeff = Xmlt.xml_nat "nat";

interpretation_type ::
  (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String) Domain;
interpretation_type =
  Xmlt.xml_do "type"
    (Xmlt.xml_take
      (Xmlt.xml_or
        (Xmlt.xml_do "matrixInterpretation"
          (Xmlt.xml_take
            (Xmlt.xml_do "domain"
              (Xmlt.xml_take basic_domain (\ x -> Xmlt.xml_return (id x))))
            (\ a ->
              Xmlt.xml_take (Xmlt.xml_nat "dimension")
                (\ b ->
                  Xmlt.xml_take (Xmlt.xml_nat "strictDimension")
                    (\ c ->
                      Xmlt.xml_return (case a Arith.zero_nat of {
Natural _ -> Int_mat b c;
Integera -> Int_mat b c;
Arctic -> Arctic_mat b;
Arctic_rat -> Arctic_rat_mat b;
Rational _ _ -> Rat_mat b c;
Mini_Alg _ _ -> Mini_Alg_mat b c;
                                      }))))))
        (Xmlt.xml_or
          (Xmlt.xml_do "coreMatrixInterpretation"
            (Xmlt.xml_take
              (Xmlt.xml_do "domain"
                (Xmlt.xml_take basic_domain (\ x -> Xmlt.xml_return (id x))))
              (\ domain ->
                Xmlt.xml_take (Xmlt.xml_nat "dimension")
                  (\ di ->
                    Xmlt.xml_take
                      (Xmlt.xml_do "indices"
                        (Xmlt.xml_take_many_sub [] Arith.zero_nat
                          Extended_Nat.Infinity_enat nat_coeff
                          (\ a ->
                            Xmlt.xml_return
                              (map (\ x -> Arith.minus_nat x Arith.one_nat)
                                a))))
                      (\ ids ->
                        Xmlt.xml_take
                          (Xmlt.xml_do "mode"
                            (Xmlt.xml_take
                              (Xmlt.xml_or
                                (Xmlt.xml_leaf "E" Matrix_TRS_Impl.E_I)
                                (Xmlt.xml_leaf "M" Matrix_TRS_Impl.M_I))
                              Xmlt.xml_return))
                          (\ m ->
                            (case (case domain Arith.zero_nat of {
                                    Natural _ -> Just Nothing;
                                    Integera -> Just Nothing;
                                    NegativeInteger -> Nothing;
                                    Arctic -> Nothing;
                                    Arctic_rat -> Nothing;
                                    Int_mat _ _ -> Nothing;
                                    Arctic_mat _ -> Nothing;
                                    Arctic_rat_mat _ -> Nothing;
                                    Rational r _ ->
                                      Just (Just (Real.ratreal r));
                                    Rat_mat _ _ -> Nothing;
                                    Mini_Alg r _ -> Just (Just r);
                                    Mini_Alg_mat _ _ -> Nothing;
                                    Int_core_mat _ _ _ -> Nothing;
                                    Real_core_mat _ _ _ _ -> Nothing;
                                  })
                              of {
                              Nothing ->
                                Xmlt.xml_error
                                  "domain must be integers or rationals or reals in coreMatrixInterpretation";
                              Just Nothing ->
                                Xmlt.xml_return (Int_core_mat di ids m);
                              Just (Just d) ->
                                Xmlt.xml_return (Real_core_mat d di ids m);
                            })))))))
          (Xmlt.xml_do "polynomial"
            (Xmlt.xml_take
              (Xmlt.xml_do "domain"
                (Xmlt.xml_take
                  (Xmlt.xml_or basic_domain
                    (Xmlt.xml_do "matrices"
                      (Xmlt.xml_take (Xmlt.xml_nat "dimension")
                        (\ a ->
                          Xmlt.xml_take (Xmlt.xml_nat "strictDimension")
                            (\ b ->
                              Xmlt.xml_take
                                (Xmlt.xml_do "domain"
                                  (Xmlt.xml_take basic_domain
                                    (\ x -> Xmlt.xml_return (id x))))
                                (\ c ->
                                  Xmlt.xml_return
                                    (\ d ->
                                      (case c d of {
Natural _ -> Int_mat a b;
Integera -> Int_mat a b;
Arctic -> Arctic_mat a;
Arctic_rat -> Arctic_rat_mat a;
Rational _ _ -> Rat_mat a b;
Mini_Alg _ _ -> Mini_Alg_mat a b;
                                      }))))))))
                  (\ x -> Xmlt.xml_return (id x))))
              (\ a ->
                Xmlt.xml_take (Xmlt.xml_nat "degree")
                  (\ b -> Xmlt.xml_return (a b)))))))
      (\ x -> Xmlt.xml_return (id x)));

arctic_rat_coeff ::
  (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
      (SN_Order_Carrier.Arctic_delta Rat.Rat);
arctic_rat_coeff =
  Xmlt.xml_or
    (Xmlt.xml_change xml_rat (Xmlt.xml_return . SN_Order_Carrier.Num_arc_delta))
    (Xmlt.xml_leaf "minusInfinity" SN_Order_Carrier.MinInfty_delta);

int_coeff ::
  (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String) Arith.Int;
int_coeff = Xmlt.xml_int "integer";

arctic_coeff ::
  (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String) SN_Order_Carrier.Arctic;
arctic_coeff =
  Xmlt.xml_or
    (Xmlt.xml_change int_coeff (Xmlt.xml_return . SN_Order_Carrier.Num_arc))
    (Xmlt.xml_leaf "minusInfinity" SN_Order_Carrier.MinInfty);

xml_change ::
  forall a b c d e.
    (a -> Strict_Sum.Sum_bot String b) ->
      a -> ([Xml.Xml], (c, (d, (e, [String])))) ->
             Strict_Sum.Sum_bot (Xmlt.Xml_error String) b;
xml_change f p x =
  Xmlt.bind2 (f p) (\ e -> Xmlt.xml_error e x) Strict_Sum.right;

polynomial ::
  forall a.
    ((Xml.Xml,
       ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
      Strict_Sum.Sum_bot (Xmlt.Xml_error String) a) ->
      (Xml.Xml,
        ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xmlt.Xml_error String)
          (Polynomials.Tpoly Arith.Nat a);
polynomial xml2coeff x =
  Xmlt.xml_or
    (Xmlt.xml_change xml2coeff (\ n -> Xmlt.xml_return (Polynomials.PNum n)))
    (Xmlt.xml_or
      (Xmlt.xml_change (Xmlt.xml_nat "variable")
        (\ n ->
          Xmlt.xml_return (Polynomials.PVar (Arith.minus_nat n Arith.one_nat))))
      (Xmlt.xml_or
        (Xmlt.xml_do "sum"
          (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
            (polynomial xml2coeff)
            (\ a -> Xmlt.xml_return (Polynomials.PSum a))))
        (Xmlt.xml_do "product"
          (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
            (polynomial xml2coeff)
            (\ a -> Xmlt.xml_return (Polynomials.PMult a))))))
    x;

fit_length ::
  forall a.
    Congruence.Partial_object_ext a (Group.Monoid_ext a (Ring.Ring_ext a ())) ->
      Arith.Nat -> [a] -> [a];
fit_length c n uu =
  (if Arith.equal_nat n Arith.zero_nat then []
    else (case uu of {
           [] -> Arith.replicate (Arith.suc (Arith.minus_nat n Arith.one_nat))
                   (Ring.zero c);
           b : bs -> b : fit_length c (Arith.minus_nat n Arith.one_nat) bs;
         }));

vec_coeff ::
  forall a.
    ((Xml.Xml,
       ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
      Strict_Sum.Sum_bot (Xmlt.Xml_error String) a) ->
      (Xml.Xml,
        ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xmlt.Xml_error String) (Matrix.Vec a);
vec_coeff xml2coeff =
  Xmlt.xml_do "vector"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      xml2coeff (\ a -> Xmlt.xml_return (Matrix.vec_of_list a)));

mat_coeff ::
  forall a.
    Arith.Nat ->
      a -> ((Xml.Xml,
              ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
             Strict_Sum.Sum_bot (Xmlt.Xml_error String) a) ->
             (Xml.Xml,
               ([([Arith.Char], [Arith.Char])],
                 (Bool, ([String], [String])))) ->
               Strict_Sum.Sum_bot (Xmlt.Xml_error String) (Matrix.Mat a);
mat_coeff n ze xml2coeff =
  Xmlt.xml_or
    (Xmlt.xml_do "matrix"
      (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
        (vec_coeff xml2coeff)
        (\ a -> Xmlt.xml_return (Matrix.mat_of_rows n a))))
    (Xmlt.xml_change (vec_coeff xml2coeff)
      (\ v ->
        Xmlt.xml_return
          (Matrix.mat n n
            (\ (i, j) ->
              (if Arith.equal_nat j Arith.zero_nat then Matrix.vec_index v i
                else ze)))));

sum_lpoly ::
  forall a.
    Congruence.Partial_object_ext a (Group.Monoid_ext a (Ring.Ring_ext a ())) ->
      [a] -> [a] -> [a];
sum_lpoly c [] ys = ys;
sum_lpoly c (v : va) [] = v : va;
sum_lpoly c (x : xs) (y : ys) = Ring.add c x y : sum_lpoly c xs ys;

lpoly_of ::
  forall a.
    (Eq a) => Congruence.Partial_object_ext a
                (Group.Monoid_ext a (Ring.Ring_ext a ())) ->
                Polynomials.Tpoly Arith.Nat a ->
                  Strict_Sum.Sum_bot String (a, [a]);
lpoly_of c (Polynomials.PNum i) = Strict_Sum.returna (i, []);
lpoly_of c (Polynomials.PVar x) =
  Strict_Sum.returna
    (Ring.zero c, Arith.replicate x (Ring.zero c) ++ [Group.one c]);
lpoly_of c (Polynomials.PSum []) = Strict_Sum.returna (Ring.zero c, []);
lpoly_of c (Polynomials.PSum (p : ps)) =
  Strict_Sum.bind (lpoly_of c p)
    (\ (cp, ncp) ->
      Strict_Sum.bind (lpoly_of c (Polynomials.PSum ps))
        (\ (cq, ncq) ->
          Strict_Sum.returna (Ring.add c cp cq, sum_lpoly c ncp ncq)));
lpoly_of c (Polynomials.PMult []) = Strict_Sum.returna (Group.one c, []);
lpoly_of c (Polynomials.PMult (p : ps)) =
  Strict_Sum.bind (lpoly_of c p)
    (\ (cp, ncp) ->
      Strict_Sum.bind (lpoly_of c (Polynomials.PMult ps))
        (\ (cq, ncq) ->
          (if all (\ a -> Ring.zero c == a) ncp
            then Strict_Sum.returna
                   (Group.mult c cp cq, map (Group.mult c cp) ncq)
            else (if all (\ a -> Ring.zero c == a) ncq
                   then Strict_Sum.returna
                          (Group.mult c cp cq,
                            map (\ x -> Group.mult c x cq) ncp)
                   else Strict_Sum.errora
                          "cannot transform non-linear polynomial to linear polynomial"))));

interpretation ::
  forall a.
    Bool ->
      ((Xml.Xml,
         ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xmlt.Xml_error String) a) ->
        (Xml.Xml,
          ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
          Strict_Sum.Sum_bot (Xmlt.Xml_error String)
            (Reduction_Pair_Implementations.Redtriple_impl a);
interpretation bi xml2name =
  Xmlt.xml_do "interpretation"
    (Xmlt.xml_take interpretation_type
      (\ typea ->
        Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
          (Xmlt.xml_do "interpret"
            (Xmlt.xml_take xml2name
              (\ f ->
                Xmlt.xml_take (Xmlt.xml_nat "arity")
                  (\ a ->
                    (case typea of {
                      Natural deg ->
                        (if Arith.less_eq_nat deg Arith.one_nat && not bi
                          then let {
                                 c = Ordered_Semiring.class_semiring HOL.Type
                                       ();
                               } in Xmlt.xml_take
                                      (Xmlt.xml_change (polynomial int_coeff)
(xml_change (lpoly_of c)))
                                      (\ poly ->
Xmlt.xml_return
  (Int_linear_poly ((f, a), (fst poly, fit_length c a (snd poly)))))
                          else Xmlt.xml_take
                                 (Xmlt.xml_change (polynomial int_coeff)
                                   (Xmlt.xml_return . Polynomials.poly_of))
                                 (\ poly ->
                                   Xmlt.xml_return
                                     (Int_non_linear_poly ((f, a), poly))));
                      Integera ->
                        Xmlt.xml_take
                          (Xmlt.xml_change (polynomial int_coeff)
                            (Xmlt.xml_return . Polynomials.poly_of))
                          (\ poly ->
                            Xmlt.xml_return
                              (Int_non_linear_poly ((f, a), poly)));
                      NegativeInteger ->
                        Xmlt.xml_take
                          (Xmlt.xml_change (polynomial int_coeff)
                            (Xmlt.xml_return . Polynomials.poly_of))
                          (\ poly ->
                            Xmlt.xml_return
                              (Int_non_linear_poly ((f, a), poly)));
                      Arctic ->
                        let {
                          c = Ordered_Semiring.class_semiring HOL.Type ();
                        } in Xmlt.xml_take
                               (Xmlt.xml_change (polynomial arctic_coeff)
                                 (xml_change (lpoly_of c)))
                               (\ poly ->
                                 Xmlt.xml_return
                                   (Arctic_linear_poly
                                     ((f, a),
                                       (fst poly, fit_length c a (snd poly)))));
                      Arctic_rat ->
                        let {
                          c = Ordered_Semiring.class_semiring HOL.Type ();
                        } in Xmlt.xml_take
                               (Xmlt.xml_change (polynomial arctic_rat_coeff)
                                 (xml_change (lpoly_of c)))
                               (\ poly ->
                                 Xmlt.xml_return
                                   (Arctic_rat_linear_poly
                                     ((f, a),
                                       (fst poly, fit_length c a (snd poly)))));
                      Int_mat n _ ->
                        let {
                          c = Matrix.ring_mat HOL.Type n ();
                        } in Xmlt.xml_take
                               (Xmlt.xml_change
                                 (polynomial
                                   (mat_coeff n Arith.zero_int int_coeff))
                                 (xml_change (lpoly_of c)))
                               (\ poly ->
                                 Xmlt.xml_return
                                   (Int_matrix
                                     ((f, a),
                                       (fst poly, fit_length c a (snd poly)))));
                      Arctic_mat n ->
                        let {
                          c = Matrix.ring_mat HOL.Type n ();
                        } in Xmlt.xml_take
                               (Xmlt.xml_change
                                 (polynomial
                                   (mat_coeff n SN_Order_Carrier.zero_arctic
                                     arctic_coeff))
                                 (xml_change (lpoly_of c)))
                               (\ poly ->
                                 Xmlt.xml_return
                                   (Arctic_matrix
                                     ((f, a),
                                       (fst poly, fit_length c a (snd poly)))));
                      Arctic_rat_mat n ->
                        let {
                          c = Matrix.ring_mat HOL.Type n ();
                        } in Xmlt.xml_take
                               (Xmlt.xml_change
                                 (polynomial
                                   (mat_coeff n
                                     SN_Order_Carrier.zero_arctic_delta
                                     arctic_rat_coeff))
                                 (xml_change (lpoly_of c)))
                               (\ poly ->
                                 Xmlt.xml_return
                                   (Arctic_rat_matrix
                                     ((f, a),
                                       (fst poly, fit_length c a (snd poly)))));
                      Rational _ deg ->
                        (if Arith.less_eq_nat deg Arith.one_nat && not bi
                          then let {
                                 c = Ordered_Semiring.class_semiring HOL.Type
                                       ();
                               } in Xmlt.xml_take
                                      (Xmlt.xml_change (polynomial xml_rat)
(xml_change (lpoly_of c)))
                                      (\ poly ->
Xmlt.xml_return
  (Rat_linear_poly ((f, a), (fst poly, fit_length c a (snd poly)))))
                          else Xmlt.xml_take
                                 (Xmlt.xml_change (polynomial xml_rat)
                                   (Xmlt.xml_return . Polynomials.poly_of))
                                 (\ poly ->
                                   Xmlt.xml_return
                                     (Rat_non_linear_poly ((f, a), poly))));
                      Rat_mat n _ ->
                        let {
                          c = Matrix.ring_mat HOL.Type n ();
                        } in Xmlt.xml_take
                               (Xmlt.xml_change
                                 (polynomial (mat_coeff n Rat.zero_rat xml_rat))
                                 (xml_change (lpoly_of c)))
                               (\ poly ->
                                 Xmlt.xml_return
                                   (Rat_matrix
                                     ((f, a),
                                       (fst poly, fit_length c a (snd poly)))));
                      Mini_Alg _ deg ->
                        (if Arith.less_eq_nat deg Arith.one_nat && not bi
                          then let {
                                 c = Ordered_Semiring.class_semiring HOL.Type
                                       ();
                               } in Xmlt.xml_take
                                      (Xmlt.xml_change (polynomial xml_real)
(xml_change (lpoly_of c)))
                                      (\ poly ->
Xmlt.xml_return
  (Real_linear_poly ((f, a), (fst poly, fit_length c a (snd poly)))))
                          else Xmlt.xml_take
                                 (Xmlt.xml_change (polynomial xml_real)
                                   (Xmlt.xml_return . Polynomials.poly_of))
                                 (\ poly ->
                                   Xmlt.xml_return
                                     (Real_non_linear_poly ((f, a), poly))));
                      Mini_Alg_mat n _ ->
                        let {
                          c = Matrix.ring_mat HOL.Type n ();
                        } in Xmlt.xml_take
                               (Xmlt.xml_change
                                 (polynomial
                                   (mat_coeff n Real.zero_real xml_real))
                                 (xml_change (lpoly_of c)))
                               (\ poly ->
                                 Xmlt.xml_return
                                   (Real_matrix
                                     ((f, a),
                                       (fst poly, fit_length c a (snd poly)))));
                      Int_core_mat n _ _ ->
                        let {
                          c = Matrix.ring_mat HOL.Type n ();
                        } in Xmlt.xml_take
                               (Xmlt.xml_change
                                 (polynomial
                                   (mat_coeff n Arith.zero_int int_coeff))
                                 (xml_change (lpoly_of c)))
                               (\ poly ->
                                 Xmlt.xml_return
                                   (Int_core_matrix
                                     ((f, a),
                                       (fst poly, fit_length c a (snd poly)))));
                      Real_core_mat d n _ _ ->
                        let {
                          c = Matrix.ring_mat HOL.Type n ();
                        } in Xmlt.xml_take
                               (Xmlt.xml_change
                                 (polynomial
                                   (mat_coeff n Real.zero_real xml_real))
                                 (xml_change (lpoly_of c)))
                               (\ poly ->
                                 Xmlt.xml_return
                                   (Real_core_matrix d
                                     ((f, a),
                                       (fst poly, fit_length c a (snd poly)))));
                    })))))
          (\ pi ->
            Xmlt.xml_return
              (case typea of {
                Natural deg ->
                  (if Arith.less_eq_nat deg Arith.one_nat && not bi
                    then Reduction_Pair_Implementations.Int_carrier
                           (map int_linear_poly pi)
                    else Reduction_Pair_Implementations.Int_nl_carrier
                           (map int_non_linear_poly pi));
                Integera ->
                  Reduction_Pair_Implementations.Int_nl_carrier
                    (map int_non_linear_poly pi);
                NegativeInteger ->
                  Reduction_Pair_Implementations.Neg_Integer_Poly
                    (map int_non_linear_poly pi);
                Arctic ->
                  Reduction_Pair_Implementations.Arctic_carrier
                    (map arctic_linear_poly pi);
                Arctic_rat ->
                  Reduction_Pair_Implementations.Arctic_rat_carrier
                    (map arctic_rat_linear_poly pi);
                Int_mat n sd ->
                  Reduction_Pair_Implementations.Int_mat_carrier n sd
                    (map int_matrix pi);
                Arctic_mat n ->
                  Reduction_Pair_Implementations.Arctic_mat_carrier n
                    (map arctic_matrix pi);
                Arctic_rat_mat n ->
                  Reduction_Pair_Implementations.Arctic_rat_mat_carrier n
                    (map arctic_rat_matrix pi);
                Rational d deg ->
                  (if Arith.less_eq_nat deg Arith.one_nat && not bi
                    then Reduction_Pair_Implementations.Rat_carrier
                           (map rat_linear_poly pi)
                    else Reduction_Pair_Implementations.Rat_nl_carrier d
                           (map rat_non_linear_poly pi));
                Rat_mat n sd ->
                  Reduction_Pair_Implementations.Rat_mat_carrier n sd
                    (map rat_matrix pi);
                Mini_Alg d deg ->
                  (if Arith.less_eq_nat deg Arith.one_nat && not bi
                    then Reduction_Pair_Implementations.Real_carrier
                           (map real_linear_poly pi)
                    else Reduction_Pair_Implementations.Real_nl_carrier d
                           (map real_non_linear_poly pi));
                Mini_Alg_mat n sd ->
                  Reduction_Pair_Implementations.Real_mat_carrier n sd
                    (map real_matrix pi);
                Int_core_mat n ids m ->
                  Reduction_Pair_Implementations.Core_matrix
                    (Matrix_TRS_Impl.Core_Matrix_Inter m n ids
                      (map (\ (f, (c, cs)) -> (f, (cs, c)))
                        (map int_core_matrix pi)));
                Real_core_mat d n ids m ->
                  Reduction_Pair_Implementations.Core_matrix_delta d
                    (Matrix_TRS_Impl.Core_Matrix_Inter m n ids
                      (map (\ (f, (c, cs)) -> (f, (cs, c)))
                        (map real_core_matrix pi)));
              }))));

level_mapping ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
                                  ([([Arith.Char], [Arith.Char])],
                                    (Bool, ([String], [String])))) ->
                                 Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                   a) ->
                                 (Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                   Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                     [((a, Arith.Nat),
[(Arith.Nat, Arith.Nat)])];
level_mapping xml2name =
  Xmlt.xml_do "levelMapping"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (Xmlt.xml_do "levelMappingEntry"
        (Xmlt.xml_take xml2name
          (\ f ->
            Xmlt.xml_take (Xmlt.xml_nat "arity")
              (\ a ->
                Xmlt.xml_take_many_sub [] Arith.zero_nat
                  Extended_Nat.Infinity_enat
                  (Xmlt.xml_do "positionLevelEntry"
                    (Xmlt.xml_take (Xmlt.xml_nat "position")
                      (\ aa ->
                        Xmlt.xml_take (Xmlt.xml_nat "level")
                          (\ b -> Xmlt.xml_return (aa, b)))))
                  (\ ps ->
                    Xmlt.xml_return
                      ((f, a),
                        map (\ (p, b) ->
                              ((if Arith.equal_nat p Arith.zero_nat then a
                                 else Arith.minus_nat p Arith.one_nat),
                                b))
                          ps))))))
      Xmlt.xml_return);

wpo_params ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
                                  ([([Arith.Char], [Arith.Char])],
                                    (Bool, ([String], [String])))) ->
                                 Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                   a) ->
                                 (Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                   Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                     [((a, Arith.Nat),
(Arith.Nat, ([Arith.Nat], WPO.Order_tag)))];
wpo_params xml2name =
  Xmlt.xml_do "precedenceStatus"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (Xmlt.xml_do "precedenceStatusEntry"
        (Xmlt.xml_take xml2name
          (\ f ->
            Xmlt.xml_take (Xmlt.xml_nat "arity")
              (\ a ->
                Xmlt.xml_take (Xmlt.xml_nat "precedence")
                  (\ p ->
                    Xmlt.xml_take_optional
                      (Xmlt.xml_or (Xmlt.xml_leaf "lex" WPO.Lex)
                        (Xmlt.xml_leaf "mul" WPO.Mul))
                      (\ ot ->
                        Xmlt.xml_take
                          (Xmlt.xml_do "status"
                            (Xmlt.xml_take_many_sub [] Arith.zero_nat
                              Extended_Nat.Infinity_enat
                              CPF_Input_Parser.position Xmlt.xml_return))
                          (\ s ->
                            Xmlt.xml_return
                              ((f, a), (p, (s, (case ot of {
         Nothing -> WPO.Lex;
         Just lm -> lm;
       })))))))))))
      Xmlt.xml_return);

status_precedence ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
                                  ([([Arith.Char], [Arith.Char])],
                                    (Bool, ([String], [String])))) ->
                                 Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                   a) ->
                                 (Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                   Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                     [((a, Arith.Nat),
(Arith.Nat, WPO.Order_tag))];
status_precedence xml2name =
  Xmlt.xml_do "statusPrecedence"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (Xmlt.xml_do "statusPrecedenceEntry"
        (Xmlt.xml_take xml2name
          (\ f ->
            Xmlt.xml_take (Xmlt.xml_nat "arity")
              (\ a ->
                Xmlt.xml_take (Xmlt.xml_nat "precedence")
                  (\ p ->
                    Xmlt.xml_take
                      (Xmlt.xml_or (Xmlt.xml_leaf "lex" WPO.Lex)
                        (Xmlt.xml_leaf "mul" WPO.Mul))
                      (\ s -> Xmlt.xml_return ((f, a), (p, s))))))))
      Xmlt.xml_return);

path_order ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
                                  ([([Arith.Char], [Arith.Char])],
                                    (Bool, ([String], [String])))) ->
                                 Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                   a) ->
                                 (Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                   Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                     (Reduction_Pair_Implementations.Redtriple_impl
                                       a);
path_order xml2name =
  Xmlt.xml_do "recursivePathOrder"
    (Xmlt.xml_take (status_precedence xml2name)
      (\ prec_tau ->
        Xmlt.xml_take_default [] (afs xml2name)
          (\ af ->
            Xmlt.xml_return (Reduction_Pair_Implementations.RPO prec_tau af))));

redtriple ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
                                  ([([Arith.Char], [Arith.Char])],
                                    (Bool, ([String], [String])))) ->
                                 Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                   a) ->
                                 (a -> a) ->
                                   Bool ->
                                     (Xml.Xml,
                                       ([([Arith.Char], [Arith.Char])],
 (Bool, ([String], [String])))) ->
                                       Strict_Sum.Sum_bot
 (Xmlt.Xml_error String) (Reduction_Pair_Implementations.Redtriple_impl a);
redtriple xml2name shp bi xml =
  Xmlt.xml_or (path_order xml2name)
    (Xmlt.xml_or (knuth_bendix_order xml2name)
      (Xmlt.xml_or (ac_knuth_bendix_order xml2name)
        (Xmlt.xml_or (interpretation bi xml2name)
          (Xmlt.xml_or
            (Xmlt.xml_do "maxPoly"
              (Xmlt.xml_take_many_sub [] Arith.zero_nat
                Extended_Nat.Infinity_enat
                (Xmlt.xml_do "interpret"
                  (Xmlt.xml_take xml2name
                    (\ f ->
                      Xmlt.xml_take (Xmlt.xml_nat "arity")
                        (\ a ->
                          Xmlt.xml_take max_poly_parser
                            (\ e -> Xmlt.xml_return ((f, a), e))))))
                (\ inters ->
                  Xmlt.xml_return
                    (Reduction_Pair_Implementations.Max_poly inters))))
            (Xmlt.xml_or
              (Xmlt.xml_do "maxMonus"
                (Xmlt.xml_take_many_sub [] Arith.zero_nat
                  Extended_Nat.Infinity_enat
                  (Xmlt.xml_do "interpret"
                    (Xmlt.xml_take xml2name
                      (\ f ->
                        Xmlt.xml_take (Xmlt.xml_nat "arity")
                          (\ a ->
                            Xmlt.xml_take max_monus_parser
                              (\ e -> Xmlt.xml_return ((f, a), e))))))
                  (\ inters ->
                    Xmlt.xml_return
                      (Reduction_Pair_Implementations.Max_monus inters))))
              (Xmlt.xml_or
                (Xmlt.xml_do "coWeightedPathOrder"
                  (Xmlt.xml_take (wpo_params xml2name)
                    (\ a ->
                      Xmlt.xml_take (redtriple xml2name shp bi)
                        (\ b ->
                          Xmlt.xml_return
                            (Reduction_Pair_Implementations.COWPO a b)))))
                (Xmlt.xml_or
                  (Xmlt.xml_do "weightedPathOrder"
                    (Xmlt.xml_take (wpo_params xml2name)
                      (\ a ->
                        Xmlt.xml_take (redtriple xml2name shp bi)
                          (\ b ->
                            Xmlt.xml_return
                              (Reduction_Pair_Implementations.WPO a b)))))
                  (Xmlt.xml_or
                    (Xmlt.xml_do "generalizedWeightedPathOrder"
                      (Xmlt.xml_take (precedence_list xml2name)
                        (\ pr ->
                          Xmlt.xml_take (redtriple xml2name shp bi)
                            (\ b ->
                              Xmlt.xml_return
                                (Reduction_Pair_Implementations.GWPO (pr, shp)
                                  b)))))
                    (Xmlt.xml_or
                      (Xmlt.xml_do "monotonicSemanticPathOrder"
                        (Xmlt.xml_take (redtriple xml2name shp bi)
                          (\ a ->
                            Xmlt.xml_return
                              (Reduction_Pair_Implementations.MSPO a))))
                      (Xmlt.xml_or
                        (Xmlt.xml_do "filteredRedPair"
                          (Xmlt.xml_take_default [] (afs xml2name)
                            (\ af ->
                              Xmlt.xml_take (redtriple xml2name shp bi)
                                (\ b ->
                                  Xmlt.xml_return
                                    (Reduction_Pair_Implementations.Filtered_Redtriple
                                      af b)))))
                        (Xmlt.xml_do "scnp"
                          (Xmlt.xml_take
                            (Xmlt.xml_do "status"
                              (Xmlt.xml_take
                                (Xmlt.xml_or
                                  (Xmlt.xml_leaf "ms"
                                    List_Order_Implementations.MS_Ext)
                                  (Xmlt.xml_or
                                    (Xmlt.xml_leaf "min"
                                      List_Order_Implementations.Min_Ext)
                                    (Xmlt.xml_or
                                      (Xmlt.xml_leaf "dms"
List_Order_Implementations.Dms_Ext)
                                      (Xmlt.xml_leaf "max"
List_Order_Implementations.Max_Ext))))
                                Xmlt.xml_return))
                            (\ a ->
                              Xmlt.xml_take (level_mapping xml2name)
                                (\ b ->
                                  Xmlt.xml_take (redtriple xml2name shp False)
                                    (\ c ->
                                      Xmlt.xml_return
(Reduction_Pair_Implementations.SCNP a b c))))))))))))))))
    xml;

xml2inn_trs_assm :: forall a. a;
xml2inn_trs_assm = error "undefined";

ta_bounds_lhs ::
  forall a.
    ((Xml.Xml,
       ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
      Strict_Sum.Sum_bot (Xmlt.Xml_error String) a) ->
      (Xml.Xml,
        ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xmlt.Xml_error String)
          (Sum_Type.Sum ((a, Arith.Nat), [[Arith.Char]]) [Arith.Char]);
ta_bounds_lhs xml2name =
  Xmlt.xml_do "lhs"
    (Xmlt.xml_or
      (Xmlt.xml_take CPF_Input_Parser.state
        (\ a -> Xmlt.xml_return (Sum_Type.Inr a)))
      (Xmlt.xml_take xml2name
        (\ f ->
          Xmlt.xml_take (Xmlt.xml_nat "height")
            (\ h ->
              Xmlt.xml_take_many_sub [] Arith.zero_nat
                Extended_Nat.Infinity_enat CPF_Input_Parser.state
                (\ qs -> Xmlt.xml_return (Sum_Type.Inl ((f, h), qs)))))));

bounds_bound ::
  (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String) Arith.Nat;
bounds_bound = Xmlt.xml_nat "bound";

bounds_type ::
  (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String) Matchbounds_Impl.Boundstype;
bounds_type =
  Xmlt.xml_do "type"
    (Xmlt.xml_take
      (Xmlt.xml_or (Xmlt.xml_leaf "roof" Matchbounds_Impl.Roof)
        (Xmlt.xml_leaf "match" Matchbounds_Impl.Match))
      (\ x -> Xmlt.xml_return (id x)));

bounds_info ::
  forall a.
    ((Xml.Xml,
       ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
      Strict_Sum.Sum_bot (Xmlt.Xml_error String) a) ->
      (Xml.Xml,
        ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xmlt.Xml_error String)
          (Matchbounds_Impl.Bounds_info a [Arith.Char]);
bounds_info xml2name =
  Xmlt.xml_do "bounds"
    (Xmlt.xml_take bounds_type
      (\ a ->
        Xmlt.xml_take bounds_bound
          (\ b ->
            Xmlt.xml_take CPF_Input_Parser.final_states
              (\ c ->
                Xmlt.xml_take
                  (CPF_Input_Parser.tree_automaton (ta_bounds_lhs xml2name))
                  (\ d ->
                    Xmlt.xml_take_default Tree_Automata_Impl.Id_Relation
                      closed_criterion
                      (\ e ->
                        Xmlt.xml_return
                          (Matchbounds_Impl.Bounds_Info a b c d e)))))));

xml2trs_termination_proof ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term (Labelings.Lab a b)
 [Arith.Char],
Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Check_Termination.Trs_termination_proof a b [Arith.Char]);
xml2trs_termination_proof xml2name termIndexMap ruleMap x =
  Xmlt.xml_do "trsTerminationProof"
    (Xmlt.xml_take
      (Xmlt.xml_or
        (Xmlt.xml_do "rIsEmpty" (Xmlt.xml_return Check_Termination.R_is_Empty))
        (Xmlt.xml_or
          (Xmlt.xml_do "semlab"
            (Xmlt.xml_take (sl_variant xml2name)
              (\ sli ->
                Xmlt.xml_take
                  (Xmlt.xml_do "trs"
                    (Xmlt.xml_take
                      (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                      (\ xa -> Xmlt.xml_return (id xa))))
                  (\ lr ->
                    Xmlt.xml_take_default []
                      (CPF_Input_Parser.innermostLhss xml2name termIndexMap)
                      (\ lq ->
                        Xmlt.xml_take
                          (xml2trs_termination_proof xml2name termIndexMap
                            ruleMap)
                          (\ p ->
                            Xmlt.xml_return
                              (Check_Termination.Semlab sli lq lr p)))))))
          (Xmlt.xml_or
            (Xmlt.xml_do "split"
              (Xmlt.xml_take
                (Xmlt.xml_do "trs"
                  (Xmlt.xml_take
                    (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                    (\ xa -> Xmlt.xml_return (id xa))))
                (\ a ->
                  Xmlt.xml_take
                    (xml2trs_termination_proof xml2name termIndexMap ruleMap)
                    (\ b ->
                      Xmlt.xml_take
                        (xml2trs_termination_proof xml2name termIndexMap
                          ruleMap)
                        (\ c ->
                          Xmlt.xml_return (Check_Termination.Split a b c))))))
            (Xmlt.xml_or
              (Xmlt.xml_do "dpTrans"
                (Xmlt.xml_take
                  (Xmlt.xml_do "dps"
                    (Xmlt.xml_take
                      (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                      (\ xa -> Xmlt.xml_return (id xa))))
                  (\ dps ->
                    Xmlt.xml_take
                      (xml2dp_termination_proof xml2name termIndexMap ruleMap)
                      (\ prf ->
                        Xmlt.xml_return
                          (Check_Termination.DP_Trans Defaults.default_nfs_dp
                            True dps prf)))))
              (Xmlt.xml_or
                (Xmlt.xml_do "ruleRemoval"
                  (Xmlt.xml_take (redtriple xml2name Labelings.Sharp False)
                    (\ ord ->
                      Xmlt.xml_take
                        (Xmlt.xml_do "trs"
                          (Xmlt.xml_take
                            (CPF_Input_Parser.rules xml2name termIndexMap
                              ruleMap)
                            (\ xa -> Xmlt.xml_return (id xa))))
                        (\ r ->
                          Xmlt.xml_take
                            (xml2trs_termination_proof xml2name termIndexMap
                              ruleMap)
                            (\ p ->
                              Xmlt.xml_return
                                (Check_Termination.Rule_Removal ord r p))))))
                (Xmlt.xml_or
                  (Xmlt.xml_change (bounds_info xml2name)
                    (Xmlt.xml_return . Check_Termination.Bounds))
                  (Xmlt.xml_or
                    (Xmlt.xml_do "stringReversal"
                      (Xmlt.xml_take
                        (Xmlt.xml_do "trs"
                          (Xmlt.xml_take
                            (CPF_Input_Parser.rules xml2name termIndexMap
                              ruleMap)
                            (\ xa -> Xmlt.xml_return (id xa))))
                        (\ _ ->
                          Xmlt.xml_take
                            (xml2trs_termination_proof xml2name termIndexMap
                              ruleMap)
                            (\ prf ->
                              Xmlt.xml_return
                                (Check_Termination.String_Reversal prf)))))
                    (Xmlt.xml_or
                      (Xmlt.xml_do "equalityRemoval"
                        (Xmlt.xml_take
                          (xml2trs_termination_proof xml2name termIndexMap
                            ruleMap)
                          (\ a ->
                            Xmlt.xml_return
                              (Check_Termination.Drop_Equality a))))
                      (Xmlt.xml_or
                        (Xmlt.xml_do "rightGroundTermination"
                          (Xmlt.xml_return
                            Check_Termination.Right_Ground_Termination))
                        (Xmlt.xml_or
                          (Xmlt.xml_do "constantToUnary"
                            (Xmlt.xml_take CPF_Input_Parser.plain_var
                              (\ v ->
                                Xmlt.xml_take (renaming xml2name)
                                  (\ ren ->
                                    Xmlt.xml_take
                                      (Xmlt.xml_do "trs"
(Xmlt.xml_take (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
  (\ xa -> Xmlt.xml_return (id xa))))
                                      (\ s ->
Xmlt.xml_take (xml2trs_termination_proof xml2name termIndexMap ruleMap)
  (\ p ->
    Xmlt.xml_return
      (Check_Termination.Constant_String
        (Monadic_Rewriting_Impl.Const_string_sound_proof v ren s) p)))))))
                          (Xmlt.xml_or
                            (Xmlt.xml_do "removeNonApplicableRules"
                              (Xmlt.xml_take
                                (Xmlt.xml_do "trs"
                                  (Xmlt.xml_take
                                    (CPF_Input_Parser.rules xml2name
                                      termIndexMap ruleMap)
                                    (\ xa -> Xmlt.xml_return (id xa))))
                                (\ a ->
                                  Xmlt.xml_take
                                    (xml2trs_termination_proof xml2name
                                      termIndexMap ruleMap)
                                    (\ b ->
                                      Xmlt.xml_return
(Check_Termination.Remove_Nonapplicable_Rules a b)))))
                            (Xmlt.xml_or
                              (Xmlt.xml_do "uncurry"
                                (Xmlt.xml_take
                                  (uncurry_info xml2name termIndexMap ruleMap)
                                  (\ i ->
                                    Xmlt.xml_take
                                      (Xmlt.xml_do "trs"
(Xmlt.xml_take (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
  (\ xa -> Xmlt.xml_return (id xa))))
                                      (\ r ->
Xmlt.xml_take (xml2trs_termination_proof xml2name termIndexMap ruleMap)
  (\ p -> Xmlt.xml_return (Check_Termination.Uncurry i r p))))))
                              (Xmlt.xml_or
                                (Xmlt.xml_do "flatContextClosure"
                                  (Xmlt.xml_take
                                    (flat_contexts xml2name termIndexMap)
                                    (\ i ->
                                      Xmlt.xml_take
(Xmlt.xml_do "trs"
  (Xmlt.xml_take (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
    (\ xa -> Xmlt.xml_return (id xa))))
(\ r ->
  Xmlt.xml_take (xml2trs_termination_proof xml2name termIndexMap ruleMap)
    (\ p -> Xmlt.xml_return (Check_Termination.Fcc i r p))))))
                                (Xmlt.xml_or
                                  (Xmlt.xml_do "switchInnermost"
                                    (Xmlt.xml_take
                                      (wcr_proof xml2name termIndexMap)
                                      (\ a ->
Xmlt.xml_take (xml2trs_termination_proof xml2name termIndexMap ruleMap)
  (\ b -> Xmlt.xml_return (Check_Termination.Switch_Innermost a b)))))
                                  (Xmlt.xml_or
                                    (Xmlt.xml_do "permutingArgumentFilter"
                                      (Xmlt.xml_take (afs xml2name)
(\ a ->
  Xmlt.xml_take (xml2trs_termination_proof xml2name termIndexMap ruleMap)
    (\ b -> Xmlt.xml_return (Check_Termination.Permuting_AFS a b)))))
                                    (Xmlt.xml_or
                                      (Xmlt.xml_do "terminationAssumption"
(Xmlt.xml_take (xml2inn_trs_assm xml2name)
  (\ qtrs -> Xmlt.xml_return (Check_Termination.Assume_SN qtrs []))))
                                      (Xmlt.xml_do "unknownProof"
(Xmlt.xml_take (Xmlt.xml_text "description")
  (\ _ ->
    Xmlt.xml_take (xml2inn_trs_assm xml2name)
      (\ b ->
        Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
          (xml2subproof xml2name termIndexMap ruleMap)
          (\ c ->
            Xmlt.xml_return
              (Check_Termination.Assume_SN b c))))))))))))))))))))))
      (\ xa -> Xmlt.xml_return (id xa)))
    x;

xml2dp_termination_proof ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term (Labelings.Lab a b)
 [Arith.Char],
Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Check_Termination.Dp_termination_proof a b [Arith.Char]);
xml2dp_termination_proof xml2name termIndexMap ruleMap x =
  Xmlt.xml_do "dpProof"
    (Xmlt.xml_take
      (Xmlt.xml_or
        (Xmlt.xml_do "pIsEmpty" (Xmlt.xml_return Check_Termination.P_is_Empty))
        (Xmlt.xml_or
          (Xmlt.xml_do "depGraphProc"
            (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
              (Xmlt.xml_do "component"
                (Xmlt.xml_take
                  (Xmlt.xml_do "dps"
                    (Xmlt.xml_take
                      (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                      (\ xa -> Xmlt.xml_return (id xa))))
                  (\ dps ->
                    Xmlt.xml_take_optional
                      (xml2dp_termination_proof xml2name termIndexMap ruleMap)
                      (\ prfOpt -> Xmlt.xml_return (prfOpt, dps)))))
              (\ a -> Xmlt.xml_return (Check_Termination.Dep_Graph_Proc a))))
          (Xmlt.xml_or
            (Xmlt.xml_do "redPairProc"
              (Xmlt.xml_take (redtriple xml2name Labelings.Sharp False)
                (\ a ->
                  Xmlt.xml_take
                    (Xmlt.xml_do "dps"
                      (Xmlt.xml_take
                        (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                        (\ xa -> Xmlt.xml_return (id xa))))
                    (\ b ->
                      Xmlt.xml_take
                        (xml2dp_termination_proof xml2name termIndexMap ruleMap)
                        (\ c ->
                          Xmlt.xml_return
                            (Check_Termination.Redpair_Proc a b c))))))
            (Xmlt.xml_or
              (Xmlt.xml_do "usableRulesProc"
                (Xmlt.xml_take
                  (Xmlt.xml_do "usableRules"
                    (Xmlt.xml_take
                      (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                      (\ xa -> Xmlt.xml_return (id xa))))
                  (\ a ->
                    Xmlt.xml_take
                      (xml2dp_termination_proof xml2name termIndexMap ruleMap)
                      (\ b ->
                        Xmlt.xml_return
                          (Check_Termination.Usable_Rules_Proc a b)))))
              (Xmlt.xml_or
                (Xmlt.xml_do "innermostLhssRemovalProc"
                  (Xmlt.xml_take
                    (CPF_Input_Parser.innermostLhss xml2name termIndexMap)
                    (\ a ->
                      Xmlt.xml_take
                        (xml2dp_termination_proof xml2name termIndexMap ruleMap)
                        (\ b ->
                          Xmlt.xml_return
                            (Check_Termination.Q_Reduction_Proc a b)))))
                (Xmlt.xml_or
                  (Xmlt.xml_do "rewritingProc"
                    (Xmlt.xml_take
                      (CPF_Input_Parser.rule xml2name termIndexMap ruleMap)
                      (\ (s, t) ->
                        Xmlt.xml_take (rstep xml2name termIndexMap ruleMap)
                          (\ (p, (lr, ta)) ->
                            Xmlt.xml_take_default (s, ta)
                              (CPF_Input_Parser.rule xml2name termIndexMap
                                ruleMap)
                              (\ st ->
                                Xmlt.xml_take_optional
                                  (Xmlt.xml_do "usableRules"
                                    (Xmlt.xml_take
                                      (CPF_Input_Parser.rules xml2name
termIndexMap ruleMap)
                                      (\ xa -> Xmlt.xml_return (id xa))))
                                  (\ ur ->
                                    Xmlt.xml_take
                                      (xml2dp_termination_proof xml2name
termIndexMap ruleMap)
                                      (\ prof ->
Xmlt.xml_return
  (Check_Termination.Rewriting_Proc ur (s, t) (s, ta) st lr p prof))))))))
                  (Xmlt.xml_or
                    (Xmlt.xml_do "narrowingProc"
                      (Xmlt.xml_take
                        (CPF_Input_Parser.rule xml2name termIndexMap ruleMap)
                        (\ a ->
                          Xmlt.xml_take CPF_Input_Parser.pos
                            (\ b ->
                              Xmlt.xml_take
                                (Xmlt.xml_do "narrowings"
                                  (Xmlt.xml_take
                                    (CPF_Input_Parser.rules xml2name
                                      termIndexMap ruleMap)
                                    (\ xa -> Xmlt.xml_return (id xa))))
                                (\ c ->
                                  Xmlt.xml_take
                                    (xml2dp_termination_proof xml2name
                                      termIndexMap ruleMap)
                                    (\ d ->
                                      Xmlt.xml_return
(Check_Termination.Narrowing_Proc a b c d)))))))
                    (Xmlt.xml_or
                      (Xmlt.xml_do "instantiationProc"
                        (Xmlt.xml_take
                          (CPF_Input_Parser.rule xml2name termIndexMap ruleMap)
                          (\ a ->
                            Xmlt.xml_take
                              (Xmlt.xml_do "instantiations"
                                (Xmlt.xml_take
                                  (CPF_Input_Parser.rules xml2name termIndexMap
                                    ruleMap)
                                  (\ xa -> Xmlt.xml_return (id xa))))
                              (\ b ->
                                Xmlt.xml_take
                                  (xml2dp_termination_proof xml2name
                                    termIndexMap ruleMap)
                                  (\ c ->
                                    Xmlt.xml_return
                                      (Check_Termination.Instantiation_Proc a b
c))))))
                      (Xmlt.xml_or
                        (Xmlt.xml_do "forwardInstantiationProc"
                          (Xmlt.xml_take
                            (CPF_Input_Parser.rule xml2name termIndexMap
                              ruleMap)
                            (\ a ->
                              Xmlt.xml_take
                                (Xmlt.xml_do "instantiations"
                                  (Xmlt.xml_take
                                    (CPF_Input_Parser.rules xml2name
                                      termIndexMap ruleMap)
                                    (\ xa -> Xmlt.xml_return (id xa))))
                                (\ b ->
                                  Xmlt.xml_take_optional
                                    (Xmlt.xml_do "usableRules"
                                      (Xmlt.xml_take
(CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
(\ xa -> Xmlt.xml_return (id xa))))
                                    (\ c ->
                                      Xmlt.xml_take
(xml2dp_termination_proof xml2name termIndexMap ruleMap)
(\ d ->
  Xmlt.xml_return (Check_Termination.Forward_Instantiation_Proc a b c d)))))))
                        (Xmlt.xml_or
                          (Xmlt.xml_do "semlabProc"
                            (Xmlt.xml_take (sl_variant xml2name)
                              (\ sli ->
                                Xmlt.xml_take
                                  (Xmlt.xml_do "dps"
                                    (Xmlt.xml_take
                                      (CPF_Input_Parser.rules xml2name
termIndexMap ruleMap)
                                      (\ xa -> Xmlt.xml_return (id xa))))
                                  (\ lp ->
                                    Xmlt.xml_take
                                      (Xmlt.xml_do "trs"
(Xmlt.xml_take (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
  (\ xa -> Xmlt.xml_return (id xa))))
                                      (\ lr ->
Xmlt.xml_take_default [] (CPF_Input_Parser.innermostLhss xml2name termIndexMap)
  (\ lq ->
    Xmlt.xml_take (xml2dp_termination_proof xml2name termIndexMap ruleMap)
      (\ p ->
        Xmlt.xml_return (Check_Termination.Semlab_Proc sli lp lq lr p))))))))
                          (Xmlt.xml_or
                            (Xmlt.xml_do "subtermProc"
                              (Xmlt.xml_take
                                (Xmlt.xml_or
                                  (Xmlt.xml_change (proj xml2name)
                                    (Xmlt.xml_return . Sum_Type.Inl))
                                  (Xmlt.xml_change (multiset_af xml2name)
                                    (Xmlt.xml_return . Sum_Type.Inr)))
                                (\ pi_mpi ->
                                  Xmlt.xml_take_many_sub [] Arith.zero_nat
                                    Extended_Nat.Infinity_enat
                                    (projected_rseq xml2name termIndexMap
                                      ruleMap
                                      (Subterm_Criterion_Impl.create_proj
(case pi_mpi of {
  Sum_Type.Inl lpi -> lpi;
  Sum_Type.Inr _ -> Subterm_Criterion_Impl.Projection [];
})))
                                    (\ seq ->
                                      Xmlt.xml_take
(Xmlt.xml_do "dps"
  (Xmlt.xml_take (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
    (\ xa -> Xmlt.xml_return (id xa))))
(\ dps ->
  Xmlt.xml_take (xml2dp_termination_proof xml2name termIndexMap ruleMap)
    (\ prf ->
      Xmlt.xml_return
        (case pi_mpi of {
          Sum_Type.Inl lpi ->
            Check_Termination.Subterm_Criterion_Proc lpi seq dps prf;
          Sum_Type.Inr mpi ->
            Check_Termination.Gen_Subterm_Criterion_Proc mpi dps prf;
        })))))))
                            (Xmlt.xml_or
                              (Xmlt.xml_do "redPairUrProc"
                                (Xmlt.xml_take
                                  (redtriple xml2name Labelings.Sharp False)
                                  (\ a ->
                                    Xmlt.xml_take
                                      (Xmlt.xml_do "dps"
(Xmlt.xml_take (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
  (\ xa -> Xmlt.xml_return (id xa))))
                                      (\ b ->
Xmlt.xml_take
  (Xmlt.xml_do "usableRules"
    (Xmlt.xml_take (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
      (\ xa -> Xmlt.xml_return (id xa))))
  (\ c ->
    Xmlt.xml_take (xml2dp_termination_proof xml2name termIndexMap ruleMap)
      (\ d -> Xmlt.xml_return (Check_Termination.Redpair_UR_Proc a b c d)))))))
                              (Xmlt.xml_or
                                (Xmlt.xml_do "monoRedPairUrProc"
                                  (Xmlt.xml_take
                                    (redtriple xml2name Labelings.Sharp False)
                                    (\ a ->
                                      Xmlt.xml_take
(Xmlt.xml_do "dps"
  (Xmlt.xml_take (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
    (\ xa -> Xmlt.xml_return (id xa))))
(\ b ->
  Xmlt.xml_take
    (Xmlt.xml_do "trs"
      (Xmlt.xml_take (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
        (\ xa -> Xmlt.xml_return (id xa))))
    (\ c ->
      Xmlt.xml_take
        (Xmlt.xml_do "usableRules"
          (Xmlt.xml_take (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
            (\ xa -> Xmlt.xml_return (id xa))))
        (\ d ->
          Xmlt.xml_take (xml2dp_termination_proof xml2name termIndexMap ruleMap)
            (\ e ->
              Xmlt.xml_return
                (Check_Termination.Mono_Redpair_UR_Proc a b c d e))))))))
                                (Xmlt.xml_or
                                  (Xmlt.xml_do "monoRedPairProc"
                                    (Xmlt.xml_take
                                      (redtriple xml2name Labelings.Sharp False)
                                      (\ a ->
Xmlt.xml_take
  (Xmlt.xml_do "dps"
    (Xmlt.xml_take (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
      (\ xa -> Xmlt.xml_return (id xa))))
  (\ b ->
    Xmlt.xml_take
      (Xmlt.xml_do "trs"
        (Xmlt.xml_take (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
          (\ xa -> Xmlt.xml_return (id xa))))
      (\ c ->
        Xmlt.xml_take (xml2dp_termination_proof xml2name termIndexMap ruleMap)
          (\ d ->
            Xmlt.xml_return (Check_Termination.Mono_Redpair_Proc a b c d)))))))
                                  (Xmlt.xml_or
                                    (Xmlt.xml_do "innermostMonoRedPairProc"
                                      (Xmlt.xml_take
(redtriple xml2name Labelings.Sharp False)
(\ rp ->
  Xmlt.xml_take
    (Xmlt.xml_do "dps"
      (Xmlt.xml_take (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
        (\ xa -> Xmlt.xml_return (id xa))))
    (\ p ->
      Xmlt.xml_take
        (Xmlt.xml_do "trs"
          (Xmlt.xml_take (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
            (\ xa -> Xmlt.xml_return (id xa))))
        (\ r ->
          Xmlt.xml_take (xml2dp_termination_proof xml2name termIndexMap ruleMap)
            (\ c ->
              Xmlt.xml_return
                (Check_Termination.Mono_URM_Redpair_Proc rp p r c)))))))
                                    (Xmlt.xml_or
                                      (Xmlt.xml_do "uncurryProc"
(Xmlt.xml_take_optional (Xmlt.xml_nat "applicativeTop")
  (\ a ->
    Xmlt.xml_take (uncurry_info xml2name termIndexMap ruleMap)
      (\ b ->
        Xmlt.xml_take
          (Xmlt.xml_do "dps"
            (Xmlt.xml_take
              (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
              (\ xa -> Xmlt.xml_return (id xa))))
          (\ c ->
            Xmlt.xml_take
              (Xmlt.xml_do "trs"
                (Xmlt.xml_take
                  (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                  (\ xa -> Xmlt.xml_return (id xa))))
              (\ d ->
                Xmlt.xml_take
                  (xml2dp_termination_proof xml2name termIndexMap ruleMap)
                  (\ e ->
                    Xmlt.xml_return
                      (Check_Termination.Uncurry_Proc a b c d e))))))))
                                      (Xmlt.xml_or
(Xmlt.xml_do "flatContextClosureProc"
  (Xmlt.xml_take
    (Xmlt.xml_do "freshSymbol"
      (Xmlt.xml_take xml2name (\ xa -> Xmlt.xml_return (id xa))))
    (\ a ->
      Xmlt.xml_take (flat_contexts xml2name termIndexMap)
        (\ b ->
          Xmlt.xml_take
            (Xmlt.xml_do "dps"
              (Xmlt.xml_take
                (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                (\ xa -> Xmlt.xml_return (id xa))))
            (\ c ->
              Xmlt.xml_take
                (Xmlt.xml_do "trs"
                  (Xmlt.xml_take
                    (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                    (\ xa -> Xmlt.xml_return (id xa))))
                (\ d ->
                  Xmlt.xml_take
                    (xml2dp_termination_proof xml2name termIndexMap ruleMap)
                    (\ e ->
                      Xmlt.xml_return
                        (Check_Termination.Fcc_Proc a b c d e))))))))
(Xmlt.xml_or
  (Xmlt.xml_do "switchInnermostProc"
    (Xmlt.xml_take (wcr_proof xml2name termIndexMap)
      (\ a ->
        Xmlt.xml_take (xml2dp_termination_proof xml2name termIndexMap ruleMap)
          (\ b ->
            Xmlt.xml_return (Check_Termination.Switch_Innermost_Proc a b)))))
  (Xmlt.xml_or
    (Xmlt.xml_do "splitProc"
      (Xmlt.xml_take
        (Xmlt.xml_do "dps"
          (Xmlt.xml_take (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
            (\ xa -> Xmlt.xml_return (id xa))))
        (\ a ->
          Xmlt.xml_take
            (Xmlt.xml_do "trs"
              (Xmlt.xml_take
                (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                (\ xa -> Xmlt.xml_return (id xa))))
            (\ b ->
              Xmlt.xml_take
                (xml2dp_termination_proof xml2name termIndexMap ruleMap)
                (\ c ->
                  Xmlt.xml_take
                    (xml2dp_termination_proof xml2name termIndexMap ruleMap)
                    (\ d ->
                      Xmlt.xml_return
                        (Check_Termination.Split_Proc a b c d)))))))
    (Xmlt.xml_or
      (Xmlt.xml_do "finitenessAssumption"
        (Xmlt.xml_take (xml2dp_input xml2name termIndexMap ruleMap True)
          (\ dpp -> Xmlt.xml_return (Check_Termination.Assume_Finite dpp []))))
      (Xmlt.xml_or
        (Xmlt.xml_do "unknownProof"
          (Xmlt.xml_take (Xmlt.xml_text "description")
            (\ _ ->
              Xmlt.xml_take (xml2dp_input xml2name termIndexMap ruleMap True)
                (\ b ->
                  Xmlt.xml_take_many_sub [] Arith.zero_nat
                    Extended_Nat.Infinity_enat
                    (xml2subproof xml2name termIndexMap ruleMap)
                    (\ c ->
                      Xmlt.xml_return (Check_Termination.Assume_Finite b c))))))
        (Xmlt.xml_or
          (Xmlt.xml_do "switchToTRS"
            (Xmlt.xml_take
              (xml2trs_termination_proof xml2name termIndexMap ruleMap)
              (\ a -> Xmlt.xml_return (Check_Termination.To_Trs_Proc a))))
          (Xmlt.xml_or
            (Xmlt.xml_do "generalRedPairProc"
              (Xmlt.xml_take (redtriple xml2name Labelings.Sharp True)
                (\ rp ->
                  Xmlt.xml_take
                    (Xmlt.xml_do "strict"
                      (Xmlt.xml_take
                        (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                        (\ xa -> Xmlt.xml_return (id xa))))
                    (\ s ->
                      Xmlt.xml_take
                        (Xmlt.xml_do "bound"
                          (Xmlt.xml_take
                            (CPF_Input_Parser.rules xml2name termIndexMap
                              ruleMap)
                            (\ xa -> Xmlt.xml_return (id xa))))
                        (\ b ->
                          Xmlt.xml_take
                            (xml2cond_red_pair_proof xml2name termIndexMap
                              ruleMap)
                            (\ c ->
                              Xmlt.xml_take
                                (xml2dp_termination_proof xml2name termIndexMap
                                  ruleMap)
                                (\ ps ->
                                  Xmlt.xml_take_optional
                                    (xml2dp_termination_proof xml2name
                                      termIndexMap ruleMap)
                                    (\ pbo ->
                                      Xmlt.xml_return
(Check_Termination.General_Redpair_Proc rp s b c (case pbo of {
           Nothing -> [ps];
           Just pb -> [ps, pb];
         }))))))))))
            (Xmlt.xml_or
              (Xmlt.xml_do "complexConstantRemovalProc"
                (Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
                  (\ t ->
                    Xmlt.xml_take
                      (Xmlt.xml_do "ruleMap"
                        (Xmlt.xml_take_many_sub [] Arith.zero_nat
                          Extended_Nat.Infinity_enat
                          (Xmlt.xml_do "ruleMapEntry"
                            (Xmlt.xml_take
                              (CPF_Input_Parser.rule xml2name termIndexMap
                                ruleMap)
                              (\ a ->
                                Xmlt.xml_take
                                  (CPF_Input_Parser.rule xml2name termIndexMap
                                    ruleMap)
                                  (\ b -> Xmlt.xml_return (a, b)))))
                          Xmlt.xml_return))
                      (\ rls ->
                        Xmlt.xml_take
                          (xml2dp_termination_proof xml2name termIndexMap
                            ruleMap)
                          (\ prf ->
                            Xmlt.xml_return
                              (Check_Termination.Complex_Constant_Removal_Proc
                                (Complex_Constant_Removal_Impl.Complex_Constant_Removal_Proof
                                  t rls)
                                prf))))))
              (Xmlt.xml_do "sizeChangeProc"
                (Xmlt.xml_take
                  (Xmlt.xml_or (Xmlt.xml_leaf "subtermCriterion" Nothing)
                    (Xmlt.xml_do "reductionPair"
                      (Xmlt.xml_take (redtriple xml2name Labelings.Sharp False)
                        (\ redp ->
                          Xmlt.xml_take_optional
                            (Xmlt.xml_do "usableRules"
                              (Xmlt.xml_take
                                (CPF_Input_Parser.rules xml2name termIndexMap
                                  ruleMap)
                                (\ xa -> Xmlt.xml_return (id xa))))
                            (\ ur -> Xmlt.xml_return (Just (redp, ur)))))))
                  (\ version ->
                    Xmlt.xml_take_many_sub [] Arith.zero_nat
                      Extended_Nat.Infinity_enat
                      (scg xml2name termIndexMap ruleMap)
                      (\ b ->
                        (case version of {
                          Nothing ->
                            Xmlt.xml_return
                              (Check_Termination.Size_Change_Subterm_Proc b);
                          Just redp_ur ->
                            Xmlt.xml_return
                              (Check_Termination.Size_Change_Redpair_Proc
                                (fst redp_ur) (snd redp_ur) b);
                        })))))))))))))))))))))))))))))
      (\ xa -> Xmlt.xml_return (id xa)))
    x;

xml2subproof ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term (Labelings.Lab a b)
 [Arith.Char],
Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Check_Termination_Common.Generic_assm_proof a b [Arith.Char]
    (Check_Termination.Trs_termination_proof a b [Arith.Char])
    (Check_Termination.Dp_termination_proof a b [Arith.Char])
    (Check_Termination.Fptrs_termination_proof a b [Arith.Char]) ()
    (Check_Termination.Unknown_proof a b [Arith.Char]));
xml2subproof xml2name termIndexMap ruleMap x =
  Xmlt.xml_do "subProof"
    (Xmlt.xml_or
      (Xmlt.xml_take (xml2dp_input xml2name termIndexMap ruleMap True)
        (\ inp ->
          Xmlt.xml_take (xml2dp_termination_proof xml2name termIndexMap ruleMap)
            (\ prf ->
              Xmlt.xml_return
                (Check_Termination_Common.Finite_assm_proof inp prf))))
      (Xmlt.xml_take (xml2inn_fp_trs_assm xml2name)
        (\ a ->
          (case a of {
            Sum_Type.Inl qtrs ->
              Xmlt.xml_take
                (xml2trs_termination_proof xml2name termIndexMap ruleMap)
                (\ prf ->
                  Xmlt.xml_return
                    (Check_Termination_Common.SN_assm_proof qtrs prf));
            Sum_Type.Inr fptrs ->
              Xmlt.xml_take
                (xml2fptrs_termination_proof xml2name termIndexMap ruleMap)
                (\ prf ->
                  Xmlt.xml_return
                    (Check_Termination_Common.SN_FP_assm_proof fptrs prf));
          }))))
    x;

xml2fptrs_termination_proof ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term (Labelings.Lab a b)
 [Arith.Char],
Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Check_Termination.Fptrs_termination_proof a b [Arith.Char]);
xml2fptrs_termination_proof xml2name termIndexMap ruleMap x =
  Xmlt.xml_do "trsTerminationProof"
    (Xmlt.xml_take
      (Xmlt.xml_or
        (Xmlt.xml_do "terminationAssumption"
          (Xmlt.xml_take (xml2fp_trs_assm xml2name)
            (\ inp -> Xmlt.xml_return (Check_Termination.Assume_FP_SN inp []))))
        (Xmlt.xml_do "unknownProof"
          (Xmlt.xml_take (xml2fp_trs_assm xml2name)
            (\ inp ->
              Xmlt.xml_take_many_sub [] Arith.zero_nat
                Extended_Nat.Infinity_enat
                (xml2subproof xml2name termIndexMap ruleMap)
                (\ subprfs ->
                  Xmlt.xml_return
                    (Check_Termination.Assume_FP_SN inp subprfs))))))
      Xmlt.xml_return)
    x;

unraveling_info ::
  forall a b.
    (Compare.Compare_order a, Shows_Literal.Showl a, Compare.Compare_order b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term (Labelings.Lab a b)
 [Arith.Char],
Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  [(((Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char],
       Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]),
      [(Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char],
         Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char])]),
     [(Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char],
        Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char])])];
unraveling_info xml2name termIndexMap ruleMap =
  Xmlt.xml_do "unravelingInformation"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (Xmlt.xml_do "unravelingEntry"
        (Xmlt.xml_take
          (CPF_Input_Parser.crule xml2name termIndexMap "conditionalRule")
          (\ a ->
            Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
              (CPF_Input_Parser.rule xml2name termIndexMap ruleMap)
              (\ b -> Xmlt.xml_return (a, b)))))
      (\ a -> Xmlt.xml_return (id a)));

xml2quasi_reductive_proof ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term (Labelings.Lab a b)
 [Arith.Char],
Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Check_Quasi_Reductive.Quasi_reductive_proof a b [Arith.Char]);
xml2quasi_reductive_proof xml2name termIndexMap ruleMap =
  Xmlt.xml_do "quasiReductiveProof"
    (Xmlt.xml_take
      (Xmlt.xml_do "unraveling"
        (Xmlt.xml_take (unraveling_info xml2name termIndexMap ruleMap)
          (\ a ->
            Xmlt.xml_take
              (xml2trs_termination_proof xml2name termIndexMap ruleMap)
              (\ b -> Xmlt.xml_return (Check_Quasi_Reductive.Unravel a b)))))
      (\ x -> Xmlt.xml_return (id x)));

xml2state_map ::
  forall a b.
    (Compare.Compare_order a, Shows_Literal.Showl a, Compare.Compare_order b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    (Xml.Xml,
                                      ([([Arith.Char], [Arith.Char])],
(Bool, ([String], [String])))) ->
                                      Strict_Sum.Sum_bot (Xmlt.Xml_error String)
([Arith.Char] -> Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]);
xml2state_map xml2name termIndexMap =
  Xmlt.xml_do "stateMap"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (Xmlt.xml_do "entry"
        (Xmlt.xml_take CPF_Input_Parser.state
          (\ a ->
            Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
              (\ b -> Xmlt.xml_return (a, b)))))
      (\ a -> Xmlt.xml_return (\ x -> Arith.the (Map.map_of a x))));

xml2nonreachable_etac_info ::
  forall a b c.
    (Compare.Compare_order a, Shows_Literal.Showl a, Compare.Compare_order b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    (Xml.Xml,
                                      ([([Arith.Char], [Arith.Char])],
(Bool, ([String], [String])))) ->
                                      Strict_Sum.Sum_bot (Xmlt.Xml_error String)
(Check_Nonreachability.Nonreachability_proof a [Arith.Char] c b);
xml2nonreachable_etac_info xml2name termIndexMap =
  Xmlt.xml_do "nonreachableEtac"
    (Xmlt.xml_take (CPF_Input_Parser.cPFsignature xml2name)
      (\ a ->
        Xmlt.xml_take xml2name
          (\ b ->
            Xmlt.xml_take xml2name
              (\ c ->
                Xmlt.xml_take
                  (CPF_Input_Parser.tree_automaton
                    (CPF_Input_Parser.ta_normal_lhs xml2name))
                  (\ d ->
                    Xmlt.xml_take (xml2state_map xml2name termIndexMap)
                      (\ e ->
                        Xmlt.xml_return
                          (Check_Nonreachability.Nonreachable_ETAC a b c
                            (Exact_Tree_Automata_Completion_Impl.map_states_impl
                              e d))))))));

conversion ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
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
conversion xml2name termIndexMap =
  Xmlt.xml_do "conversion"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (CPF_Input_Parser.term xml2name termIndexMap) Xmlt.xml_return);

subsumption_proof ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
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
                                       ([([Arith.Char], [Arith.Char])],
 (Bool, ([String], [String])))) ->
                                       Strict_Sum.Sum_bot
 (Xmlt.Xml_error String)
 [((Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char]),
    [Term_Rewriting.Term a [Arith.Char]])];
subsumption_proof xml2name termIndexMap ruleMap =
  Xmlt.xml_do "subsumptionProof"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (Xmlt.xml_do "ruleSubsumptionProof"
        (Xmlt.xml_take (CPF_Input_Parser.rule xml2name termIndexMap ruleMap)
          (\ r ->
            Xmlt.xml_take (conversion xml2name termIndexMap)
              (\ e -> Xmlt.xml_return (r, e)))))
      Xmlt.xml_return);

xml2approx_completion_proof ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term (Labelings.Lab a b)
 [Arith.Char],
Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Check_Completion_Proof.Approx_completion_proof a b [Arith.Char]);
xml2approx_completion_proof xml2name termIndexMap ruleMap =
  Xmlt.xml_do "approxCompletionProof"
    (Xmlt.xml_take (wcr_proof xml2name termIndexMap)
      (\ w ->
        Xmlt.xml_take (xml2trs_termination_proof xml2name termIndexMap ruleMap)
          (\ t ->
            Xmlt.xml_take_optional
              (subsumption_proof xml2name termIndexMap ruleMap)
              (\ s ->
                Xmlt.xml_return
                  (Check_Completion_Proof.SN_WCR_Subsumption w t s)))));

xml2ordered_completion ::
  forall a b.
    (Compare.Compare_order a, Shows_Literal.Showl a, Compare.Compare_order b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term (Labelings.Lab a b)
 [Arith.Char],
Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  ([(Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char],
      Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char])],
    ([(Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char],
        Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char])],
      (Ordered_Completion_Impl.Reduction_order_input (Labelings.Lab a b),
        Ordered_Completion_Impl.Ordered_completion_proof (Labelings.Lab a b)
          [Arith.Char])));
xml2ordered_completion xml2name termIndexMap ruleMap =
  Xmlt.xml_do "orderedCompletion"
    (Xmlt.xml_take
      (Xmlt.xml_do "orderedCompletionResult"
        (Xmlt.xml_take
          (Xmlt.xml_do "trs"
            (Xmlt.xml_take
              (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
              Xmlt.xml_return))
          (\ rs ->
            Xmlt.xml_take
              (Xmlt.xml_do "equations"
                (Xmlt.xml_take
                  (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                  Xmlt.xml_return))
              (\ es ->
                Xmlt.xml_take
                  (Xmlt.xml_do "reductionOrder"
                    (Xmlt.xml_take (CPF_Input_Parser.kbo_input xml2name)
                      Xmlt.xml_return))
                  (\ ro -> Xmlt.xml_return (rs, (es, ro)))))))
      (\ (rs, (es, ro)) ->
        Xmlt.xml_take (xml2ordered_completion_proof xml2name termIndexMap)
          (\ p -> Xmlt.xml_return (rs, (es, (ro, p))))));

xml2completion_proof ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term (Labelings.Lab a b)
 [Arith.Char],
Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Check_Completion_Proof.Completion_proof a b [Arith.Char]);
xml2completion_proof xml2name termIndexMap ruleMap =
  Xmlt.xml_do "completionProof"
    (Xmlt.xml_take (wcr_proof xml2name termIndexMap)
      (\ w ->
        Xmlt.xml_take (xml2trs_termination_proof xml2name termIndexMap ruleMap)
          (\ t ->
            Xmlt.xml_take
              (Xmlt.xml_do "equivalenceProof"
                (Xmlt.xml_take (subsumption_proof xml2name termIndexMap ruleMap)
                  (\ s1 ->
                    Xmlt.xml_take_optional
                      (subsumption_proof xml2name termIndexMap ruleMap)
                      (\ s2 -> Xmlt.xml_return (s1, s2)))))
              (\ (s1, s2) ->
                Xmlt.xml_return
                  (Check_Completion_Proof.SN_WCR_Eq w t s1 s2)))));

xml2equational_disproof ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term (Labelings.Lab a b)
 [Arith.Char],
Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Check_Equational_Proof.Equational_disproof a b [Arith.Char]);
xml2equational_disproof xml2name termIndexMap ruleMap =
  Xmlt.xml_do "equationalDisproof"
    (Xmlt.xml_take
      (Xmlt.xml_or
        (Xmlt.xml_do "completionAndNormalization"
          (Xmlt.xml_take
            (Xmlt.xml_do "trs"
              (Xmlt.xml_take
                (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                (\ x -> Xmlt.xml_return (id x))))
            (\ a ->
              Xmlt.xml_take (xml2completion_proof xml2name termIndexMap ruleMap)
                (\ b ->
                  Xmlt.xml_return
                    (Check_Equational_Proof.Completion_and_Normalization_Different
                      a b)))))
        (Xmlt.xml_or
          (Xmlt.xml_do "approxAndCompletionAndNormalization"
            (Xmlt.xml_take
              (Xmlt.xml_do "trs"
                (Xmlt.xml_take
                  (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                  (\ x -> Xmlt.xml_return (id x))))
              (\ a ->
                Xmlt.xml_take
                  (xml2approx_completion_proof xml2name termIndexMap ruleMap)
                  (\ b ->
                    Xmlt.xml_return
                      (Check_Equational_Proof.Approx_and_Completion_and_Normalization_Different
                        a b)))))
          (Xmlt.xml_or
            (Xmlt.xml_do "approxAndOrderedCompletionAndNormalization"
              (Xmlt.xml_take
                (Xmlt.xml_do "trs"
                  (Xmlt.xml_take
                    (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                    (\ x -> Xmlt.xml_return (id x))))
                (\ a ->
                  Xmlt.xml_take
                    (Xmlt.xml_do "equations"
                      (Xmlt.xml_take
                        (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                        (\ x -> Xmlt.xml_return (id x))))
                    (\ b ->
                      Xmlt.xml_take
                        (Xmlt.xml_do "reductionOrder"
                          (Xmlt.xml_take (CPF_Input_Parser.kbo_input xml2name)
                            (\ x -> Xmlt.xml_return (id x))))
                        (\ c ->
                          Xmlt.xml_return
                            (Check_Equational_Proof.Approx_and_Ordered_Completion_and_Normalization_Different
                              a b c))))))
            (Xmlt.xml_change
              (xml2ordered_completion xml2name termIndexMap ruleMap)
              (\ (rs, (es, (ro, p))) ->
                Xmlt.xml_return
                  (Check_Equational_Proof.Ordered_Completion_and_Normalization_Different
                    rs es ro p))))))
      (\ x -> Xmlt.xml_return (id x)));

xml2nonreachability_proof ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term (Labelings.Lab a b)
 [Arith.Char],
Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Check_Nonreachability.Nonreachability_proof a [Arith.Char]
    (Reduction_Pair_Implementations.Redtriple_impl (Labelings.Lab a b)) b);
xml2nonreachability_proof xml2name termIndexMap ruleMap x =
  Xmlt.xml_do "nonreachabilityProof"
    (Xmlt.xml_take
      (Xmlt.xml_or
        (Xmlt.xml_leaf "nonreachableTcap"
          Check_Nonreachability.Nonreachable_Gtcap)
        (Xmlt.xml_or (xml2nonreachable_etac_info xml2name termIndexMap)
          (Xmlt.xml_or
            (Xmlt.xml_do "nonreachableSubstApprox"
              (Xmlt.xml_take
                (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                (\ a ->
                  Xmlt.xml_take
                    (xml2nonreachability_proof xml2name termIndexMap ruleMap)
                    (\ b ->
                      Xmlt.xml_return
                        (Check_Nonreachability.Nonreachable_Subst_Approx a
                          b)))))
            (Xmlt.xml_or
              (Xmlt.xml_do "nonreachableReverse"
                (Xmlt.xml_take
                  (xml2nonreachability_proof xml2name termIndexMap ruleMap)
                  (\ xa ->
                    Xmlt.xml_return
                      (Check_Nonreachability.Nonreachable_Reverse xa))))
              (Xmlt.xml_or
                (Xmlt.xml_do "nonreachableCorewritePair"
                  (Xmlt.xml_take (redtriple xml2name Labelings.Sharp False)
                    (\ xa ->
                      Xmlt.xml_return
                        (Check_Nonreachability.Nonreachable_Co_Rewrite_Pair
                          Reduction_Pair_Implementations.default_rel_impl xa))))
                (Xmlt.xml_or
                  (Xmlt.xml_do "nonreachableEquationalDisproof"
                    (Xmlt.xml_take
                      (xml2equational_disproof xml2name termIndexMap ruleMap)
                      (\ xa ->
                        Xmlt.xml_return
                          (Check_Nonreachability.Nonreachable_Equational_Disproof
                            xa))))
                  (Xmlt.xml_do "nonreachableFGCR"
                    (Xmlt.xml_take
                      (Xmlt.xml_do "eqSymbol"
                        (Xmlt.xml_take xml2name Xmlt.xml_return))
                      (\ eq ->
                        Xmlt.xml_take
                          (Xmlt.xml_do "trueSymbol"
                            (Xmlt.xml_take xml2name Xmlt.xml_return))
                          (\ tr ->
                            Xmlt.xml_take
                              (Xmlt.xml_do "falseSymbol"
                                (Xmlt.xml_take xml2name Xmlt.xml_return))
                              (\ fa ->
                                Xmlt.xml_take
                                  (xml2ordered_completion xml2name termIndexMap
                                    ruleMap)
                                  (\ (rs, (es, (ro, p))) ->
                                    Xmlt.xml_return
                                      (Check_Nonreachability.Nonreachable_FGCR
eq tr fa es rs ro p)))))))))))))
      (\ xa -> Xmlt.xml_return (id xa)))
    x;

xml2nonjoinability_proof ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term (Labelings.Lab a b)
 [Arith.Char],
Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Check_Nonreachability.Nonjoinability_proof a [Arith.Char]
    (Reduction_Pair_Implementations.Redtriple_impl (Labelings.Lab a b)) b);
xml2nonjoinability_proof xml2name termIndexMap ruleMap =
  Xmlt.xml_do "nonjoinabilityProof"
    (Xmlt.xml_take
      (Xmlt.xml_or
        (Xmlt.xml_leaf "nonjoinableTcap" Check_Nonreachability.Nonjoinable_Tcap)
        (Xmlt.xml_change
          (xml2nonreachability_proof xml2name termIndexMap ruleMap)
          (Xmlt.xml_return . Check_Nonreachability.Nonjoinable_Ground_NF)))
      (\ x -> Xmlt.xml_return (id x)));

xml2inline_cond_info ::
  forall a b.
    (Compare.Compare_order a, Shows_Literal.Showl a, Compare.Compare_order b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    (Xml.Xml,
                                      ([([Arith.Char], [Arith.Char])],
(Bool, ([String], [String])))) ->
                                      Strict_Sum.Sum_bot (Xmlt.Xml_error String)
[(((Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char],
     Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]),
    [(Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char],
       Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char])]),
   [(Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char],
      Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char])])];
xml2inline_cond_info xml2name termIndexMap =
  Xmlt.xml_do "inlinedRules"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (Xmlt.xml_do "inlinedRule"
        (Xmlt.xml_take (CPF_Input_Parser.crule xml2name termIndexMap "rule")
          (\ rule ->
            Xmlt.xml_take
              (CPF_Input_Parser.conditions xml2name termIndexMap
                "inlinedConditions")
              (\ conds -> Xmlt.xml_return (rule, conds)))))
      Xmlt.xml_return);

split_if_info ::
  forall a b.
    (Compare.Compare_order a, Shows_Literal.Showl a, Compare.Compare_order b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    (Xml.Xml,
                                      ([([Arith.Char], [Arith.Char])],
(Bool, ([String], [String])))) ->
                                      Strict_Sum.Sum_bot (Xmlt.Xml_error String)
(Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char],
  (Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char],
    [(((Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char],
         Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]),
        [(Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char],
           Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char])]),
       (Labelings.Lab a b,
         [Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]]))]));
split_if_info xml2name termIndexMap =
  Xmlt.xml_do "splitIfInformation"
    (Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
      (\ t ->
        Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
          (\ f ->
            Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
              (Xmlt.xml_do "normalUnravelingEntry"
                (Xmlt.xml_take
                  (CPF_Input_Parser.crule xml2name termIndexMap "rule")
                  (\ a ->
                    Xmlt.xml_take xml2name
                      (\ fa ->
                        Xmlt.xml_take_many_sub [] Arith.zero_nat
                          Extended_Nat.Infinity_enat
                          (CPF_Input_Parser.term xml2name termIndexMap)
                          (\ ts -> Xmlt.xml_return (a, (fa, ts)))))))
              (\ es -> Xmlt.xml_return (t, (f, es))))));

xml2infeasibility_proof ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term (Labelings.Lab a b)
 [Arith.Char],
Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Check_Infeasibility.Infeasibility_proof a [Arith.Char]
    (Reduction_Pair_Implementations.Redtriple_impl (Labelings.Lab a b)) b);
xml2infeasibility_proof xml2name termIndexMap ruleMap x =
  Xmlt.xml_do "infeasibilityProof"
    (Xmlt.xml_take
      (Xmlt.xml_or
        (Xmlt.xml_do "infeasibleCompoundConditions"
          (Xmlt.xml_take xml2name
            (\ a ->
              Xmlt.xml_take
                (xml2nonreachability_proof xml2name termIndexMap ruleMap)
                (\ b ->
                  Xmlt.xml_return
                    (Check_Infeasibility.Infeasible_Compound_Conditions a b)))))
        (Xmlt.xml_or
          (Xmlt.xml_do "infeasibleEquation"
            (Xmlt.xml_take (CPF_Input_Parser.rule xml2name termIndexMap ruleMap)
              (\ a ->
                Xmlt.xml_take
                  (xml2nonreachability_proof xml2name termIndexMap ruleMap)
                  (\ b ->
                    Xmlt.xml_return
                      ((case a of {
                         (aa, ba) ->
                           Check_Infeasibility.Infeasible_Equation aa ba;
                       })
                        b)))))
          (Xmlt.xml_or
            (Xmlt.xml_do "infeasibleSubset"
              (Xmlt.xml_take
                (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                (\ a ->
                  Xmlt.xml_take
                    (xml2infeasibility_proof xml2name termIndexMap ruleMap)
                    (\ b ->
                      Xmlt.xml_return
                        (Check_Infeasibility.Infeasible_Subset a b)))))
            (Xmlt.xml_or
              (Xmlt.xml_do "infeasibleRhssEqual"
                (Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
                  (\ a ->
                    Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
                      (\ b ->
                        Xmlt.xml_take
                          (CPF_Input_Parser.term xml2name termIndexMap)
                          (\ c ->
                            Xmlt.xml_take
                              (xml2nonjoinability_proof xml2name termIndexMap
                                ruleMap)
                              (\ d ->
                                Xmlt.xml_return
                                  (Check_Infeasibility.Infeasible_Rhss_Equal a b
                                    c d)))))))
              (Xmlt.xml_or
                (Xmlt.xml_do "infeasibleTrans"
                  (Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
                    (\ a ->
                      Xmlt.xml_take
                        (CPF_Input_Parser.term xml2name termIndexMap)
                        (\ b ->
                          Xmlt.xml_take
                            (CPF_Input_Parser.term xml2name termIndexMap)
                            (\ c ->
                              Xmlt.xml_take
                                (xml2nonreachability_proof xml2name termIndexMap
                                  ruleMap)
                                (\ d ->
                                  Xmlt.xml_return
                                    (Check_Infeasibility.Infeasible_Trans a b c
                                      d)))))))
                (Xmlt.xml_or
                  (Xmlt.xml_do "infeasibleSplitIf"
                    (Xmlt.xml_take (split_if_info xml2name termIndexMap)
                      (\ a ->
                        Xmlt.xml_take
                          (xml2nonreachability_proof xml2name termIndexMap
                            ruleMap)
                          (\ b ->
                            Xmlt.xml_return
                              (Check_Infeasibility.Infeasible_Split_If a b)))))
                  (Xmlt.xml_or
                    (Xmlt.xml_do "infeasibleGoalLifting"
                      (Xmlt.xml_take xml2name
                        (\ a ->
                          Xmlt.xml_take xml2name
                            (\ b ->
                              Xmlt.xml_take
                                (xml2infeasibility_proof xml2name termIndexMap
                                  ruleMap)
                                (\ c ->
                                  Xmlt.xml_return
                                    (Check_Infeasibility.Infeasible_Goal_Lifting
                                      a b c))))))
                    (Xmlt.xml_or
                      (Xmlt.xml_do "ifritRules"
                        (Xmlt.xml_take
                          (Xmlt.xml_do "rules"
                            (Xmlt.xml_take_many_sub [] Arith.zero_nat
                              Extended_Nat.Infinity_enat
                              (CPF_Input_Parser.crule xml2name termIndexMap
                                "rule")
                              Xmlt.xml_return))
                          (\ a ->
                            Xmlt.xml_take
                              (xml2infeasibility_proof xml2name termIndexMap
                                ruleMap)
                              (\ b ->
                                Xmlt.xml_return
                                  ((Check_Infeasibility.Infeasible_Transform .
                                     Check_Infeasibility.Ifrit_Rules_Inf)
                                    a b)))))
                      (Xmlt.xml_or
                        (Xmlt.xml_do "leftInlineConditions"
                          (Xmlt.xml_take
                            (Xmlt.xml_do "rules"
                              (Xmlt.xml_take_many_sub [] Arith.zero_nat
                                Extended_Nat.Infinity_enat
                                (CPF_Input_Parser.crule xml2name termIndexMap
                                  "rule")
                                Xmlt.xml_return))
                            (\ a ->
                              Xmlt.xml_take
                                (xml2inline_cond_info xml2name termIndexMap)
                                (\ b ->
                                  Xmlt.xml_take
                                    (xml2infeasibility_proof xml2name
                                      termIndexMap ruleMap)
                                    (\ c ->
                                      Xmlt.xml_return
((Check_Infeasibility.Infeasible_Transform .
   Check_Infeasibility.Left_Inline_Conditions_Inf a)
  b c))))))
                        (Xmlt.xml_do "rightInlineConditions"
                          (Xmlt.xml_take
                            (Xmlt.xml_do "rules"
                              (Xmlt.xml_take_many_sub [] Arith.zero_nat
                                Extended_Nat.Infinity_enat
                                (CPF_Input_Parser.crule xml2name termIndexMap
                                  "rule")
                                Xmlt.xml_return))
                            (\ a ->
                              Xmlt.xml_take
                                (xml2inline_cond_info xml2name termIndexMap)
                                (\ b ->
                                  Xmlt.xml_take
                                    (xml2infeasibility_proof xml2name
                                      termIndexMap ruleMap)
                                    (\ c ->
                                      Xmlt.xml_return
((Check_Infeasibility.Infeasible_Transform .
   Check_Infeasibility.Right_Inline_Conditions_Inf a)
  b c)))))))))))))))
      (\ xa -> Xmlt.xml_return (id xa)))
    x;

xml2infeasible_rules_info ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term (Labelings.Lab a b)
 [Arith.Char],
Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  [(((Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char],
       Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]),
      [(Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char],
         Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char])]),
     Check_Infeasibility.Infeasibility_proof a [Arith.Char]
       (Reduction_Pair_Implementations.Redtriple_impl (Labelings.Lab a b)) b)];
xml2infeasible_rules_info xml2name termIndexMap ruleMap =
  Xmlt.xml_do "infeasibleRules"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (Xmlt.xml_do "infeasibleRule"
        (Xmlt.xml_take (CPF_Input_Parser.crule xml2name termIndexMap "rule")
          (\ a ->
            Xmlt.xml_take
              (xml2infeasibility_proof xml2name termIndexMap ruleMap)
              (\ b -> Xmlt.xml_return (a, b)))))
      (\ a -> Xmlt.xml_return (id a)));

compatible_ta ::
  forall a b.
    (Compare.Compare_order a, Shows_Literal.Showl a, Compare.Compare_order b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  String ->
                                    (Xml.Xml,
                                      ([([Arith.Char], [Arith.Char])],
(Bool, ([String], [String])))) ->
                                      Strict_Sum.Sum_bot (Xmlt.Xml_error String)
(Tree_Automata_Impl.Tree_automaton [Arith.Char] (Labelings.Lab a b),
  Tree_Automata_Impl.Ta_relation [Arith.Char]);
compatible_ta xml2name tag =
  Xmlt.xml_do tag
    (Xmlt.xml_take
      (CPF_Input_Parser.tree_automaton
        (CPF_Input_Parser.ta_normal_lhs xml2name))
      (\ a ->
        Xmlt.xml_take_default Tree_Automata_Impl.Id_Relation closed_criterion
          (\ b -> Xmlt.xml_return (a, b))));

xml2non_join_info ::
  ((Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
      (Labelings.Lab [Arith.Char] [Arith.Nat])) ->
    Mapping.Mapping [Arith.Char]
      (Term_Rewriting.Term (Labelings.Lab [Arith.Char] [Arith.Nat])
        [Arith.Char]) ->
      Mapping.Mapping [Arith.Char]
        (Term_Rewriting.Term (Labelings.Lab [Arith.Char] [Arith.Nat])
           [Arith.Char],
          Term_Rewriting.Term (Labelings.Lab [Arith.Char] [Arith.Nat])
            [Arith.Char]) ->
        (Xml.Xml,
          ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
          Strict_Sum.Sum_bot (Xmlt.Xml_error String)
            (Non_Confluence_Impl.Non_join_info
              (Labelings.Lab [Arith.Char] [Arith.Nat]) [Arith.Char] [Arith.Char]
              (Reduction_Pair_Implementations.Redtriple_impl
                (Labelings.Lab [Arith.Char] [Arith.Nat])));
xml2non_join_info xml2name termIndexMap ruleMap x =
  Xmlt.xml_or (Xmlt.xml_leaf "distinctNormalForms" Non_Confluence_Impl.Diff_NFs)
    (Xmlt.xml_or
      (Xmlt.xml_leaf "capNotUnif"
        (Non_Confluence_Impl.Tcap_Non_Unif Check_CRP.default_grd_fun))
      (Xmlt.xml_or
        (Xmlt.xml_do "subterm"
          (Xmlt.xml_take CPF_Input_Parser.pos
            (\ a ->
              Xmlt.xml_take (xml2non_join_info xml2name termIndexMap ruleMap)
                (\ b -> Xmlt.xml_return (Non_Confluence_Impl.Subterm_NJ a b)))))
        (Xmlt.xml_or
          (Xmlt.xml_do "grounding"
            (Xmlt.xml_take (subst xml2name termIndexMap)
              (\ a ->
                Xmlt.xml_take (xml2non_join_info xml2name termIndexMap ruleMap)
                  (\ b ->
                    Xmlt.xml_return (Non_Confluence_Impl.Grounding a b)))))
          (Xmlt.xml_or
            (Xmlt.xml_do "emptyTreeAutomataIntersection"
              (Xmlt.xml_take (compatible_ta xml2name "firstAutomaton")
                (\ a ->
                  Xmlt.xml_take (compatible_ta xml2name "secondAutomaton")
                    (\ b ->
                      Xmlt.xml_return
                        ((case a of {
                           (ta1, rel1) ->
                             (\ (aa, ba) ->
                               Non_Confluence_Impl.Tree_Aut_Intersect_Empty ta1
                                 rel1 aa ba);
                         })
                          b)))))
            (Xmlt.xml_or
              (Xmlt.xml_do "differentInterpretation"
                (Xmlt.xml_take (sl_variant xml2name)
                  (\ xa ->
                    Xmlt.xml_return (Non_Confluence_Impl.Finite_Model_Gt xa))))
              (Xmlt.xml_or
                (Xmlt.xml_do "strictDecrease"
                  (Xmlt.xml_take (redtriple xml2name Labelings.Sharp False)
                    (\ xa ->
                      Xmlt.xml_return
                        (Non_Confluence_Impl.Discr_Pair_Gt
                          Reduction_Pair_Implementations.default_rel_impl xa))))
                (Xmlt.xml_or
                  (Xmlt.xml_do "argumentFilterNonJoin"
                    (Xmlt.xml_take (afs xml2name)
                      (\ a ->
                        Xmlt.xml_take
                          (xml2non_join_info xml2name termIndexMap ruleMap)
                          (\ b ->
                            Xmlt.xml_return
                              (Non_Confluence_Impl.Argument_Filter_NJ a b)))))
                  (Xmlt.xml_or
                    (Xmlt.xml_do "usableRulesNonJoin"
                      (Xmlt.xml_take_optional
                        (Xmlt.xml_or (Xmlt.xml_leaf "left" True)
                          (Xmlt.xml_leaf "right" False))
                        (\ a ->
                          (case a of {
                            Nothing ->
                              Xmlt.xml_take
                                (xml2non_join_info xml2name termIndexMap
                                  ruleMap)
                                (\ b ->
                                  Xmlt.xml_return
                                    (Non_Confluence_Impl.Usable_Rules_Reach_NJ
                                      b));
                            Just left ->
                              Xmlt.xml_take
                                (Xmlt.xml_do "usableRules"
                                  (Xmlt.xml_take
                                    (CPF_Input_Parser.rules xml2name
                                      termIndexMap ruleMap)
                                    (\ xa -> Xmlt.xml_return (id xa))))
                                (\ u ->
                                  Xmlt.xml_take
                                    (xml2non_join_info xml2name termIndexMap
                                      ruleMap)
                                    (\ p ->
                                      Xmlt.xml_return
(Non_Confluence_Impl.Usable_Rules_Reach_Unif_NJ
  (if left then Sum_Type.Inl u else Sum_Type.Inr u) p)));
                          }))))
                    (Xmlt.xml_leaf "finitelyReachable"
                      Non_Confluence_Impl.Finitely_Reachable)))))))))
    x;

xml2ms_signature ::
  forall a b.
    (Compare.Compare_order a, Shows_Literal.Showl a, Compare.Compare_order b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  (Xml.Xml,
                                    ([([Arith.Char], [Arith.Char])],
                                      (Bool, ([String], [String])))) ->
                                    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                      [(Labelings.Lab a b,
 ([[Arith.Char]], [Arith.Char]))];
xml2ms_signature xml2name =
  Xmlt.xml_do "manySortedSignature"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (Xmlt.xml_do "manySortedFunction"
        (Xmlt.xml_take xml2name
          (\ a ->
            Xmlt.xml_take
              (Xmlt.xml_do "args"
                (Xmlt.xml_take_many_sub [] Arith.zero_nat
                  Extended_Nat.Infinity_enat (Xmlt.xml_text "sort")
                  (\ aa -> Xmlt.xml_return (id aa))))
              (\ b ->
                Xmlt.xml_take
                  (Xmlt.xml_do "result"
                    (Xmlt.xml_take (Xmlt.xml_text "sort")
                      (\ x -> Xmlt.xml_return (id x))))
                  (\ c -> Xmlt.xml_return (a, (b, c)))))))
      (\ a -> Xmlt.xml_return (id a)));

xml2ncr_proof ::
  ((Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
      (Labelings.Lab [Arith.Char] [Arith.Nat])) ->
    Mapping.Mapping [Arith.Char]
      (Term_Rewriting.Term (Labelings.Lab [Arith.Char] [Arith.Nat])
        [Arith.Char]) ->
      Mapping.Mapping [Arith.Char]
        (Term_Rewriting.Term (Labelings.Lab [Arith.Char] [Arith.Nat])
           [Arith.Char],
          Term_Rewriting.Term (Labelings.Lab [Arith.Char] [Arith.Nat])
            [Arith.Char]) ->
        (Xml.Xml,
          ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
          Strict_Sum.Sum_bot (Xmlt.Xml_error String)
            (Check_CRP.Ncr_proof [Arith.Char] [Arith.Nat] [Arith.Char]
              [Arith.Char]);
xml2ncr_proof xml2name termIndexMap ruleMap x =
  let {
    rew = rsteps xml2name termIndexMap ruleMap;
  } in Xmlt.xml_do "crDisproof"
         (Xmlt.xml_take
           (Xmlt.xml_or
             (Xmlt.xml_do "nonWcrAndSN"
               (Xmlt.xml_take (\ xa -> Strict_Sum.right (fst xa))
                 (\ _ ->
                   Xmlt.xml_take
                     (xml2trs_termination_proof xml2name termIndexMap ruleMap)
                     (\ prf -> Xmlt.xml_return (Check_CRP.SN_NWCR prf)))))
             (Xmlt.xml_or
               (Xmlt.xml_do "nonJoinableFork"
                 (Xmlt.xml_take rew
                   (\ a ->
                     Xmlt.xml_take rew
                       (\ b ->
                         Xmlt.xml_take
                           (xml2non_join_info xml2name termIndexMap ruleMap)
                           (\ c ->
                             Xmlt.xml_return
                               ((case a of {
                                  (s, seq1) ->
                                    (\ (_, aa) -> Check_CRP.Non_Join s seq1 aa);
                                })
                                  b
                                 c))))))
               (Xmlt.xml_or
                 (Xmlt.xml_do "modularityDisjoint"
                   (Xmlt.xml_take
                     (Xmlt.xml_do "trs"
                       (Xmlt.xml_take
                         (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                         (\ xa -> Xmlt.xml_return (id xa))))
                     (\ a ->
                       Xmlt.xml_take
                         (xml2ncr_proof xml2name termIndexMap ruleMap)
                         (\ b ->
                           Xmlt.xml_return (Check_CRP.NCR_Disj_Subtrs a b)))))
                 (Xmlt.xml_or
                   (Xmlt.xml_do "redundantRules"
                     (Xmlt.xml_take
                       (Xmlt.xml_do "trs"
                         (Xmlt.xml_take
                           (CPF_Input_Parser.rules xml2name termIndexMap
                             ruleMap)
                           (\ xa -> Xmlt.xml_return (id xa))))
                       (\ a ->
                         Xmlt.xml_take (Xmlt.xml_nat "nrSteps")
                           (\ b ->
                             Xmlt.xml_take
                               (xml2ncr_proof xml2name termIndexMap ruleMap)
                               (\ c ->
                                 Xmlt.xml_return
                                   (Check_CRP.NCR_Redundant_Rules a b c))))))
                   (Xmlt.xml_or
                     (Xmlt.xml_do "ruleRemoval"
                       (Xmlt.xml_take
                         (Xmlt.xml_do "removedRules"
                           (Xmlt.xml_take
                             (CPF_Input_Parser.rules xml2name termIndexMap
                               ruleMap)
                             (\ xa -> Xmlt.xml_return (id xa))))
                         (\ a ->
                           Xmlt.xml_take
                             (Xmlt.xml_do "simulations"
                               (Xmlt.xml_take_many_sub [] Arith.zero_nat
                                 Extended_Nat.Infinity_enat
                                 (Xmlt.xml_do "ruleSimulation"
                                   (Xmlt.xml_take
                                     (CPF_Input_Parser.rule xml2name
                                       termIndexMap ruleMap)
                                     (\ aa ->
                                       Xmlt.xml_take rew
 (\ b -> Xmlt.xml_return (aa, snd b)))))
                                 (\ aa -> Xmlt.xml_return (id aa))))
                             (\ b ->
                               Xmlt.xml_take
                                 (xml2ncr_proof xml2name termIndexMap ruleMap)
                                 (\ c ->
                                   Xmlt.xml_return
                                     (Check_CRP.NCR_Rule_Removal a b c))))))
                     (Xmlt.xml_do "persistentDecomposition"
                       (Xmlt.xml_take (xml2ms_signature xml2name)
                         (\ a ->
                           Xmlt.xml_take
                             (Xmlt.xml_do "component"
                               (Xmlt.xml_take
                                 (Xmlt.xml_do "trs"
                                   (Xmlt.xml_take
                                     (CPF_Input_Parser.rules xml2name
                                       termIndexMap ruleMap)
                                     (\ xa -> Xmlt.xml_return (id xa))))
                                 (\ aa ->
                                   Xmlt.xml_take
                                     (xml2ncr_proof xml2name termIndexMap
                                       ruleMap)
                                     (\ b -> Xmlt.xml_return (aa, b)))))
                             (\ b ->
                               Xmlt.xml_return
                                 (case b of {
                                   (ba, c) ->
                                     Check_CRP.NCR_Persistent_Decomposition a ba
                                       c;
                                 }))))))))))
           (\ xa -> Xmlt.xml_return (id xa)))
         x;

xml2conditional_ncr_proof ::
  ((Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
      (Labelings.Lab [Arith.Char] [Arith.Nat])) ->
    Mapping.Mapping [Arith.Char]
      (Term_Rewriting.Term (Labelings.Lab [Arith.Char] [Arith.Nat])
        [Arith.Char]) ->
      Mapping.Mapping [Arith.Char]
        (Term_Rewriting.Term (Labelings.Lab [Arith.Char] [Arith.Nat])
           [Arith.Char],
          Term_Rewriting.Term (Labelings.Lab [Arith.Char] [Arith.Nat])
            [Arith.Char]) ->
        (Xml.Xml,
          ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
          Strict_Sum.Sum_bot (Xmlt.Xml_error String)
            (Check_Conditional_CRP.Conditional_ncr_proof [Arith.Char]
              [Arith.Nat] [Arith.Char] [Arith.Char]
              (Reduction_Pair_Implementations.Redtriple_impl
                (Labelings.Lab [Arith.Char] [Arith.Nat])));
xml2conditional_ncr_proof xml2name termIndexMap ruleMap x =
  Xmlt.xml_do "conditionalCrDisproof"
    (Xmlt.xml_take
      (Xmlt.xml_or
        (Xmlt.xml_do "unconditional"
          (Xmlt.xml_take (xml2ncr_proof xml2name termIndexMap ruleMap)
            (\ xa ->
              Xmlt.xml_return (Check_Conditional_CRP.Unconditional_CNCR xa))))
        (Xmlt.xml_or
          (Xmlt.xml_do "inlineConditions"
            (Xmlt.xml_take
              (Xmlt.xml_do "rules"
                (Xmlt.xml_take_many_sub [] Arith.zero_nat
                  Extended_Nat.Infinity_enat
                  (CPF_Input_Parser.crule xml2name termIndexMap "rule")
                  Xmlt.xml_return))
              (\ a ->
                Xmlt.xml_take (xml2inline_cond_info xml2name termIndexMap)
                  (\ b ->
                    Xmlt.xml_take
                      (xml2conditional_ncr_proof xml2name termIndexMap ruleMap)
                      (\ c ->
                        Xmlt.xml_return
                          ((Check_Conditional_CRP.Transformation_CNCR .
                             Check_Conditional_CRP.Inline_Conditions_CCRT a)
                            b c))))))
          (Xmlt.xml_or
            (Xmlt.xml_do "infeasibleRuleRemoval"
              (Xmlt.xml_take
                (xml2infeasible_rules_info xml2name termIndexMap ruleMap)
                (\ a ->
                  Xmlt.xml_take
                    (xml2conditional_ncr_proof xml2name termIndexMap ruleMap)
                    (\ b ->
                      Xmlt.xml_return
                        ((Check_Conditional_CRP.Transformation_CNCR .
                           Check_Conditional_CRP.Infeasible_Rule_Removal_CCRT)
                          a b)))))
            (Xmlt.xml_do "nonJoinableFork"
              (Xmlt.xml_take
                (Xmlt.xml_do "terms"
                  (Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
                    (\ a ->
                      Xmlt.xml_take
                        (CPF_Input_Parser.term xml2name termIndexMap)
                        (\ b ->
                          Xmlt.xml_take
                            (CPF_Input_Parser.term xml2name termIndexMap)
                            (\ c -> Xmlt.xml_return (a, (b, c)))))))
                (\ a ->
                  Xmlt.xml_take (csteps xml2name termIndexMap)
                    (\ b ->
                      Xmlt.xml_take (csteps xml2name termIndexMap)
                        (\ c ->
                          Xmlt.xml_take
                            (xml2non_join_info xml2name termIndexMap ruleMap)
                            (\ d ->
                              Xmlt.xml_return
                                ((case a of {
                                   (s, (aa, ba)) ->
                                     Check_Conditional_CRP.Non_Join_CNCR s aa
                                       ba;
                                 })
                                   b
                                   c
                                  d))))))))))
      (\ xa -> Xmlt.xml_return (id xa)))
    x;

xml2const_map ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  (Xml.Xml,
                                    ([([Arith.Char], [Arith.Char])],
                                      (Bool, ([String], [String])))) ->
                                    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                      (Labelings.Lab a b -> Maybe [Arith.Char]);
xml2const_map xml2name =
  Xmlt.xml_do "constMap"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (Xmlt.xml_do "entry"
        (Xmlt.xml_take
          (Xmlt.xml_do "symbol"
            (Xmlt.xml_take xml2name (\ x -> Xmlt.xml_return (id x))))
          (\ a ->
            Xmlt.xml_take (Xmlt.xml_text "const")
              (\ b -> Xmlt.xml_return (a, b)))))
      (\ a -> Xmlt.xml_return (Map.map_of a)));

xml2context_joinable_proof ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    (Xml.Xml,
                                      ([([Arith.Char], [Arith.Char])],
(Bool, ([String], [String])))) ->
                                      Strict_Sum.Sum_bot (Xmlt.Xml_error String)
(Check_AL94.Context_joinable_proof (Labelings.Lab a b) [Arith.Char]);
xml2context_joinable_proof xml2name termIndexMap =
  Xmlt.xml_do "contextJoinabilityProof"
    (Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
      (\ a ->
        Xmlt.xml_take (csteps xml2name termIndexMap)
          (\ b ->
            Xmlt.xml_take (csteps xml2name termIndexMap)
              (\ c ->
                Xmlt.xml_take (xml2const_map xml2name)
                  (\ d ->
                    Xmlt.xml_return
                      (Check_AL94.Contextual_Join (Check_AL94.orig_term d a)
                        (map (Check_AL94.orig_cstep d) b)
                        (map (Check_AL94.orig_cstep d) c)))))));

xml2context_joinable_ccps ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    (Xml.Xml,
                                      ([([Arith.Char], [Arith.Char])],
(Bool, ([String], [String])))) ->
                                      Strict_Sum.Sum_bot (Xmlt.Xml_error String)
[(Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char],
   (Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char],
     ([(Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char],
         Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char])],
       Check_AL94.Context_joinable_proof (Labelings.Lab a b) [Arith.Char])))];
xml2context_joinable_ccps xml2name termIndexMap =
  Xmlt.xml_do "contextJoinableCCPs"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (Xmlt.xml_do "contextJoinableCCP"
        (Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
          (\ s ->
            Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
              (\ t ->
                Xmlt.xml_take
                  (CPF_Input_Parser.conditions xml2name termIndexMap
                    "conditions")
                  (\ cs ->
                    Xmlt.xml_take
                      (xml2context_joinable_proof xml2name termIndexMap)
                      (\ p -> Xmlt.xml_return (s, (t, (cs, p)))))))))
      Xmlt.xml_return);

xml2ao_infeasibility_proof ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term (Labelings.Lab a b)
 [Arith.Char],
Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Check_Level_Confluence.Ao_infeasibility_proof a [Arith.Char]
    (Reduction_Pair_Implementations.Redtriple_impl (Labelings.Lab a b)) b);
xml2ao_infeasibility_proof xml2name termIndexMap ruleMap =
  Xmlt.xml_do "aoInfeasibilityProof"
    (Xmlt.xml_take
      (Xmlt.xml_or
        (Xmlt.xml_change (xml2infeasibility_proof xml2name termIndexMap ruleMap)
          (Xmlt.xml_return . Check_Level_Confluence.AO_Infeasibility_Proof))
        (Xmlt.xml_do "aoLhssEqual"
          (Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
            (\ a ->
              Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
                (\ b ->
                  Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
                    (\ c ->
                      Xmlt.xml_take
                        (xml2nonjoinability_proof xml2name termIndexMap ruleMap)
                        (\ d ->
                          Xmlt.xml_return
                            (Check_Level_Confluence.AO_Lhss_Equal a b c
                              d))))))))
      (\ x -> Xmlt.xml_return (id x)));

xml2ao_infeasible_conds ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term (Labelings.Lab a b)
 [Arith.Char],
Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  [([(Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char],
       Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char])],
     ([(Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char],
         Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char])],
       Check_Level_Confluence.Ao_infeasibility_proof a [Arith.Char]
         (Reduction_Pair_Implementations.Redtriple_impl (Labelings.Lab a b))
         b))];
xml2ao_infeasible_conds xml2name termIndexMap ruleMap =
  Xmlt.xml_do "aoInfeasibleConditions"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (Xmlt.xml_do "aoInfeasibleCondition"
        (Xmlt.xml_take
          (CPF_Input_Parser.conditions xml2name termIndexMap "conditions")
          (\ a ->
            Xmlt.xml_take
              (CPF_Input_Parser.conditions xml2name termIndexMap "conditions")
              (\ b ->
                Xmlt.xml_take
                  (xml2ao_infeasibility_proof xml2name termIndexMap ruleMap)
                  (\ c -> Xmlt.xml_return (a, (b, c)))))))
      (\ a -> Xmlt.xml_return (id a)));

xml2infeasible_conds ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term (Labelings.Lab a b)
 [Arith.Char],
Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  [([(Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char],
       Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char])],
     Check_Infeasibility.Infeasibility_proof a [Arith.Char]
       (Reduction_Pair_Implementations.Redtriple_impl (Labelings.Lab a b)) b)];
xml2infeasible_conds xml2name termIndexMap ruleMap =
  Xmlt.xml_do "infeasibleConditions"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (Xmlt.xml_do "infeasibleCondition"
        (Xmlt.xml_take
          (CPF_Input_Parser.conditions xml2name termIndexMap "conditions")
          (\ a ->
            Xmlt.xml_take
              (xml2infeasibility_proof xml2name termIndexMap ruleMap)
              (\ b -> Xmlt.xml_return (a, b)))))
      (\ a -> Xmlt.xml_return (id a)));

xml2unfeasible_proof ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    (Xml.Xml,
                                      ([([Arith.Char], [Arith.Char])],
(Bool, ([String], [String])))) ->
                                      Strict_Sum.Sum_bot (Xmlt.Xml_error String)
(Check_AL94.Unfeasible_proof (Labelings.Lab a b) [Arith.Char]);
xml2unfeasible_proof xml2name termIndexMap =
  Xmlt.xml_do "unfeasibilityProof"
    (Xmlt.xml_take
      (Xmlt.xml_do "terms"
        (Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
          (\ a ->
            Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
              (\ b ->
                Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
                  (\ c -> Xmlt.xml_return (a, (b, c)))))))
      (\ a ->
        Xmlt.xml_take (csteps xml2name termIndexMap)
          (\ b ->
            Xmlt.xml_take (csteps xml2name termIndexMap)
              (\ c ->
                Xmlt.xml_take
                  (Xmlt.xml_do "rules"
                    (Xmlt.xml_take
                      (CPF_Input_Parser.crule xml2name termIndexMap "rule")
                      (\ aa ->
                        Xmlt.xml_take
                          (CPF_Input_Parser.crule xml2name termIndexMap "rule")
                          (\ ba -> Xmlt.xml_return (aa, ba)))))
                  (\ d ->
                    Xmlt.xml_take (xml2const_map xml2name)
                      (\ e ->
                        Xmlt.xml_return
                          ((case a of {
                             (t, (u, v)) ->
                               (\ ps qs (r, ra) m ->
                                 Check_AL94.UnfeasibleOverlap
                                   (Check_AL94.orig_term m t)
                                   (Check_AL94.orig_term m u)
                                   (Check_AL94.orig_term m v)
                                   (map (Check_AL94.orig_cstep m) ps)
                                   (map (Check_AL94.orig_cstep m) qs) r ra);
                           })
                             b
                             c
                             d
                            e)))))));

xml2unfeasible_ccps ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    (Xml.Xml,
                                      ([([Arith.Char], [Arith.Char])],
(Bool, ([String], [String])))) ->
                                      Strict_Sum.Sum_bot (Xmlt.Xml_error String)
[([Arith.Char] -> Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char],
   Check_AL94.Unfeasible_proof (Labelings.Lab a b) [Arith.Char])];
xml2unfeasible_ccps xml2name termIndexMap =
  Xmlt.xml_do "unfeasibleCCPs"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (Xmlt.xml_do "unfeasibleCCP"
        (Xmlt.xml_take (subst xml2name termIndexMap)
          (\ a ->
            Xmlt.xml_take (xml2unfeasible_proof xml2name termIndexMap)
              (\ b -> Xmlt.xml_return (Term_Rewriting.subst_of a, b)))))
      (\ a -> Xmlt.xml_return (id a)));

rule_labeling_function ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
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
                                       ([([Arith.Char], [Arith.Char])],
 (Bool, ([String], [String])))) ->
                                       Strict_Sum.Sum_bot
 (Xmlt.Xml_error String)
 [((Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char]),
    Arith.Nat)];
rule_labeling_function xml2name termIndexMap ruleMap =
  Xmlt.xml_do "ruleLabelingFunction"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (Xmlt.xml_do "ruleLabelingFunctionEntry"
        (Xmlt.xml_take (CPF_Input_Parser.rule xml2name termIndexMap ruleMap)
          (\ a ->
            Xmlt.xml_take (Xmlt.xml_nat "label")
              (\ b -> Xmlt.xml_return (a, b)))))
      (\ a -> Xmlt.xml_return (id a)));

add_source_lab_proof ::
  forall a b c.
    Check_CRP.Cr_proof a b c ->
      Maybe Arith.Nat ->
        Check_Termination.Trs_termination_proof a b c ->
          Check_CRP.Cr_proof a b c;
add_source_lab_proof (Check_CRP.Rule_Labeling rl js uu) uv prf =
  Check_CRP.Rule_Labeling rl js (Just prf);
add_source_lab_proof (Check_CRP.Rule_Labeling_Conv rl cs uw) (Just n) prf =
  Check_CRP.Rule_Labeling_Conv rl cs (Just (n, prf));

xml2cr_proof ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term (Labelings.Lab a b)
 [Arith.Char],
Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Check_CRP.Cr_proof a b [Arith.Char]);
xml2cr_proof xml2name termIndexMap ruleMap x =
  Xmlt.xml_do "crProof"
    (Xmlt.xml_take
      (Xmlt.xml_or
        (Xmlt.xml_do "wcrAndSN"
          (Xmlt.xml_take (wcr_proof xml2name termIndexMap)
            (\ a ->
              Xmlt.xml_take
                (xml2trs_termination_proof xml2name termIndexMap ruleMap)
                (\ b -> Xmlt.xml_return (Check_CRP.SN_WCR a b)))))
        (Xmlt.xml_or (Xmlt.xml_leaf "orthogonal" Check_CRP.Weakly_Orthogonal)
          (Xmlt.xml_or
            (Xmlt.xml_do "stronglyClosed"
              (Xmlt.xml_take joinAutoBfs1
                (\ n -> Xmlt.xml_return (Check_CRP.Strongly_Closed n))))
            (Xmlt.xml_or
              (Xmlt.xml_do "parallelClosed"
                (Xmlt.xml_take joinAutoBfs
                  (\ n -> Xmlt.xml_return (Check_CRP.Parallel_Closed n))))
              (Xmlt.xml_or
                (Xmlt.xml_do "pcpClosed"
                  (Xmlt.xml_take
                    (Xmlt.xml_do "ordinaryCriticalPairs"
                      (Xmlt.xml_take (xml2cp_join_info xml2name termIndexMap)
                        (\ xa -> Xmlt.xml_return (id xa))))
                    (\ hints_cp ->
                      Xmlt.xml_take
                        (Xmlt.xml_do "parallelCriticalPairs"
                          (Xmlt.xml_take
                            (xml2cp_join_info xml2name termIndexMap)
                            (\ xa -> Xmlt.xml_return (id xa))))
                        (\ hints_pcp ->
                          Xmlt.xml_return
                            (Check_CRP.PCP_Closed hints_cp hints_pcp)))))
                (Xmlt.xml_or
                  (Xmlt.xml_do "compositionalPcp"
                    (Xmlt.xml_take
                      (Xmlt.xml_do "trs"
                        (Xmlt.xml_take
                          (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                          (\ xa -> Xmlt.xml_return (id xa))))
                      (\ trsC ->
                        Xmlt.xml_take (xml2cp_join_info xml2name termIndexMap)
                          (\ hints ->
                            Xmlt.xml_take
                              (xml2cr_proof xml2name termIndexMap ruleMap)
                              (\ prf ->
                                Xmlt.xml_return
                                  (Check_CRP.Compositional_PCP trsC hints
                                    prf))))))
                  (Xmlt.xml_or
                    (Xmlt.xml_do "compositionalPcps"
                      (Xmlt.xml_take
                        (Xmlt.xml_do "trsC"
                          (Xmlt.xml_take
                            (CPF_Input_Parser.rules xml2name termIndexMap
                              ruleMap)
                            (\ xa -> Xmlt.xml_return (id xa))))
                        (\ trsC ->
                          Xmlt.xml_take
                            (Xmlt.xml_do "trsP"
                              (Xmlt.xml_take
                                (CPF_Input_Parser.rules xml2name termIndexMap
                                  ruleMap)
                                (\ xa -> Xmlt.xml_return (id xa))))
                            (\ trsP ->
                              Xmlt.xml_take
                                (xml2cp_join_info xml2name termIndexMap)
                                (\ hintsP ->
                                  Xmlt.xml_take
                                    (xml2cp_join_info xml2name termIndexMap)
                                    (\ hints ->
                                      Xmlt.xml_take
(xml2trs_termination_proof xml2name termIndexMap ruleMap)
(\ sn_prf ->
  Xmlt.xml_take (xml2cr_proof xml2name termIndexMap ruleMap)
    (\ cr_prf ->
      Xmlt.xml_return
        (Check_CRP.Compositional_PCPS trsC trsP hintsP hints sn_prf
          cr_prf)))))))))
                    (Xmlt.xml_or
                      (Xmlt.xml_do "developmentClosed"
                        (Xmlt.xml_take joinAutoBfs
                          (\ n ->
                            Xmlt.xml_return (Check_CRP.Development_Closed n))))
                      (Xmlt.xml_or
                        (Xmlt.xml_do "criticalPairClosingSystem"
                          (Xmlt.xml_take
                            (Xmlt.xml_do "trs"
                              (Xmlt.xml_take
                                (CPF_Input_Parser.rules xml2name termIndexMap
                                  ruleMap)
                                (\ xa -> Xmlt.xml_return (id xa))))
                            (\ a ->
                              Xmlt.xml_take
                                (xml2trs_termination_proof xml2name termIndexMap
                                  ruleMap)
                                (\ b ->
                                  Xmlt.xml_take joinAutoBfs1
                                    (\ c ->
                                      Xmlt.xml_return
(Check_CRP.Critical_Pair_Closing_System a b c))))))
                        (Xmlt.xml_or
                          (Xmlt.xml_do "ruleLabeling"
                            (Xmlt.xml_take
                              (rule_labeling_function xml2name termIndexMap
                                ruleMap)
                              (\ a ->
                                Xmlt.xml_take
                                  (joinSequences xml2name termIndexMap)
                                  (\ b ->
                                    Xmlt.xml_return
                                      (Check_CRP.Rule_Labeling a b Nothing)))))
                          (Xmlt.xml_or
                            (Xmlt.xml_do "pcpRuleLabeling"
                              (Xmlt.xml_take
                                (rule_labeling_function xml2name termIndexMap
                                  ruleMap)
                                (\ lab ->
                                  Xmlt.xml_take
                                    (xml2cp_join_info xml2name termIndexMap)
                                    (\ joins ->
                                      Xmlt.xml_return
(Check_CRP.PCP_Rule_Lab
  (Parallel_Critical_Pairs_Impl.PCP_Sequences
    (Rule_Labeling_Impl.rule_lab_repr_to_lab lab) joins))))))
                            (Xmlt.xml_or
                              (Xmlt.xml_do "compositionalPcpRuleLabeling"
                                (Xmlt.xml_take
                                  (rule_labeling_function xml2name termIndexMap
                                    ruleMap)
                                  (\ lab ->
                                    Xmlt.xml_take_optional
                                      (rule_labeling_function xml2name
termIndexMap ruleMap)
                                      (\ laba ->
Xmlt.xml_take
  (Xmlt.xml_do "joinsRS"
    (Xmlt.xml_take (xml2cp_join_info xml2name termIndexMap)
      (\ xa -> Xmlt.xml_return (id xa))))
  (\ joinsRS ->
    Xmlt.xml_take_optional
      (Xmlt.xml_do "joinsSR"
        (Xmlt.xml_take (xml2cp_join_info xml2name termIndexMap)
          (\ xa -> Xmlt.xml_return (id xa))))
      (\ joinsSR ->
        Xmlt.xml_take
          (Xmlt.xml_do "trs"
            (Xmlt.xml_take
              (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
              (\ xa -> Xmlt.xml_return (id xa))))
          (\ trs ->
            Xmlt.xml_take (xml2cr_proof xml2name termIndexMap ruleMap)
              (\ subPrf ->
                Xmlt.xml_return
                  (Check_CRP.Compositional_PCP_Rule_Lab trs
                    (Parallel_Critical_Pairs_Impl.PCP_Sequences_Com
                      (Rule_Labeling_Impl.rule_lab_repr_to_lab lab)
                      (Arith.map_option Rule_Labeling_Impl.rule_lab_repr_to_lab
                        laba)
                      joinsRS (case joinsSR of {
                                Nothing -> joinsRS;
                                Just j -> j;
                              }))
                    subPrf)))))))))
                              (Xmlt.xml_or
                                (Xmlt.xml_do "decreasingDiagrams"
                                  (Xmlt.xml_take_optional
                                    (xml2trs_termination_proof xml2name
                                      termIndexMap ruleMap)
                                    (\ a ->
                                      Xmlt.xml_take
(Xmlt.xml_or
  (Xmlt.xml_do "ruleLabeling"
    (Xmlt.xml_take (rule_labeling_function xml2name termIndexMap ruleMap)
      (\ rl ->
        Xmlt.xml_take (joinSequences xml2name termIndexMap)
          (\ js ->
            (case a of {
              Nothing ->
                Xmlt.xml_return (Check_CRP.Rule_Labeling rl js Nothing);
              Just prf ->
                Xmlt.xml_return
                  (add_source_lab_proof (Check_CRP.Rule_Labeling rl js Nothing)
                    Nothing prf);
            })))))
  (Xmlt.xml_do "ruleLabelingConv"
    (Xmlt.xml_take (rule_labeling_function xml2name termIndexMap ruleMap)
      (\ rl ->
        Xmlt.xml_take (joinSequences xml2name termIndexMap)
          (\ cs ->
            (case a of {
              Nothing ->
                Xmlt.xml_return (Check_CRP.Rule_Labeling_Conv rl cs Nothing);
              Just prf ->
                Xmlt.xml_take (Xmlt.xml_nat "nrSteps")
                  (\ n ->
                    Xmlt.xml_return
                      (add_source_lab_proof
                        (Check_CRP.Rule_Labeling_Conv rl cs Nothing) (Just n)
                        prf));
            }))))))
Xmlt.xml_return)))
                                (Xmlt.xml_or
                                  (Xmlt.xml_do "redundantRules"
                                    (Xmlt.xml_take
                                      (Xmlt.xml_do "trs"
(Xmlt.xml_take (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
  (\ xa -> Xmlt.xml_return (id xa))))
                                      (\ trs ->
Xmlt.xml_take (Xmlt.xml_nat "nrSteps")
  (\ n ->
    Xmlt.xml_take_default []
      (Xmlt.xml_do "conversions"
        (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
          (conversion xml2name termIndexMap) (\ a -> Xmlt.xml_return (id a))))
      (\ cs ->
        Xmlt.xml_take (xml2cr_proof xml2name termIndexMap ruleMap)
          (\ prf ->
            Xmlt.xml_return (Check_CRP.Redundant_Rules trs n cs prf)))))))
                                  (Xmlt.xml_do "persistentDecomposition"
                                    (Xmlt.xml_take (xml2ms_signature xml2name)
                                      (\ sig ->
Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
  (Xmlt.xml_do "component"
    (Xmlt.xml_take
      (Xmlt.xml_do "trs"
        (Xmlt.xml_take (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
          (\ xa -> Xmlt.xml_return (id xa))))
      (\ a ->
        Xmlt.xml_take (xml2cr_proof xml2name termIndexMap ruleMap)
          (\ b -> Xmlt.xml_return (a, b)))))
  (\ subs ->
    Xmlt.xml_return
      (Check_CRP.Persistent_Decomposition sig subs)))))))))))))))))))
      (\ xa -> Xmlt.xml_return (id xa)))
    x;

xml2conditional_cr_proof ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term (Labelings.Lab a b)
 [Arith.Char],
Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Check_Conditional_CRP.Conditional_cr_proof a b [Arith.Char]
    (Reduction_Pair_Implementations.Redtriple_impl (Labelings.Lab a b)));
xml2conditional_cr_proof xml2name termIndexMap ruleMap x =
  Xmlt.xml_do "conditionalCrProof"
    (Xmlt.xml_take
      (Xmlt.xml_or
        (Xmlt.xml_do "unconditional"
          (Xmlt.xml_take (xml2cr_proof xml2name termIndexMap ruleMap)
            (\ xa ->
              Xmlt.xml_return (Check_Conditional_CRP.Unconditional_CR xa))))
        (Xmlt.xml_or
          (Xmlt.xml_do "unraveling"
            (Xmlt.xml_take (unraveling_info xml2name termIndexMap ruleMap)
              (\ a ->
                Xmlt.xml_take (xml2cr_proof xml2name termIndexMap ruleMap)
                  (\ b ->
                    Xmlt.xml_return (Check_Conditional_CRP.Unravel_CR a b)))))
          (Xmlt.xml_or
            (Xmlt.xml_do "inlineConditions"
              (Xmlt.xml_take
                (Xmlt.xml_do "rules"
                  (Xmlt.xml_take_many_sub [] Arith.zero_nat
                    Extended_Nat.Infinity_enat
                    (CPF_Input_Parser.crule xml2name termIndexMap "rule")
                    Xmlt.xml_return))
                (\ a ->
                  Xmlt.xml_take (xml2inline_cond_info xml2name termIndexMap)
                    (\ b ->
                      Xmlt.xml_take
                        (xml2conditional_cr_proof xml2name termIndexMap ruleMap)
                        (\ c ->
                          Xmlt.xml_return
                            ((Check_Conditional_CRP.Transformation_CR .
                               Check_Conditional_CRP.Inline_Conditions_CCRT a)
                              b c))))))
            (Xmlt.xml_or
              (Xmlt.xml_do "infeasibleRuleRemoval"
                (Xmlt.xml_take
                  (xml2infeasible_rules_info xml2name termIndexMap ruleMap)
                  (\ a ->
                    Xmlt.xml_take
                      (xml2conditional_cr_proof xml2name termIndexMap ruleMap)
                      (\ b ->
                        Xmlt.xml_return
                          ((Check_Conditional_CRP.Transformation_CR .
                             Check_Conditional_CRP.Infeasible_Rule_Removal_CCRT)
                            a b)))))
              (Xmlt.xml_or
                (Xmlt.xml_leaf "almostOrthogonal"
                  Check_Conditional_CRP.Almost_Orthogonal_CR)
                (Xmlt.xml_or
                  (Xmlt.xml_do "almostOrthogonalModuloInfeasibility"
                    (Xmlt.xml_take
                      (xml2ao_infeasible_conds xml2name termIndexMap ruleMap)
                      (\ xa ->
                        Xmlt.xml_return
                          (Check_Conditional_CRP.Almost_Orthogonal_Modulo_Infeasibility_CR
                            xa))))
                  (Xmlt.xml_do "al94"
                    (Xmlt.xml_take
                      (xml2quasi_reductive_proof xml2name termIndexMap ruleMap)
                      (\ a ->
                        Xmlt.xml_take
                          (xml2context_joinable_ccps xml2name termIndexMap)
                          (\ b ->
                            Xmlt.xml_take
                              (xml2infeasible_conds xml2name termIndexMap
                                ruleMap)
                              (\ c ->
                                Xmlt.xml_take
                                  (xml2unfeasible_ccps xml2name termIndexMap)
                                  (\ d ->
                                    Xmlt.xml_return
                                      (Check_Conditional_CRP.AL94_CR a b c
d)))))))))))))
      (\ xa -> Xmlt.xml_return (id xa)))
    x;

xml2ac_dp_termination_proof ::
  forall a b.
    (Compare.Compare_order a, Shows_Literal.Showl a, Compare.Compare_order b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term (Labelings.Lab a b)
 [Arith.Char],
Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Check_AC_Termination.Ac_dp_termination_proof (Labelings.Lab a b)
    [Arith.Char]);
xml2ac_dp_termination_proof xml2name termIndexMap ruleMap x =
  Xmlt.xml_do "acDPTerminationProof"
    (Xmlt.xml_take
      (Xmlt.xml_or
        (Xmlt.xml_do "acRedPairProc"
          (Xmlt.xml_take (redtriple xml2name Labelings.Sharp False)
            (\ a ->
              Xmlt.xml_take
                (Xmlt.xml_do "dps"
                  (Xmlt.xml_take
                    (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                    (\ xa -> Xmlt.xml_return (id xa))))
                (\ b ->
                  Xmlt.xml_take
                    (Xmlt.xml_do "usableRules"
                      (Xmlt.xml_take
                        (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                        (\ xa -> Xmlt.xml_return (id xa))))
                    (\ c ->
                      Xmlt.xml_take
                        (xml2ac_dp_termination_proof xml2name termIndexMap
                          ruleMap)
                        (\ d ->
                          Xmlt.xml_return
                            (Check_AC_Termination.AC_Redpair_UR_Proc a b c
                              d)))))))
        (Xmlt.xml_or
          (Xmlt.xml_do "acSubtermProc"
            (Xmlt.xml_take (multiset_af xml2name)
              (\ pi ->
                Xmlt.xml_take
                  (Xmlt.xml_do "dps"
                    (Xmlt.xml_take
                      (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                      (\ xa -> Xmlt.xml_return (id xa))))
                  (\ r ->
                    Xmlt.xml_take
                      (xml2ac_dp_termination_proof xml2name termIndexMap
                        ruleMap)
                      (\ prf ->
                        Xmlt.xml_return
                          (Check_AC_Termination.AC_Subterm_Proc pi r prf))))))
          (Xmlt.xml_or
            (Xmlt.xml_do "acTrivialProc"
              (Xmlt.xml_return Check_AC_Termination.AC_P_is_Empty))
            (Xmlt.xml_or
              (Xmlt.xml_do "acMonoRedPairProc"
                (Xmlt.xml_take (redtriple xml2name Labelings.Sharp False)
                  (\ a ->
                    Xmlt.xml_take
                      (Xmlt.xml_do "dps"
                        (Xmlt.xml_take
                          (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                          (\ xa -> Xmlt.xml_return (id xa))))
                      (\ b ->
                        Xmlt.xml_take
                          (Xmlt.xml_do "trs"
                            (Xmlt.xml_take
                              (CPF_Input_Parser.rules xml2name termIndexMap
                                ruleMap)
                              (\ xa -> Xmlt.xml_return (id xa))))
                          (\ c ->
                            Xmlt.xml_take
                              (Xmlt.xml_do "usableRules"
                                (Xmlt.xml_take
                                  (CPF_Input_Parser.rules xml2name termIndexMap
                                    ruleMap)
                                  (\ xa -> Xmlt.xml_return (id xa))))
                              (\ d ->
                                Xmlt.xml_take
                                  (xml2ac_dp_termination_proof xml2name
                                    termIndexMap ruleMap)
                                  (\ e ->
                                    Xmlt.xml_return
                                      (Check_AC_Termination.AC_Mono_Redpair_UR_Proc
a b c d e))))))))
              (Xmlt.xml_do "acDepGraphProc"
                (Xmlt.xml_take_many_sub [] Arith.zero_nat
                  Extended_Nat.Infinity_enat
                  (Xmlt.xml_do "component"
                    (Xmlt.xml_take
                      (Xmlt.xml_do "dps"
                        (Xmlt.xml_take
                          (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                          (\ xa -> Xmlt.xml_return (id xa))))
                      (\ dps ->
                        Xmlt.xml_take_optional
                          (xml2ac_dp_termination_proof xml2name termIndexMap
                            ruleMap)
                          (\ prfOpt -> Xmlt.xml_return (prfOpt, dps)))))
                  (\ ret ->
                    Xmlt.xml_return
                      (Check_AC_Termination.AC_Dep_Graph_Proc ret))))))))
      (\ xa -> Xmlt.xml_return (id xa)))
    x;

xml2ac_termination_proof ::
  forall a b.
    (Compare.Compare_order a, Shows_Literal.Showl a, Compare.Compare_order b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term (Labelings.Lab a b)
 [Arith.Char],
Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Check_AC_Termination.Ac_termination_proof a b [Arith.Char]);
xml2ac_termination_proof xml2name termIndexMap ruleMap x =
  Xmlt.xml_do "acTerminationProof"
    (Xmlt.xml_take
      (Xmlt.xml_or
        (Xmlt.xml_do "acDependencyPairs"
          (Xmlt.xml_take
            (Xmlt.xml_do "equations"
              (Xmlt.xml_take
                (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                (\ xa -> Xmlt.xml_return (id xa))))
            (\ e ->
              Xmlt.xml_take
                (Xmlt.xml_do "dpEquations"
                  (Xmlt.xml_take
                    (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                    (\ xa -> Xmlt.xml_return (id xa))))
                (\ dpe ->
                  Xmlt.xml_take
                    (Xmlt.xml_do "dps"
                      (Xmlt.xml_take
                        (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                        (\ xa -> Xmlt.xml_return (id xa))))
                    (\ dp ->
                      Xmlt.xml_take
                        (Xmlt.xml_do "extensions"
                          (Xmlt.xml_take
                            (CPF_Input_Parser.rules xml2name termIndexMap
                              ruleMap)
                            (\ xa -> Xmlt.xml_return (id xa))))
                        (\ rext ->
                          Xmlt.xml_take
                            (xml2ac_dp_termination_proof xml2name termIndexMap
                              ruleMap)
                            (\ p1 ->
                              Xmlt.xml_take_optional
                                (xml2ac_dp_termination_proof xml2name
                                  termIndexMap ruleMap)
                                (\ a ->
                                  (case a of {
                                    Nothing ->
                                      Xmlt.xml_return
(Check_AC_Termination.AC_DP_Trans_Single
  (AC_Dependency_Pairs_Impl.AC_dependency_pairs_proof e dp dpe rext) p1);
                                    Just p2 ->
                                      Xmlt.xml_return
(Check_AC_Termination.AC_DP_Trans
  (AC_Dependency_Pairs_Impl.AC_dependency_pairs_proof e dp dpe rext) p1 p2);
                                  })))))))))
        (Xmlt.xml_or
          (Xmlt.xml_do "acRuleRemoval"
            (Xmlt.xml_take (redtriple xml2name Labelings.Sharp False)
              (\ a ->
                Xmlt.xml_take
                  (Xmlt.xml_do "trs"
                    (Xmlt.xml_take
                      (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                      (\ xa -> Xmlt.xml_return (id xa))))
                  (\ b ->
                    Xmlt.xml_take
                      (xml2ac_termination_proof xml2name termIndexMap ruleMap)
                      (\ c ->
                        Xmlt.xml_return
                          (Check_AC_Termination.AC_Rule_Removal a b c))))))
          (Xmlt.xml_do "acRIsEmpty"
            (Xmlt.xml_return Check_AC_Termination.AC_R_is_Empty))))
      (\ xa -> Xmlt.xml_return (id xa)))
    x;

xml2feasibility_proof ::
  forall a b.
    (Compare.Compare_order a, Shows_Literal.Showl a, Compare.Compare_order b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    (Xml.Xml,
                                      ([([Arith.Char], [Arith.Char])],
(Bool, ([String], [String])))) ->
                                      Strict_Sum.Sum_bot (Xmlt.Xml_error String)
(Check_Infeasibility.Feasibility_proof (Labelings.Lab a b) [Arith.Char]);
xml2feasibility_proof xml2name termIndexMap x =
  Xmlt.xml_do "feasibilityProof"
    (Xmlt.xml_take
      (Xmlt.xml_do "substitutionAndSteps"
        (Xmlt.xml_take (subst xml2name termIndexMap)
          (\ sigma ->
            Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
              (csteps xml2name termIndexMap)
              (\ prfs ->
                Xmlt.xml_return
                  (Check_Infeasibility.Feasible_Witness sigma prfs)))))
      (\ xa -> Xmlt.xml_return (id xa)))
    x;

xml2unknown_disproof ::
  forall a b.
    (Compare.Compare_order a, Shows_Literal.Showl a, Compare.Compare_order b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term (Labelings.Lab a b)
 [Arith.Char],
Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Check_Nontermination.Neg_unknown_proof a b [Arith.Char]);
xml2unknown_disproof xml2name termIndexMap ruleMap x =
  Xmlt.xml_do "unknownInputProof"
    (Xmlt.xml_take
      (Xmlt.xml_or
        (Xmlt.xml_do "unknownAssumption"
          (Xmlt.xml_take CPF_Input_Parser.unknown_inputa
            (\ xa ->
              Xmlt.xml_return (Check_Nontermination.Assume_NT_Unknown xa []))))
        (Xmlt.xml_do "unknownProof"
          (Xmlt.xml_take (Xmlt.xml_text "description")
            (\ _ ->
              Xmlt.xml_take CPF_Input_Parser.unknown_inputa
                (\ b ->
                  Xmlt.xml_take_many_sub [] Arith.zero_nat
                    Extended_Nat.Infinity_enat
                    (\ xa -> Strict_Sum.right (fst xa))
                    (\ _ ->
                      Xmlt.xml_return
                        (Check_Nontermination.Assume_NT_Unknown b [])))))))
      (\ xa -> Xmlt.xml_return (id xa)))
    x;

xml2eq_proof ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
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
                                       ([([Arith.Char], [Arith.Char])],
 (Bool, ([String], [String])))) ->
                                       Strict_Sum.Sum_bot
 (Xmlt.Xml_error String) (Equational_Reasoning.Eq_proof a [Arith.Char]);
xml2eq_proof xml2name termIndexMap ruleMap x =
  Xmlt.xml_or
    (Xmlt.xml_do "refl"
      (Xmlt.xml_take (CPF_Input_Parser.term xml2name termIndexMap)
        (\ xa -> Xmlt.xml_return (Equational_Reasoning.Refl xa))))
    (Xmlt.xml_or
      (Xmlt.xml_do "sym"
        (Xmlt.xml_take (xml2eq_proof xml2name termIndexMap ruleMap)
          (\ xa -> Xmlt.xml_return (Equational_Reasoning.Sym xa))))
      (Xmlt.xml_or
        (Xmlt.xml_do "trans"
          (Xmlt.xml_take (xml2eq_proof xml2name termIndexMap ruleMap)
            (\ a ->
              Xmlt.xml_take (xml2eq_proof xml2name termIndexMap ruleMap)
                (\ b -> Xmlt.xml_return (Equational_Reasoning.Trans a b)))))
        (Xmlt.xml_or
          (Xmlt.xml_do "assm"
            (Xmlt.xml_take (CPF_Input_Parser.rule xml2name termIndexMap ruleMap)
              (\ a ->
                Xmlt.xml_take (subst xml2name termIndexMap)
                  (\ b ->
                    Xmlt.xml_return
                      (Equational_Reasoning.Assm a
                        (Term_Rewriting.mk_subst Term_Rewriting.Var b))))))
          (Xmlt.xml_do "cong"
            (Xmlt.xml_take xml2name
              (\ a ->
                Xmlt.xml_take_many_sub [] Arith.zero_nat
                  Extended_Nat.Infinity_enat
                  (xml2eq_proof xml2name termIndexMap ruleMap)
                  (\ b -> Xmlt.xml_return (Equational_Reasoning.Cong a b))))))))
    x;

xml2equational_proof ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term (Labelings.Lab a b)
 [Arith.Char],
Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Check_Equational_Proof.Equational_proof a b [Arith.Char]);
xml2equational_proof xml2name termIndexMap ruleMap =
  Xmlt.xml_do "equationalProof"
    (Xmlt.xml_take
      (Xmlt.xml_or
        (Xmlt.xml_do "equationalProofTree"
          (Xmlt.xml_take (xml2eq_proof xml2name termIndexMap ruleMap)
            (\ x ->
              Xmlt.xml_return
                (Check_Equational_Proof.Equational_Proof_Tree x))))
        (Xmlt.xml_or
          (Xmlt.xml_change (conversion xml2name termIndexMap)
            (\ e -> Xmlt.xml_return (Check_Equational_Proof.Conversion e)))
          (Xmlt.xml_or
            (Xmlt.xml_change (subsumption_proof xml2name termIndexMap ruleMap)
              (Xmlt.xml_return .
                Check_Equational_Proof.Conversion_With_History))
            (Xmlt.xml_do "completionAndNormalization"
              (Xmlt.xml_take
                (Xmlt.xml_do "trs"
                  (Xmlt.xml_take
                    (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                    (\ x -> Xmlt.xml_return (id x))))
                (\ a ->
                  Xmlt.xml_take
                    (xml2completion_proof xml2name termIndexMap ruleMap)
                    (\ b ->
                      Xmlt.xml_return
                        (Check_Equational_Proof.Completion_and_Normalization a
                          b))))))))
      (\ x -> Xmlt.xml_return (id x)));

xml2complexity_input :: forall a. a;
xml2complexity_input = error "undefined";

rule_pairs ::
  forall a.
    (Shows_Literal.Showl a) => ((Xml.Xml,
                                  ([([Arith.Char], [Arith.Char])],
                                    (Bool, ([String], [String])))) ->
                                 Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                   a) ->
                                 Mapping.Mapping [Arith.Char]
                                   (Term_Rewriting.Term a [Arith.Char]) ->
                                   Mapping.Mapping [Arith.Char]
                                     (Term_Rewriting.Term a [Arith.Char],
                                       Term_Rewriting.Term a [Arith.Char]) ->
                                     String ->
                                       String ->
 (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
   Strict_Sum.Sum_bot (Xmlt.Xml_error String)
     [((Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char]),
        (Term_Rewriting.Term a [Arith.Char],
          Term_Rewriting.Term a [Arith.Char]))];
rule_pairs xml2name termIndexMap ruleMap s p =
  Xmlt.xml_do s
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (Xmlt.xml_do p
        (Xmlt.xml_take (CPF_Input_Parser.rule xml2name termIndexMap ruleMap)
          (\ a ->
            Xmlt.xml_take (CPF_Input_Parser.rule xml2name termIndexMap ruleMap)
              (\ b -> Xmlt.xml_return (a, b)))))
      Xmlt.xml_return);

xml2complexity_proof ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term (Labelings.Lab a b)
 [Arith.Char],
Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Check_Complexity.Complexity_proof a b [Arith.Char]);
xml2complexity_proof xml2name termIndexMap ruleMap x =
  Xmlt.xml_do "complexityProof"
    (Xmlt.xml_take
      (Xmlt.xml_or
        (Xmlt.xml_do "ruleShifting"
          (Xmlt.xml_take (redtriple xml2name Labelings.Sharp True)
            (\ rp ->
              Xmlt.xml_take
                (Xmlt.xml_do "trs"
                  (Xmlt.xml_take
                    (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                    (\ xa -> Xmlt.xml_return (id xa))))
                (\ del ->
                  Xmlt.xml_take_optional
                    (Xmlt.xml_do "usableRules"
                      (Xmlt.xml_take
                        (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                        (\ xa -> Xmlt.xml_return (id xa))))
                    (\ ur ->
                      Xmlt.xml_take
                        (xml2complexity_proof xml2name termIndexMap ruleMap)
                        (\ prf ->
                          Xmlt.xml_return
                            (Check_Complexity.Rule_Shift_Complexity rp del ur
                              prf)))))))
        (Xmlt.xml_or
          (Xmlt.xml_do "usableRules"
            (Xmlt.xml_take
              (Xmlt.xml_do "nonUsableRules"
                (Xmlt.xml_take
                  (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                  (\ xa -> Xmlt.xml_return (id xa))))
              (\ a ->
                Xmlt.xml_take
                  (xml2complexity_proof xml2name termIndexMap ruleMap)
                  (\ b ->
                    Xmlt.xml_return
                      (Check_Complexity.Usable_Rules_Complexity a b)))))
          (Xmlt.xml_or
            (Xmlt.xml_do "split"
              (Xmlt.xml_take
                (Xmlt.xml_do "trs"
                  (Xmlt.xml_take
                    (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                    (\ xa -> Xmlt.xml_return (id xa))))
                (\ a ->
                  Xmlt.xml_take
                    (xml2complexity_proof xml2name termIndexMap ruleMap)
                    (\ b ->
                      Xmlt.xml_take
                        (xml2complexity_proof xml2name termIndexMap ruleMap)
                        (\ c ->
                          Xmlt.xml_return
                            (Check_Complexity.Split_Complexity a b c))))))
            (Xmlt.xml_or
              (Xmlt.xml_do "removeNonApplicableRules"
                (Xmlt.xml_take
                  (Xmlt.xml_do "trs"
                    (Xmlt.xml_take
                      (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                      (\ xa -> Xmlt.xml_return (id xa))))
                  (\ a ->
                    Xmlt.xml_take
                      (xml2complexity_proof xml2name termIndexMap ruleMap)
                      (\ b ->
                        Xmlt.xml_return
                          (Check_Complexity.Remove_Nonapplicable_Rules_Complexity
                            a b)))))
              (Xmlt.xml_or
                (Xmlt.xml_change (bounds_info xml2name)
                  (Xmlt.xml_return . Check_Complexity.Matchbounds_Complexity))
                (Xmlt.xml_or
                  (Xmlt.xml_do "relativeBounds"
                    (Xmlt.xml_take (bounds_info xml2name)
                      (\ a ->
                        Xmlt.xml_take
                          (Xmlt.xml_do "trs"
                            (Xmlt.xml_take
                              (CPF_Input_Parser.rules xml2name termIndexMap
                                ruleMap)
                              (\ xa -> Xmlt.xml_return (id xa))))
                          (\ b ->
                            Xmlt.xml_take
                              (xml2complexity_proof xml2name termIndexMap
                                ruleMap)
                              (\ c ->
                                Xmlt.xml_return
                                  (Check_Complexity.Matchbounds_Rel_Complexity a
                                    b c))))))
                  (Xmlt.xml_or
                    (Xmlt.xml_do "rIsEmpty"
                      (Xmlt.xml_return Check_Complexity.RisEmpty_Complexity))
                    (Xmlt.xml_or
                      (Xmlt.xml_do "dtTransformation"
                        (Xmlt.xml_take
                          (rule_pairs xml2name termIndexMap ruleMap "strictDTs"
                            "ruleWithDT")
                          (\ s ->
                            Xmlt.xml_take
                              (rule_pairs xml2name termIndexMap ruleMap
                                "weakDTs" "ruleWithDT")
                              (\ w ->
                                Xmlt.xml_take
                                  (CPF_Input_Parser.innermostLhss xml2name
                                    termIndexMap)
                                  (\ inn ->
                                    Xmlt.xml_take
                                      (xml2complexity_proof xml2name
termIndexMap ruleMap)
                                      (\ p ->
Xmlt.xml_return
  (Check_Complexity.DT_Transformation
    (DT_Transformation_Impl.DT_Transformation_Info s w inn) p)))))))
                      (Xmlt.xml_or
                        (Xmlt.xml_do "wdpTransformation"
                          (Xmlt.xml_take
                            (CPF_Input_Parser.symbols xml2name
                              "compoundSymbols")
                            (\ comp ->
                              Xmlt.xml_take
                                (rule_pairs xml2name termIndexMap ruleMap
                                  "strictWDPs" "ruleWithWDP")
                                (\ s ->
                                  Xmlt.xml_take
                                    (rule_pairs xml2name termIndexMap ruleMap
                                      "weakWDPs" "ruleWithWDP")
                                    (\ w ->
                                      Xmlt.xml_take
(CPF_Input_Parser.innermostLhss xml2name termIndexMap)
(\ q ->
  Xmlt.xml_take (xml2complexity_proof xml2name termIndexMap ruleMap)
    (\ p ->
      Xmlt.xml_return
        (Check_Complexity.WDP_Transformation
          (WDP_Transformation_Impl.WDP_Trans_Info (Arith.set comp) s w q)
          p))))))))
                        (Xmlt.xml_or
                          (Xmlt.xml_do "unknownProof"
                            (Xmlt.xml_take (Xmlt.xml_text "description")
                              (\ _ ->
                                Xmlt.xml_take (xml2complexity_input xml2name)
                                  (\ b ->
                                    Xmlt.xml_take_many_sub [] Arith.zero_nat
                                      Extended_Nat.Infinity_enat
                                      (Xmlt.xml_do "subProof"
(Xmlt.xml_take (xml2complexity_input xml2name)
  (\ inp ->
    Xmlt.xml_take (xml2complexity_proof xml2name termIndexMap ruleMap)
      (\ prf ->
        Xmlt.xml_return
          (Check_Termination_Common.Complexity_assm_proof inp prf)))))
                                      (\ c ->
Xmlt.xml_return (Check_Complexity.Complexity_Assumption b c))))))
                          (Xmlt.xml_do "complexityAssumption"
                            (Xmlt.xml_take (xml2complexity_input xml2name)
                              (\ p ->
                                Xmlt.xml_return
                                  (Check_Complexity.Complexity_Assumption p
                                    []))))))))))))))
      (\ xa -> Xmlt.xml_return (id xa)))
    x;

xml2unknown_proof ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term (Labelings.Lab a b)
 [Arith.Char],
Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Check_Termination.Unknown_proof a b [Arith.Char]);
xml2unknown_proof xml2name termIndexMap ruleMap x =
  Xmlt.xml_do "unknownInputProof"
    (Xmlt.xml_take
      (Xmlt.xml_or
        (Xmlt.xml_do "unknownAssumption"
          (Xmlt.xml_take CPF_Input_Parser.unknown_inputa
            (\ u -> Xmlt.xml_return (Check_Termination.Assume_Unknown u []))))
        (Xmlt.xml_do "unknownProof"
          (Xmlt.xml_take (Xmlt.xml_text "description")
            (\ _ ->
              Xmlt.xml_take CPF_Input_Parser.unknown_inputa
                (\ b ->
                  Xmlt.xml_take_many_sub [] Arith.zero_nat
                    Extended_Nat.Infinity_enat
                    (xml2subproof xml2name termIndexMap ruleMap)
                    (\ c ->
                      Xmlt.xml_return
                        (Check_Termination.Assume_Unknown b c)))))))
      Xmlt.xml_return)
    x;

xml2ncomm_proof ::
  ((Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
      (Labelings.Lab [Arith.Char] [Arith.Nat])) ->
    Mapping.Mapping [Arith.Char]
      (Term_Rewriting.Term (Labelings.Lab [Arith.Char] [Arith.Nat])
        [Arith.Char]) ->
      Mapping.Mapping [Arith.Char]
        (Term_Rewriting.Term (Labelings.Lab [Arith.Char] [Arith.Nat])
           [Arith.Char],
          Term_Rewriting.Term (Labelings.Lab [Arith.Char] [Arith.Nat])
            [Arith.Char]) ->
        (Xml.Xml,
          ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
          Strict_Sum.Sum_bot (Xmlt.Xml_error String)
            (Check_CRP.Ncomm_proof [Arith.Char] [Arith.Nat] [Arith.Char]
              [Arith.Char]);
xml2ncomm_proof xml2name termIndexMap ruleMap x =
  let {
    rew = rsteps xml2name termIndexMap ruleMap;
  } in Xmlt.xml_do "comDisproof"
         (Xmlt.xml_take
           (Xmlt.xml_or
             (Xmlt.xml_do "nonJoinableFork"
               (Xmlt.xml_take rew
                 (\ a ->
                   Xmlt.xml_take rew
                     (\ b ->
                       Xmlt.xml_take
                         (xml2non_join_info xml2name termIndexMap ruleMap)
                         (\ c ->
                           Xmlt.xml_return
                             ((case a of {
                                (s, seq1) ->
                                  (\ (_, aa) ->
                                    Check_CRP.Non_Join_Comm s seq1 aa);
                              })
                                b
                               c))))))
             (Xmlt.xml_do "swapTRSs"
               (Xmlt.xml_take (xml2ncomm_proof xml2name termIndexMap ruleMap)
                 (\ xa -> Xmlt.xml_return (Check_CRP.Swap_Not_Comm xa)))))
           (\ xa -> Xmlt.xml_return (id xa)))
         x;

xml2comm_proof ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => ((Xml.Xml,
                                   ([([Arith.Char], [Arith.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Labelings.Lab a b)) ->
                                  Mapping.Mapping [Arith.Char]
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char]) ->
                                    Mapping.Mapping [Arith.Char]
                                      (Term_Rewriting.Term (Labelings.Lab a b)
 [Arith.Char],
Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char]) ->
                                      (Xml.Xml,
([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
Strict_Sum.Sum_bot (Xmlt.Xml_error String)
  (Check_CRP.Comm_proof a b [Arith.Char]);
xml2comm_proof xml2name termIndexMap ruleMap x =
  Xmlt.xml_do "comProof"
    (Xmlt.xml_take
      (Xmlt.xml_or
        (Xmlt.xml_do "parallelClosed"
          (Xmlt.xml_take joinAutoBfs
            (\ n -> Xmlt.xml_return (Check_CRP.Parallel_Closed_Comm n))))
        (Xmlt.xml_or
          (Xmlt.xml_do "developmentClosed"
            (Xmlt.xml_take joinAutoBfs
              (\ n -> Xmlt.xml_return (Check_CRP.Development_Closed_Comm n))))
          (Xmlt.xml_or
            (Xmlt.xml_do "pcpClosed"
              (Xmlt.xml_take
                (Xmlt.xml_do "ordinaryCriticalPairs"
                  (Xmlt.xml_take (xml2cp_join_info xml2name termIndexMap)
                    (\ xa -> Xmlt.xml_return (id xa))))
                (\ hints_cp ->
                  Xmlt.xml_take
                    (Xmlt.xml_do "parallelCriticalPairs"
                      (Xmlt.xml_take (xml2cp_join_info xml2name termIndexMap)
                        (\ xa -> Xmlt.xml_return (id xa))))
                    (\ hints_pcp ->
                      Xmlt.xml_return
                        (Check_CRP.PCP_Closed_Comm hints_cp hints_pcp)))))
            (Xmlt.xml_or
              (Xmlt.xml_do "pcpRuleLabeling"
                (Xmlt.xml_take
                  (rule_labeling_function xml2name termIndexMap ruleMap)
                  (\ lab ->
                    Xmlt.xml_take_optional
                      (rule_labeling_function xml2name termIndexMap ruleMap)
                      (\ laba ->
                        Xmlt.xml_take
                          (Xmlt.xml_do "joinsRS"
                            (Xmlt.xml_take
                              (xml2cp_join_info xml2name termIndexMap)
                              (\ xa -> Xmlt.xml_return (id xa))))
                          (\ joinsRS ->
                            Xmlt.xml_take
                              (Xmlt.xml_do "joinsSR"
                                (Xmlt.xml_take
                                  (xml2cp_join_info xml2name termIndexMap)
                                  (\ xa -> Xmlt.xml_return (id xa))))
                              (\ joinsSR ->
                                Xmlt.xml_return
                                  (Check_CRP.PCP_Rule_Lab_Comm
                                    (Parallel_Critical_Pairs_Impl.PCP_Sequences_Com
                                      (Rule_Labeling_Impl.rule_lab_repr_to_lab
lab)
                                      (Arith.map_option
Rule_Labeling_Impl.rule_lab_repr_to_lab laba)
                                      joinsRS joinsSR))))))))
              (Xmlt.xml_or
                (Xmlt.xml_do "compositionalPcpRuleLabeling"
                  (Xmlt.xml_take
                    (rule_labeling_function xml2name termIndexMap ruleMap)
                    (\ lab ->
                      Xmlt.xml_take_optional
                        (rule_labeling_function xml2name termIndexMap ruleMap)
                        (\ laba ->
                          Xmlt.xml_take
                            (Xmlt.xml_do "joinsRS"
                              (Xmlt.xml_take
                                (xml2cp_join_info xml2name termIndexMap)
                                (\ xa -> Xmlt.xml_return (id xa))))
                            (\ joinsRS ->
                              Xmlt.xml_take
                                (Xmlt.xml_do "joinsSR"
                                  (Xmlt.xml_take
                                    (xml2cp_join_info xml2name termIndexMap)
                                    (\ xa -> Xmlt.xml_return (id xa))))
                                (\ joinsSR ->
                                  Xmlt.xml_take
                                    (Xmlt.xml_do "trs"
                                      (Xmlt.xml_take
(CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
(\ xa -> Xmlt.xml_return (id xa))))
                                    (\ c ->
                                      Xmlt.xml_take
(Xmlt.xml_do "trs"
  (Xmlt.xml_take (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
    (\ xa -> Xmlt.xml_return (id xa))))
(\ d ->
  Xmlt.xml_take (xml2comm_proof xml2name termIndexMap ruleMap)
    (\ subPrf ->
      Xmlt.xml_return
        (Check_CRP.PCP_Compositional_Rule_Lab_Comm c d
          (Parallel_Critical_Pairs_Impl.PCP_Sequences_Com
            (Rule_Labeling_Impl.rule_lab_repr_to_lab lab)
            (Arith.map_option Rule_Labeling_Impl.rule_lab_repr_to_lab laba)
            joinsRS joinsSR)
          subPrf))))))))))
                (Xmlt.xml_or
                  (Xmlt.xml_do "compositionalPcps"
                    (Xmlt.xml_take
                      (Xmlt.xml_do "trsC"
                        (Xmlt.xml_take
                          (CPF_Input_Parser.rules xml2name termIndexMap ruleMap)
                          (\ xa -> Xmlt.xml_return (id xa))))
                      (\ trsC ->
                        Xmlt.xml_take
                          (Xmlt.xml_do "trsD"
                            (Xmlt.xml_take
                              (CPF_Input_Parser.rules xml2name termIndexMap
                                ruleMap)
                              (\ xa -> Xmlt.xml_return (id xa))))
                          (\ trsD ->
                            Xmlt.xml_take
                              (Xmlt.xml_do "trsP"
                                (Xmlt.xml_take
                                  (CPF_Input_Parser.rules xml2name termIndexMap
                                    ruleMap)
                                  (\ xa -> Xmlt.xml_return (id xa))))
                              (\ trsP ->
                                Xmlt.xml_take
                                  (xml2cp_join_info xml2name termIndexMap)
                                  (\ hintsP_RS ->
                                    Xmlt.xml_take
                                      (xml2cp_join_info xml2name termIndexMap)
                                      (\ hintsP_SR ->
Xmlt.xml_take (xml2cp_join_info xml2name termIndexMap)
  (\ hintsRS ->
    Xmlt.xml_take (xml2cp_join_info xml2name termIndexMap)
      (\ hintsSR ->
        Xmlt.xml_take (xml2trs_termination_proof xml2name termIndexMap ruleMap)
          (\ sn_prf ->
            Xmlt.xml_take (xml2comm_proof xml2name termIndexMap ruleMap)
              (\ com_prf ->
                Xmlt.xml_return
                  (Check_CRP.Compositional_PCPS_Comm trsC trsD trsP hintsP_RS
                    hintsP_SR hintsRS hintsSR sn_prf com_prf))))))))))))
                  (Xmlt.xml_or
                    (Xmlt.xml_do "swapTRSs"
                      (Xmlt.xml_take
                        (xml2comm_proof xml2name termIndexMap ruleMap)
                        (\ xa -> Xmlt.xml_return (Check_CRP.Swap_Comm xa))))
                    (Xmlt.xml_do "switchToCrProof"
                      (Xmlt.xml_take
                        (xml2cr_proof xml2name termIndexMap ruleMap)
                        (\ xa ->
                          Xmlt.xml_return (Check_CRP.CR_Proof xa)))))))))))
      (\ xa -> Xmlt.xml_return (id xa)))
    x;

proof ::
  ((Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
      (Labelings.Lab [Arith.Char] [Arith.Nat])) ->
    Mapping.Mapping [Arith.Char]
      (Term_Rewriting.Term (Labelings.Lab [Arith.Char] [Arith.Nat])
        [Arith.Char]) ->
      Mapping.Mapping [Arith.Char]
        (Term_Rewriting.Term (Labelings.Lab [Arith.Char] [Arith.Nat])
           [Arith.Char],
          Term_Rewriting.Term (Labelings.Lab [Arith.Char] [Arith.Nat])
            [Arith.Char]) ->
        (Xml.Xml,
          ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
          Strict_Sum.Sum_bot (Xmlt.Xml_error String)
            (Proof_Checker.Proof [Arith.Char] [Arith.Nat] [Arith.Char]);
proof xml2name termIndexMap ruleMap =
  Xmlt.xml_do "proof"
    (Xmlt.xml_take
      (Xmlt.xml_or
        (Xmlt.xml_change
          (xml2trs_termination_proof xml2name termIndexMap ruleMap)
          (Xmlt.xml_return . Proof_Checker.TRS_Termination_Proof))
        (Xmlt.xml_or
          (Xmlt.xml_change
            (xml2trs_nontermination_proof xml2name termIndexMap ruleMap)
            (Xmlt.xml_return . Proof_Checker.TRS_Nontermination_Proof))
          (Xmlt.xml_or
            (Xmlt.xml_change
              (xml2reltrs_nontermination_proof xml2name termIndexMap ruleMap)
              (Xmlt.xml_return .
                Proof_Checker.Relative_TRS_Nontermination_Proof))
            (Xmlt.xml_or
              (Xmlt.xml_change (xml2cr_proof xml2name termIndexMap ruleMap)
                (Xmlt.xml_return . Proof_Checker.TRS_Confluence_Proof))
              (Xmlt.xml_or
                (Xmlt.xml_change (xml2ncr_proof xml2name termIndexMap ruleMap)
                  (Xmlt.xml_return . Proof_Checker.TRS_Non_Confluence_Proof))
                (Xmlt.xml_or
                  (Xmlt.xml_change
                    (xml2dp_termination_proof xml2name termIndexMap ruleMap)
                    (Xmlt.xml_return . Proof_Checker.DP_Termination_Proof))
                  (Xmlt.xml_or
                    (Xmlt.xml_change
                      (xml2dp_nontermination_proof xml2name termIndexMap
                        ruleMap)
                      (Xmlt.xml_return . Proof_Checker.DP_Nontermination_Proof))
                    (Xmlt.xml_or
                      (Xmlt.xml_change
                        (xml2completion_proof xml2name termIndexMap ruleMap)
                        (Xmlt.xml_return . Proof_Checker.Completion_Proof))
                      (Xmlt.xml_or
                        (Xmlt.xml_change
                          (xml2ordered_completion_proof xml2name termIndexMap)
                          (Xmlt.xml_return .
                            Proof_Checker.Ordered_Completion_Proof))
                        (Xmlt.xml_or
                          (Xmlt.xml_change
                            (xml2equational_proof xml2name termIndexMap ruleMap)
                            (Xmlt.xml_return . Proof_Checker.Equational_Proof))
                          (Xmlt.xml_or
                            (Xmlt.xml_change
                              (xml2equational_disproof xml2name termIndexMap
                                ruleMap)
                              (Xmlt.xml_return .
                                Proof_Checker.Equational_Disproof))
                            (Xmlt.xml_or
                              (Xmlt.xml_change
                                (xml2complexity_proof xml2name termIndexMap
                                  ruleMap)
                                (Xmlt.xml_return .
                                  Proof_Checker.Complexity_Proof))
                              (Xmlt.xml_or
                                (Xmlt.xml_change
                                  (xml2quasi_reductive_proof xml2name
                                    termIndexMap ruleMap)
                                  (Xmlt.xml_return .
                                    Proof_Checker.Quasi_Reductive_Proof))
                                (Xmlt.xml_or
                                  (Xmlt.xml_change
                                    (xml2conditional_cr_proof xml2name
                                      termIndexMap ruleMap)
                                    (Xmlt.xml_return .
                                      Proof_Checker.Conditional_CR_Proof))
                                  (Xmlt.xml_or
                                    (Xmlt.xml_change
                                      (xml2conditional_ncr_proof xml2name
termIndexMap ruleMap)
                                      (Xmlt.xml_return .
Proof_Checker.Conditional_Non_CR_Proof))
                                    (Xmlt.xml_or
                                      (Xmlt.xml_change
(xml2ncomm_proof xml2name termIndexMap ruleMap)
(Xmlt.xml_return . Proof_Checker.TRS_Non_Commutation_Proof))
                                      (Xmlt.xml_or
(Xmlt.xml_change (xml2comm_proof xml2name termIndexMap ruleMap)
  (Xmlt.xml_return . Proof_Checker.TRS_Commutation_Proof))
(Xmlt.xml_or
  (Xmlt.xml_do "treeAutomatonClosedProof"
    (Xmlt.xml_take closed_criterion
      (\ x -> Xmlt.xml_return (Proof_Checker.Tree_Automata_Closed_Proof x))))
  (Xmlt.xml_or
    (Xmlt.xml_change (xml2ac_termination_proof xml2name termIndexMap ruleMap)
      (Xmlt.xml_return . Proof_Checker.AC_Termination_Proof))
    (Xmlt.xml_or
      (Xmlt.xml_do "ltsTerminationProof"
        (Xmlt.xml_take LTS_Parser.lts_termination_proof_parser
          (\ x -> Xmlt.xml_return (Proof_Checker.LTS_Termination_Proof x))))
      (Xmlt.xml_or
        (Xmlt.xml_do "ltsSafetyProof"
          (Xmlt.xml_take LTS_Parser.lts_safety_proof_parser
            (\ x -> Xmlt.xml_return (Proof_Checker.LTS_Safety_Proof x))))
        (Xmlt.xml_or
          (Xmlt.xml_change
            (xml2infeasibility_proof xml2name termIndexMap ruleMap)
            (Xmlt.xml_return . Proof_Checker.Infeasibility_Proof))
          (Xmlt.xml_or
            (Xmlt.xml_change (xml2feasibility_proof xml2name termIndexMap)
              (Xmlt.xml_return . Proof_Checker.Feasibility_Proof))
            (Xmlt.xml_or
              (Xmlt.xml_change (xml2unknown_proof xml2name termIndexMap ruleMap)
                (Xmlt.xml_return . Proof_Checker.Unknown_Proof))
              (Xmlt.xml_change
                (xml2unknown_disproof xml2name termIndexMap ruleMap)
                (Xmlt.xml_return .
                  Proof_Checker.Unknown_Disproof))))))))))))))))))))))))))
      Xmlt.xml_return);

symbol_parser ::
  (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
      (Labelings.Lab [Arith.Char] [Arith.Nat]);
symbol_parser x =
  Xmlt.xml_or
    (Xmlt.xml_change (Xmlt.xml_text "name") (Xmlt.xml_return . Labelings.UnLab))
    (Xmlt.xml_or
      (Xmlt.xml_do "sharp"
        (Xmlt.xml_take symbol_parser
          (\ xa -> Xmlt.xml_return (Labelings.Sharp xa))))
      (Xmlt.xml_do "labeledSymbol"
        (Xmlt.xml_take symbol_parser
          (\ a ->
            Xmlt.xml_take
              (Xmlt.xml_or
                (Xmlt.xml_do "numberLabel"
                  (Xmlt.xml_take_many_sub [] Arith.zero_nat
                    Extended_Nat.Infinity_enat (Xmlt.xml_nat "number")
                    (\ aa -> Xmlt.xml_return (Sum_Type.Inl aa))))
                (Xmlt.xml_do "symbolLabel"
                  (Xmlt.xml_take_many_sub [] Arith.zero_nat
                    Extended_Nat.Infinity_enat symbol_parser
                    (\ aa -> Xmlt.xml_return (Sum_Type.Inr aa)))))
              (\ b ->
                Xmlt.xml_return (case b of {
                                  Sum_Type.Inl ba -> Labelings.Lab a ba;
                                  Sum_Type.Inr ba -> Labelings.FunLab a ba;
                                }))))))
    x;

input_parser ::
  Mapping.Mapping [Arith.Char]
    (Term_Rewriting.Term (Labelings.Lab [Arith.Char] [Arith.Nat])
      [Arith.Char]) ->
    Mapping.Mapping [Arith.Char]
      (Term_Rewriting.Term (Labelings.Lab [Arith.Char] [Arith.Nat])
         [Arith.Char],
        Term_Rewriting.Term (Labelings.Lab [Arith.Char] [Arith.Nat])
          [Arith.Char]) ->
      (Xml.Xml,
        ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xmlt.Xml_error String)
          (Ceta_Problem_Spec.Input (Labelings.Lab [Arith.Char] [Arith.Nat])
            [Arith.Char]);
input_parser = CPF_Input_Parser.input symbol_parser;

proof_parser ::
  Mapping.Mapping [Arith.Char]
    (Term_Rewriting.Term (Labelings.Lab [Arith.Char] [Arith.Nat])
      [Arith.Char]) ->
    Mapping.Mapping [Arith.Char]
      (Term_Rewriting.Term (Labelings.Lab [Arith.Char] [Arith.Nat])
         [Arith.Char],
        Term_Rewriting.Term (Labelings.Lab [Arith.Char] [Arith.Nat])
          [Arith.Char]) ->
      (Xml.Xml,
        ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xmlt.Xml_error String)
          (Proof_Checker.Proof [Arith.Char] [Arith.Nat] [Arith.Char]);
proof_parser = proof symbol_parser;

answer_parser ::
  Mapping.Mapping [Arith.Char]
    (Term_Rewriting.Term (Labelings.Lab [Arith.Char] [Arith.Nat])
      [Arith.Char]) ->
    Mapping.Mapping [Arith.Char]
      (Term_Rewriting.Term (Labelings.Lab [Arith.Char] [Arith.Nat])
         [Arith.Char],
        Term_Rewriting.Term (Labelings.Lab [Arith.Char] [Arith.Nat])
          [Arith.Char]) ->
      (Xml.Xml,
        ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xmlt.Xml_error String)
          (Ceta_Problem_Spec.Answer (Labelings.Lab [Arith.Char] [Arith.Nat])
            [Arith.Char]);
answer_parser = CPF_Input_Parser.answer symbol_parser;

property_parser ::
  (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
      (Ceta_Problem_Spec.Property (Labelings.Lab [Arith.Char] [Arith.Nat])
        [Arith.Char]);
property_parser = CPF_Input_Parser.property symbol_parser;

}
