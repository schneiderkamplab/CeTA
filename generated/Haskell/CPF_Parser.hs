{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module CPF_Parser(parse_combined_cert_problem) where {

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
import qualified CPF_Input_Parser;
import qualified Proof_Checker;
import qualified FOR_Preliminaries;
import qualified CPF_Proof_Parser;
import qualified Ceta_Problem_Spec;
import qualified Phantom_Type;
import qualified Strict_Sum;
import qualified Mapping;
import qualified Xmlt;
import qualified Labelings;
import qualified Term_Rewriting;
import qualified Xml;
import qualified Arith;

parse_from_string ::
  forall a.
    ((Xml.Xml,
       ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
      Strict_Sum.Sum_bot (Xmlt.Xml_error String) a) ->
      [Arith.Char] -> Strict_Sum.Sum_bot String a;
parse_from_string xml_parser s =
  Strict_Sum.catch_error
    (Xmlt.parse_xml_string
      (FOR_Preliminaries.debug (Term_Rewriting.showsl_literal "0") "parsing xml"
        xml_parser)
      s)
    (\ e -> Strict_Sum.errora (Arith.implode e));

parse_input ::
  [Arith.Char] ->
    Strict_Sum.Sum_bot String
      (Ceta_Problem_Spec.Input (Labelings.Lab [Arith.Char] [Arith.Nat])
        [Arith.Char]);
parse_input inp =
  Strict_Sum.catch_error
    (parse_from_string
      (CPF_Proof_Parser.input_parser
        (Mapping.mapping_empty
          (Phantom_Type.of_phantom Mapping.mapping_impl_list))
        (Mapping.mapping_empty
          (Phantom_Type.of_phantom Mapping.mapping_impl_list)))
      inp)
    (\ e ->
      Strict_Sum.errora
        ("parse-input error: CeTA expects a CPF-\'input\' element\n\n" ++ e));

parse_merge ::
  forall a b.
    String ->
      (a -> Strict_Sum.Sum_bot String b) ->
        Maybe a -> Maybe b -> Strict_Sum.Sum_bot String b;
parse_merge e p op_maj op_min =
  (case op_maj of {
    Nothing ->
      (case op_min of {
        Nothing -> Strict_Sum.errora (("no " ++ e) ++ " has been provided");
        Just a -> Strict_Sum.returna a;
      });
    Just a -> p a;
  });

parse_answer ::
  [Arith.Char] ->
    Strict_Sum.Sum_bot String
      (Ceta_Problem_Spec.Answer (Labelings.Lab [Arith.Char] [Arith.Nat])
        [Arith.Char]);
parse_answer inp =
  Strict_Sum.catch_error
    (parse_from_string
      (CPF_Proof_Parser.answer_parser
        (Mapping.mapping_empty
          (Phantom_Type.of_phantom Mapping.mapping_impl_list))
        (Mapping.mapping_empty
          (Phantom_Type.of_phantom Mapping.mapping_impl_list)))
      inp)
    (\ e ->
      Strict_Sum.errora
        ("parse-answer error: CeTA accepts YES, NO, WORST_CASE(?,O(n^k)) for some number k, or a CPF-\'answer\' element\n\n" ++
          e));

parse_property ::
  [Arith.Char] ->
    Strict_Sum.Sum_bot String
      (Ceta_Problem_Spec.Property (Labelings.Lab [Arith.Char] [Arith.Nat])
        [Arith.Char]);
parse_property inp =
  Strict_Sum.catch_error
    (parse_from_string CPF_Proof_Parser.property_parser inp)
    (\ e ->
      Strict_Sum.errora
        ("parse-property error: CeTA accepts SN, DC, RC, CR, INF, COM or a CPF-\'property\' element\n\n" ++
          e));

certification_problem_parser ::
  (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
      (Maybe (Ceta_Problem_Spec.Input (Labelings.Lab [Arith.Char] [Arith.Nat])
               [Arith.Char]),
        (Maybe (Ceta_Problem_Spec.Property
                 (Labelings.Lab [Arith.Char] [Arith.Nat]) [Arith.Char]),
          (Maybe (Ceta_Problem_Spec.Answer
                   (Labelings.Lab [Arith.Char] [Arith.Nat]) [Arith.Char]),
            Proof_Checker.Proof [Arith.Char] [Arith.Nat] [Arith.Char])));
certification_problem_parser =
  Xmlt.xml_do "certificationProblem"
    (Xmlt.xml_take (Xmlt.xml_text "cpfVersion")
      (\ _ ->
        Xmlt.xml_take
          (CPF_Input_Parser.lookupTables CPF_Proof_Parser.symbol_parser)
          (\ (termIndexMap, ruleMap) ->
            Xmlt.xml_take_optional
              (CPF_Proof_Parser.input_parser termIndexMap ruleMap)
              (\ inp ->
                Xmlt.xml_take_optional CPF_Proof_Parser.property_parser
                  (\ prop ->
                    Xmlt.xml_take_optional
                      (CPF_Proof_Parser.answer_parser termIndexMap ruleMap)
                      (\ ans ->
                        Xmlt.xml_take
                          (CPF_Proof_Parser.proof_parser termIndexMap ruleMap)
                          (\ proof ->
                            Xmlt.xml_take_optional
                              (\ x -> Strict_Sum.right (fst x))
                              (\ _ ->
                                Xmlt.xml_return
                                  (inp, (prop, (ans, proof)))))))))));

parse_cert_problem ::
  [Arith.Char] ->
    Strict_Sum.Sum_bot String
      (Maybe (Ceta_Problem_Spec.Input (Labelings.Lab [Arith.Char] [Arith.Nat])
               [Arith.Char]),
        (Maybe (Ceta_Problem_Spec.Property
                 (Labelings.Lab [Arith.Char] [Arith.Nat]) [Arith.Char]),
          (Maybe (Ceta_Problem_Spec.Answer
                   (Labelings.Lab [Arith.Char] [Arith.Nat]) [Arith.Char]),
            Proof_Checker.Proof [Arith.Char] [Arith.Nat] [Arith.Char])));
parse_cert_problem = parse_from_string certification_problem_parser;

parse_combined_cert_problem ::
  Maybe [Arith.Char] ->
    Maybe [Arith.Char] ->
      Maybe [Arith.Char] ->
        [Arith.Char] ->
          Strict_Sum.Sum_bot String
            (Ceta_Problem_Spec.Input (Labelings.Lab [Arith.Char] [Arith.Nat])
               [Arith.Char],
              (Ceta_Problem_Spec.Property
                 (Labelings.Lab [Arith.Char] [Arith.Nat]) [Arith.Char],
                (Ceta_Problem_Spec.Answer
                   (Labelings.Lab [Arith.Char] [Arith.Nat]) [Arith.Char],
                  Proof_Checker.Proof [Arith.Char] [Arith.Nat] [Arith.Char])));
parse_combined_cert_problem inp1 prop1 answ1 prfs =
  Strict_Sum.bind (parse_cert_problem prfs)
    (\ (inp2, (prop2, (answ2, prf))) ->
      Strict_Sum.bind (parse_merge "input" parse_input inp1 inp2)
        (\ inp ->
          Strict_Sum.bind (parse_merge "property" parse_property prop1 prop2)
            (\ prop ->
              Strict_Sum.bind (parse_merge "answer" parse_answer answ1 answ2)
                (\ answ -> Strict_Sum.returna (inp, (prop, (answ, prf)))))));

}
