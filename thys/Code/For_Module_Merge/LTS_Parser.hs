{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  LTS_Parser(lts_input_parser, lts_safety_input_parser, lts_safety_proof_parser,
              lts_termination_proof_parser)
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
import qualified Product_Type;
import qualified Map_Of;
import qualified Fresh_Variable_Addition;
import qualified Transition_Removal;
import qualified Location_Addition;
import qualified LTS_Termination_Prover;
import qualified Mapping_Impl;
import qualified Collection_Order;
import qualified Container_Setup;
import qualified Invariant_Proof_Checkers;
import qualified LTS_Safety_Prover;
import qualified Cooperation_Program;
import qualified List;
import qualified LTS;
import qualified Integer_Arithmetic;
import qualified Invariant_Checker;
import qualified Extended_Nat;
import qualified Formula;
import qualified Term;
import qualified Arith;
import qualified HOL;
import qualified Strict_Sum;
import qualified Xmlt;
import qualified Str;
import qualified Xml;

trans_id ::
  forall a.
    (String ->
      (Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xmlt.Xml_error String) a) ->
      (Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xmlt.Xml_error String) a;
trans_id trans_id_parser = trans_id_parser "transitionId";

formula_parser ::
  forall a b c.
    ((Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
      Strict_Sum.Sum_bot (Xmlt.Xml_error String)
        (Formula.Formula (Term.Term a (b, c)))) ->
      (Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xmlt.Xml_error String)
          (Formula.Formula (Term.Term a (b, c)));
formula_parser atom_parser x =
  Xmlt.xml_or
    (Xmlt.xml_do "disjunction"
      (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
        (formula_parser atom_parser)
        (\ fs -> Xmlt.xml_return (Formula.Disjunction fs))))
    (Xmlt.xml_or
      (Xmlt.xml_do "conjunction"
        (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
          (formula_parser atom_parser)
          (\ fs -> Xmlt.xml_return (Formula.Conjunction fs))))
      atom_parser)
    x;

hints_parser ::
  forall a.
    (HOL.Default a) => (Xml.Xml,
                         ([([Str.Char], [Str.Char])],
                           (Bool, ([String], [String])))) ->
                         Strict_Sum.Sum_bot (Xmlt.Xml_error String) a;
hints_parser xml = Xmlt.xml_do "auto" (Xmlt.xml_return HOL.defaulta) xml;

art_node_parser ::
  forall a b c d e f g.
    (HOL.Default g) => (String ->
                         (Xml.Xml,
                           ([([Str.Char], [Str.Char])],
                             (Bool, ([String], [String])))) ->
                           Strict_Sum.Sum_bot (Xmlt.Xml_error String) a) ->
                         ((Xml.Xml,
                            ([([Str.Char], [Str.Char])],
                              (Bool, ([String], [String])))) ->
                           Strict_Sum.Sum_bot (Xmlt.Xml_error String) b) ->
                           ((Xml.Xml,
                              ([([Str.Char], [Str.Char])],
                                (Bool, ([String], [String])))) ->
                             Strict_Sum.Sum_bot (Xmlt.Xml_error String) c) ->
                             ((Xml.Xml,
                                ([([Str.Char], [Str.Char])],
                                  (Bool, ([String], [String])))) ->
                               Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                 (Formula.Formula (Term.Term d (e, f)))) ->
                               (Xml.Xml,
                                 ([([Str.Char], [Str.Char])],
                                   (Bool, ([String], [String])))) ->
                                 Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                   (Invariant_Checker.Art_node_impl d e f b a c
                                      g,
                                     [a]);
art_node_parser art_node_id_parser location_parser trans_parser atom_parser =
  Xmlt.xml_do "node"
    (Xmlt.xml_take_default False (Xmlt.xml_do "initial" (Xmlt.xml_return True))
      (\ init ->
        Xmlt.xml_take (art_node_id_parser "nodeId")
          (\ nodeId ->
            Xmlt.xml_take
              (Xmlt.xml_do "invariant"
                (Xmlt.xml_take (formula_parser atom_parser) Xmlt.xml_return))
              (\ invariant ->
                Xmlt.xml_take
                  (Xmlt.xml_do "location"
                    (Xmlt.xml_take location_parser Xmlt.xml_return))
                  (\ location ->
                    Xmlt.xml_take
                      (Xmlt.xml_or
                        (Xmlt.xml_do "children"
                          (Xmlt.xml_take_many_sub [] Arith.zero_nat
                            Extended_Nat.Infinity_enat
                            (Xmlt.xml_do "child"
                              (Xmlt.xml_take trans_parser
                                (\ tr ->
                                  Xmlt.xml_take (art_node_id_parser "nodeId")
                                    (\ n ->
                                      Xmlt.xml_take_default HOL.defaulta
(Xmlt.xml_do "hints" (Xmlt.xml_take hints_parser Xmlt.xml_return))
(\ h -> Xmlt.xml_return (tr, (n, h)))))))
                            (\ chs ->
                              Xmlt.xml_return
                                (Invariant_Checker.Children_Edge chs))))
                        (Xmlt.xml_do "coverEdge"
                          (Xmlt.xml_take (art_node_id_parser "nodeId")
                            (\ n ->
                              Xmlt.xml_take_default HOL.defaulta
                                (Xmlt.xml_do "hints"
                                  (Xmlt.xml_take hints_parser Xmlt.xml_return))
                                (\ h ->
                                  Xmlt.xml_return
                                    (Invariant_Checker.Cover_Edge n h))))))
                      (\ edges ->
                        Xmlt.xml_return
                          (Invariant_Checker.Art_Node nodeId invariant location
                             edges,
                            (if init then [nodeId] else []))))))));

art_parser ::
  forall a b c d e f g.
    (HOL.Default g) => (String ->
                         (Xml.Xml,
                           ([([Str.Char], [Str.Char])],
                             (Bool, ([String], [String])))) ->
                           Strict_Sum.Sum_bot (Xmlt.Xml_error String) a) ->
                         ((Xml.Xml,
                            ([([Str.Char], [Str.Char])],
                              (Bool, ([String], [String])))) ->
                           Strict_Sum.Sum_bot (Xmlt.Xml_error String) b) ->
                           ((Xml.Xml,
                              ([([Str.Char], [Str.Char])],
                                (Bool, ([String], [String])))) ->
                             Strict_Sum.Sum_bot (Xmlt.Xml_error String) c) ->
                             ((Xml.Xml,
                                ([([Str.Char], [Str.Char])],
                                  (Bool, ([String], [String])))) ->
                               Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                 (Formula.Formula (Term.Term d (e, f)))) ->
                               (Xml.Xml,
                                 ([([Str.Char], [Str.Char])],
                                   (Bool, ([String], [String])))) ->
                                 Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                   (Invariant_Checker.Art_impl_ext d e f b a c g
                                     ());
art_parser art_node_id_parser location_parser trans_parser atom_parser =
  Xmlt.xml_do "impact"
    (Xmlt.xml_take_default []
      (Xmlt.xml_change (art_node_id_parser "initial")
        (\ x -> Xmlt.xml_return [x]))
      (\ init ->
        Xmlt.xml_take
          (Xmlt.xml_do "nodes"
            (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
              (art_node_parser art_node_id_parser location_parser trans_parser
                atom_parser)
              Xmlt.xml_return))
          (\ pairs ->
            let {
              nodes = map fst pairs;
              inits = init ++ concatMap snd pairs;
            } in Xmlt.xml_return
                   (Invariant_Checker.Art_impl_ext inits nodes ()))));

variable_parser ::
  (Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String) [Str.Char];
variable_parser = Xmlt.xml_text "variableId";

exp_parsera ::
  forall a.
    ((Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
      Strict_Sum.Sum_bot (Xmlt.Xml_error String) a) ->
      (Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xmlt.Xml_error String)
          (Term.Term Integer_Arithmetic.Sig (a, Integer_Arithmetic.Ty));
exp_parsera v xml =
  Xmlt.xml_or
    (Xmlt.xml_do "product"
      (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
        (exp_parsera v)
        (\ exps ->
          Xmlt.xml_return
            (Term.Fun (Integer_Arithmetic.ProdF (List.size_list exps)) exps))))
    (Xmlt.xml_or
      (Xmlt.xml_do "sum"
        (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
          (exp_parsera v)
          (\ exps ->
            Xmlt.xml_return
              (Term.Fun (Integer_Arithmetic.SumF (List.size_list exps)) exps))))
      (Xmlt.xml_or
        (Xmlt.xml_change (Xmlt.xml_int "constant")
          (\ i -> Xmlt.xml_return (Term.Fun (Integer_Arithmetic.ConstF i) [])))
        (Xmlt.xml_change v
          (\ x -> Xmlt.xml_return (Term.Var (x, Integer_Arithmetic.IntT))))))
    xml;

exp_parser ::
  (Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
      (Term.Term Integer_Arithmetic.Sig ([Str.Char], Integer_Arithmetic.Ty));
exp_parser = exp_parsera variable_parser;

transition_parser ::
  forall a b c d e.
    ((Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
      Strict_Sum.Sum_bot (Xmlt.Xml_error String) a) ->
      ((Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xmlt.Xml_error String) b) ->
        ((Xml.Xml,
           ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
          Strict_Sum.Sum_bot (Xmlt.Xml_error String)
            (Formula.Formula (Term.Term c (LTS.Trans_var d, e)))) ->
          (Xml.Xml,
            ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
            Strict_Sum.Sum_bot (Xmlt.Xml_error String)
              (b, LTS.Transition_rule c d e a);
transition_parser location_parser trans_parser tatom_parser =
  Xmlt.xml_do "transition"
    (Xmlt.xml_take trans_parser
      (\ tr ->
        Xmlt.xml_take
          (Xmlt.xml_do "source" (Xmlt.xml_take location_parser Xmlt.xml_return))
          (\ l ->
            Xmlt.xml_take
              (Xmlt.xml_do "target"
                (Xmlt.xml_take location_parser Xmlt.xml_return))
              (\ r ->
                Xmlt.xml_take
                  (Xmlt.xml_do "formula"
                    (Xmlt.xml_take (formula_parser tatom_parser)
                      Xmlt.xml_return))
                  (\ phi -> Xmlt.xml_return (tr, LTS.Transition l r phi))))));

lts_parser ::
  forall a b c d e.
    ((Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
      Strict_Sum.Sum_bot (Xmlt.Xml_error String) a) ->
      ((Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xmlt.Xml_error String) b) ->
        ((Xml.Xml,
           ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
          Strict_Sum.Sum_bot (Xmlt.Xml_error String)
            (Formula.Formula (Term.Term c (LTS.Trans_var d, e)))) ->
          String ->
            (Xml.Xml,
              ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
              Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                (LTS.Lts_impl c d e a b);
lts_parser location_parser trans_parser tatom_parser tag =
  Xmlt.xml_do tag
    (Xmlt.xml_take
      (Xmlt.xml_do "initial"
        (Xmlt.xml_take_many_sub [] Arith.one_nat Extended_Nat.Infinity_enat
          location_parser Xmlt.xml_return))
      (\ i ->
        Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
          (transition_parser location_parser trans_parser tatom_parser)
          (\ t -> Xmlt.xml_return (LTS.Lts_Impl i t []))));

bexp_parser ::
  forall a.
    ((Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
      Strict_Sum.Sum_bot (Xmlt.Xml_error String) a) ->
      (Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xmlt.Xml_error String)
          (Formula.Formula
            (Term.Term Integer_Arithmetic.Sig (a, Integer_Arithmetic.Ty)));
bexp_parser v =
  let {
    bexp_parser =
      Xmlt.xml_or
        (Xmlt.xml_do "leq"
          (Xmlt.xml_take (exp_parsera v)
            (\ l ->
              Xmlt.xml_take (exp_parsera v)
                (\ r ->
                  Xmlt.xml_return (Term.Fun Integer_Arithmetic.LeF [l, r])))))
        (Xmlt.xml_or
          (Xmlt.xml_do "less"
            (Xmlt.xml_take (exp_parsera v)
              (\ l ->
                Xmlt.xml_take (exp_parsera v)
                  (\ r ->
                    Xmlt.xml_return
                      (Term.Fun Integer_Arithmetic.LessF [l, r])))))
          (Xmlt.xml_or
            (Xmlt.xml_do "eq"
              (Xmlt.xml_take (exp_parsera v)
                (\ l ->
                  Xmlt.xml_take (exp_parsera v)
                    (\ r ->
                      Xmlt.xml_return
                        (Term.Fun Integer_Arithmetic.EqF [l, r])))))
            (Xmlt.xml_or
              (Xmlt.xml_do "geq"
                (Xmlt.xml_take (exp_parsera v)
                  (\ l ->
                    Xmlt.xml_take (exp_parsera v)
                      (\ r ->
                        Xmlt.xml_return
                          (Term.Fun Integer_Arithmetic.LeF [r, l])))))
              (Xmlt.xml_do "greater"
                (Xmlt.xml_take (exp_parsera v)
                  (\ l ->
                    Xmlt.xml_take (exp_parsera v)
                      (\ r ->
                        Xmlt.xml_return
                          (Term.Fun Integer_Arithmetic.LessF [r, l]))))))));
  } in Xmlt.xml_or
         (Xmlt.xml_do "not"
           (Xmlt.xml_take bexp_parser
             (\ a -> Xmlt.xml_return (Formula.NegAtom a))))
         (Xmlt.xml_change bexp_parser (Xmlt.xml_return . Formula.Atom));

atom_parser ::
  (Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
      (Formula.Formula
        (Term.Term Integer_Arithmetic.Sig ([Str.Char], Integer_Arithmetic.Ty)));
atom_parser = Xmlt.xml_change (bexp_parser variable_parser) Xmlt.xml_return;

type_parser ::
  (Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String) Integer_Arithmetic.Ty;
type_parser =
  Xmlt.xml_or (Xmlt.xml_do "int" (Xmlt.xml_return Integer_Arithmetic.IntT))
    (Xmlt.xml_do "bool" (Xmlt.xml_return Integer_Arithmetic.BoolT));

trans_var_parser ::
  (Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String) (LTS.Trans_var [Str.Char]);
trans_var_parser =
  Xmlt.xml_or
    (Xmlt.xml_do "post"
      (Xmlt.xml_take variable_parser (\ v -> Xmlt.xml_return (LTS.Post v))))
    (Xmlt.xml_or
      (Xmlt.xml_do "aux"
        (Xmlt.xml_take variable_parser
          (\ v -> Xmlt.xml_return (LTS.Intermediate v))))
      (Xmlt.xml_change variable_parser (Xmlt.xml_return . LTS.Pre)));

tatom_parser ::
  (Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
      (Formula.Formula
        (Term.Term Integer_Arithmetic.Sig
          (LTS.Trans_var [Str.Char], Integer_Arithmetic.Ty)));
tatom_parser = Xmlt.xml_change (bexp_parser trans_var_parser) Xmlt.xml_return;

tatom_parsera ::
  (Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
      (Formula.Formula
        (Term.Term Integer_Arithmetic.Sig
          (LTS.Trans_var [Str.Char], Integer_Arithmetic.Ty)));
tatom_parsera = Xmlt.xml_change (bexp_parser trans_var_parser) Xmlt.xml_return;

sharp_trans_id ::
  forall a.
    (String ->
      (Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xmlt.Xml_error String) a) ->
      (Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xmlt.Xml_error String)
          (Cooperation_Program.Sharp a);
sharp_trans_id trans_id_parser =
  Xmlt.xml_or
    (Xmlt.xml_change (trans_id_parser "transitionDuplicate")
      (Xmlt.xml_return . Cooperation_Program.Sharp))
    (Xmlt.xml_change (trans_id_parser "transitionId")
      (Xmlt.xml_return . Cooperation_Program.Flat));

location_parser ::
  forall a.
    (String ->
      (Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xmlt.Xml_error String) a) ->
      (Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xmlt.Xml_error String) a;
location_parser location_id_parser = location_id_parser "locationId";

cut_points_to_transitions ::
  forall a b c d e.
    [(Cooperation_Program.Sharp a,
       LTS.Transition_rule b c d (Cooperation_Program.Sharp e))] ->
      [(e, (a, Formula.Formula (Term.Term b (LTS.Trans_var c, d))))] ->
        [(Cooperation_Program.Sharp a,
           LTS.Transition_rule b c d (Cooperation_Program.Sharp e))];
cut_points_to_transitions ts [] = ts;
cut_points_to_transitions ts ((l, (tr, phi)) : cps) =
  cut_points_to_transitions
    ((Cooperation_Program.Flat tr,
       LTS.Transition (Cooperation_Program.Flat l) (Cooperation_Program.Sharp l)
         phi) :
      ts)
    cps;

cutPoints_parser ::
  forall a b c d e.
    (String ->
      (Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xmlt.Xml_error String) a) ->
      (String ->
        (Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
          Strict_Sum.Sum_bot (Xmlt.Xml_error String) b) ->
        ((Xml.Xml,
           ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
          Strict_Sum.Sum_bot (Xmlt.Xml_error String)
            (Formula.Formula (Term.Term c (LTS.Trans_var d, e)))) ->
          (Xml.Xml,
            ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
            Strict_Sum.Sum_bot (Xmlt.Xml_error String)
              [(Cooperation_Program.Sharp b,
                 LTS.Transition_rule c d e (Cooperation_Program.Sharp a))];
cutPoints_parser location_id_parser trans_id_parser tatom_parser =
  Xmlt.xml_do "cutPoints"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (Xmlt.xml_do "cutPoint"
        (Xmlt.xml_take (location_id_parser "locationId")
          (\ l ->
            Xmlt.xml_take (trans_id_parser "skipId")
              (\ tr ->
                Xmlt.xml_take
                  (Xmlt.xml_do "skipFormula"
                    (Xmlt.xml_take (formula_parser tatom_parser)
                      Xmlt.xml_return))
                  (\ phi -> Xmlt.xml_return (l, (tr, phi)))))))
      (\ tuples -> Xmlt.xml_return (cut_points_to_transitions [] tuples)));

invariant_parser ::
  forall a b c d.
    ((Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
      Strict_Sum.Sum_bot (Xmlt.Xml_error String) a) ->
      ((Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xmlt.Xml_error String)
          (Formula.Formula (Term.Term b (c, d)))) ->
        (Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
          Strict_Sum.Sum_bot (Xmlt.Xml_error String)
            (a, Formula.Formula (Term.Term b (c, d)));
invariant_parser location_parser atom_parser =
  Xmlt.xml_do "invariant"
    (Xmlt.xml_take
      (Xmlt.xml_do "location" (Xmlt.xml_take location_parser Xmlt.xml_return))
      (\ l ->
        Xmlt.xml_take
          (Xmlt.xml_do "formula"
            (Xmlt.xml_take (formula_parser atom_parser) Xmlt.xml_return))
          (\ phi -> Xmlt.xml_return (l, phi))));

lts_input_parser ::
  (Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
      (LTS.Lts_impl Integer_Arithmetic.Sig [Str.Char] Integer_Arithmetic.Ty
        [Str.Char] [Str.Char]);
lts_input_parser =
  lts_parser (location_parser Xmlt.xml_text) (trans_id Xmlt.xml_text)
    tatom_parsera "lts";

invariants_parser ::
  forall a b c d.
    ((Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
      Strict_Sum.Sum_bot (Xmlt.Xml_error String) a) ->
      ((Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xmlt.Xml_error String)
          (Formula.Formula (Term.Term b (c, d)))) ->
        (Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
          Strict_Sum.Sum_bot (Xmlt.Xml_error String)
            [(a, Formula.Formula (Term.Term b (c, d)))];
invariants_parser location_parser atom_parser =
  Xmlt.xml_do "invariants"
    (Xmlt.xml_take_many_sub [] Arith.zero_nat Extended_Nat.Infinity_enat
      (invariant_parser location_parser atom_parser) Xmlt.xml_return);

safety_input_parser ::
  forall a b c d e.
    ((Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
      Strict_Sum.Sum_bot (Xmlt.Xml_error String) a) ->
      ((Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xmlt.Xml_error String) b) ->
        ((Xml.Xml,
           ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
          Strict_Sum.Sum_bot (Xmlt.Xml_error String)
            (Formula.Formula (Term.Term c (LTS.Trans_var d, e)))) ->
          (Xml.Xml,
            ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
            Strict_Sum.Sum_bot (Xmlt.Xml_error String)
              (LTS.Lts_impl c d e a b, [a]);
safety_input_parser location_parser trans_parser tatom_parser =
  Xmlt.xml_do "ltsSafetyInput"
    (Xmlt.xml_take (lts_parser location_parser trans_parser tatom_parser "lts")
      (\ lts ->
        Xmlt.xml_take
          (Xmlt.xml_do "error"
            (Xmlt.xml_take_many_sub [] Arith.one_nat Extended_Nat.Infinity_enat
              location_parser Xmlt.xml_return))
          (\ err -> Xmlt.xml_return (lts, err))));

invariant_proof_parser ::
  forall a b c d e f.
    (HOL.Default f) => ((Xml.Xml,
                          ([([Str.Char], [Str.Char])],
                            (Bool, ([String], [String])))) ->
                         Strict_Sum.Sum_bot (Xmlt.Xml_error String) a) ->
                         ((Xml.Xml,
                            ([([Str.Char], [Str.Char])],
                              (Bool, ([String], [String])))) ->
                           Strict_Sum.Sum_bot (Xmlt.Xml_error String) b) ->
                           ((Xml.Xml,
                              ([([Str.Char], [Str.Char])],
                                (Bool, ([String], [String])))) ->
                             Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                               (Formula.Formula (Term.Term c (d, e)))) ->
                             [(a, Formula.Formula (Term.Term c (d, e)))] ->
                               (Xml.Xml,
                                 ([([Str.Char], [Str.Char])],
                                   (Bool, ([String], [String])))) ->
                                 Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                   (Invariant_Proof_Checkers.Invariant_proof c d
                                     e a [Str.Char] b f);
invariant_proof_parser location_parser trans_parser atom_parser i =
  Xmlt.xml_change
    (art_parser Xmlt.xml_text location_parser trans_parser atom_parser)
    (\ prf -> Xmlt.xml_return (Invariant_Proof_Checkers.Impact i prf));

safety_proof_parser ::
  forall a b c d e f.
    (HOL.Default f) => ((Xml.Xml,
                          ([([Str.Char], [Str.Char])],
                            (Bool, ([String], [String])))) ->
                         Strict_Sum.Sum_bot (Xmlt.Xml_error String) a) ->
                         ((Xml.Xml,
                            ([([Str.Char], [Str.Char])],
                              (Bool, ([String], [String])))) ->
                           Strict_Sum.Sum_bot (Xmlt.Xml_error String) b) ->
                           ((Xml.Xml,
                              ([([Str.Char], [Str.Char])],
                                (Bool, ([String], [String])))) ->
                             Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                               (Formula.Formula (Term.Term c (d, e)))) ->
                             (Xml.Xml,
                               ([([Str.Char], [Str.Char])],
                                 (Bool, ([String], [String])))) ->
                               Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                 (LTS_Safety_Prover.Safety_proof c d e a
                                   [Str.Char] b f);
safety_proof_parser location_parser trans_parser atom_parser =
  Xmlt.xml_do "safetyViaInvariants"
    (Xmlt.xml_take (invariants_parser location_parser atom_parser)
      (\ i ->
        Xmlt.xml_take
          (invariant_proof_parser location_parser trans_parser atom_parser i)
          (\ p ->
            Xmlt.xml_return
              (LTS_Safety_Prover.Invariant_Assertion p
                LTS_Safety_Prover.Trivial))));

sharp_location_parser ::
  forall a.
    (String ->
      (Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xmlt.Xml_error String) a) ->
      (Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xmlt.Xml_error String)
          (Cooperation_Program.Sharp a);
sharp_location_parser location_id_parser =
  Xmlt.xml_or
    (Xmlt.xml_change (location_id_parser "locationDuplicate")
      (Xmlt.xml_return . Cooperation_Program.Sharp))
    (Xmlt.xml_change (location_id_parser "locationId")
      (Xmlt.xml_return . Cooperation_Program.Flat));

lts_safety_input_parser ::
  (Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
      (LTS.Lts_impl Integer_Arithmetic.Sig [Str.Char] Integer_Arithmetic.Ty
         [Str.Char] [Str.Char],
        [[Str.Char]]);
lts_safety_input_parser =
  safety_input_parser (location_parser Xmlt.xml_text) (trans_id Xmlt.xml_text)
    tatom_parsera;

lts_safety_proof_parser ::
  forall a.
    (HOL.Default a) => (Xml.Xml,
                         ([([Str.Char], [Str.Char])],
                           (Bool, ([String], [String])))) ->
                         Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                           (LTS_Safety_Prover.Safety_proof
                             Integer_Arithmetic.Sig [Str.Char]
                             Integer_Arithmetic.Ty [Str.Char] [Str.Char]
                             [Str.Char] a);
lts_safety_proof_parser =
  safety_proof_parser (location_parser Xmlt.xml_text) (trans_id Xmlt.xml_text)
    atom_parser;

cooperation_proof_parser ::
  forall a b c d e f.
    (Collection_Order.Ccompare a, Eq a, Collection_Order.Ccompare e, Eq e,
      Mapping_Impl.Mapping_impl e,
      HOL.Default f) => (String ->
                          (Xml.Xml,
                            ([([Str.Char], [Str.Char])],
                              (Bool, ([String], [String])))) ->
                            Strict_Sum.Sum_bot (Xmlt.Xml_error String) a) ->
                          ((Xml.Xml,
                             ([([Str.Char], [Str.Char])],
                               (Bool, ([String], [String])))) ->
                            Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                              (Term.Term b (c, d))) ->
                            ((Xml.Xml,
                               ([([Str.Char], [Str.Char])],
                                 (Bool, ([String], [String])))) ->
                              Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                (Formula.Formula (Term.Term b (c, d)))) ->
                              ((Xml.Xml,
                                 ([([Str.Char], [Str.Char])],
                                   (Bool, ([String], [String])))) ->
                                Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                  (Formula.Formula
                                    (Term.Term b (LTS.Trans_var c, d)))) ->
                                ((Xml.Xml,
                                   ([([Str.Char], [Str.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    c) ->
                                  ((Xml.Xml,
                                     ([([Str.Char], [Str.Char])],
                                       (Bool, ([String], [String])))) ->
                                    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                      d) ->
                                    d -> ((Xml.Xml,
    ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
   Strict_Sum.Sum_bot (Xmlt.Xml_error String) e) ->
   (Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
     Strict_Sum.Sum_bot (Xmlt.Xml_error String)
       (LTS_Termination_Prover.Cooperation_proof b c d a e f);
cooperation_proof_parser location_id_parser exp_parser atom_parser tatom_parser
  variable_parser type_parser dom_type trans_parser xs =
  Xmlt.xml_or
    (Xmlt.xml_do "trivial" (Xmlt.xml_return LTS_Termination_Prover.Trivial))
    (Xmlt.xml_or
      (Xmlt.xml_do "newInvariants"
        (Xmlt.xml_take
          (invariants_parser (sharp_location_parser location_id_parser)
            atom_parser)
          (\ i ->
            Xmlt.xml_take
              (invariant_proof_parser (sharp_location_parser location_id_parser)
                trans_parser atom_parser i)
              (\ p ->
                Xmlt.xml_take
                  (cooperation_proof_parser location_id_parser exp_parser
                    atom_parser tatom_parser variable_parser type_parser
                    dom_type trans_parser)
                  (\ cp ->
                    Xmlt.xml_return
                      (LTS_Termination_Prover.Invariants_Update p cp))))))
      (Xmlt.xml_or
        (Xmlt.xml_do "transitionRemoval"
          (Xmlt.xml_take
            (Xmlt.xml_do "rankingFunctions"
              (Xmlt.xml_take_many_sub [] Arith.zero_nat
                Extended_Nat.Infinity_enat
                (Xmlt.xml_do "rankingFunction"
                  (Xmlt.xml_take
                    (Xmlt.xml_do "location"
                      (Xmlt.xml_take (sharp_location_parser location_id_parser)
                        Xmlt.xml_return))
                    (\ l ->
                      Xmlt.xml_take
                        (Xmlt.xml_do "expression"
                          (Xmlt.xml_take_many_sub [] Arith.one_nat
                            Extended_Nat.Infinity_enat exp_parser
                            Xmlt.xml_return))
                        (\ es -> Xmlt.xml_return (l, es)))))
                Xmlt.xml_return))
            (\ rs ->
              Xmlt.xml_take
                (Xmlt.xml_do "bound"
                  (Xmlt.xml_take_many_sub [] Arith.zero_nat
                    Extended_Nat.Infinity_enat exp_parser Xmlt.xml_return))
                (\ bounds ->
                  Xmlt.xml_take
                    (Xmlt.xml_do "remove"
                      (Xmlt.xml_take_many_sub [] Arith.zero_nat
                        Extended_Nat.Infinity_enat trans_parser
                        Xmlt.xml_return))
                    (\ removed ->
                      Xmlt.xml_take_default (\ _ -> HOL.defaulta)
                        (Xmlt.xml_do "hints"
                          (Xmlt.xml_take_many_sub [] Arith.zero_nat
                            Extended_Nat.Infinity_enat
                            (Xmlt.xml_do "hint"
                              (Xmlt.xml_take trans_parser
                                (\ tr ->
                                  Xmlt.xml_take_default HOL.defaulta
                                    hints_parser
                                    (\ hint -> Xmlt.xml_return (tr, hint)))))
                            (\ pairs ->
                              Xmlt.xml_return
                                (Map_Of.map_of_default HOL.defaulta pairs))))
                        (\ hinter ->
                          Xmlt.xml_take
                            (cooperation_proof_parser location_id_parser
                              exp_parser atom_parser tatom_parser
                              variable_parser type_parser dom_type trans_parser)
                            (\ inner ->
                              let {
                                rf = Map_Of.map_of_default [] rs;
                              } in Xmlt.xml_return
                                     (LTS_Termination_Prover.Transition_Removal
                                       (Transition_Removal.Transition_removal_info
 rf removed dom_type bounds hinter)
                                       inner))))))))
        (Xmlt.xml_or
          (Xmlt.xml_do "locationAddition"
            (Xmlt.xml_take
              (transition_parser (sharp_location_parser location_id_parser)
                trans_parser tatom_parser)
              (\ tr ->
                Xmlt.xml_take
                  (cooperation_proof_parser location_id_parser exp_parser
                    atom_parser tatom_parser variable_parser type_parser
                    dom_type trans_parser)
                  (\ prof ->
                    (case tr of {
                      (tr_id, tau) ->
                        Xmlt.xml_return
                          (LTS_Termination_Prover.Location_Addition
                            (Location_Addition.Location_Addition_Info
                              (LTS.source tau) (LTS.target tau) tr_id tau)
                            prof);
                    })))))
          (Xmlt.xml_or
            (Xmlt.xml_do "freshVariableAddition"
              (Xmlt.xml_take variable_parser
                (\ x1 ->
                  Xmlt.xml_take type_parser
                    (\ x2 ->
                      Xmlt.xml_take
                        (Xmlt.xml_do "additionalFormulas"
                          (Xmlt.xml_take_many_sub [] Arith.zero_nat
                            Extended_Nat.Infinity_enat
                            (Xmlt.xml_do "additionalFormula"
                              (Xmlt.xml_take trans_parser
                                (\ tr ->
                                  Xmlt.xml_take (formula_parser tatom_parser)
                                    (\ phi -> Xmlt.xml_return (tr, phi)))))
                            Xmlt.xml_return))
                        (\ x3 ->
                          Xmlt.xml_take
                            (cooperation_proof_parser location_id_parser
                              exp_parser atom_parser tatom_parser
                              variable_parser type_parser dom_type trans_parser)
                            (\ prof ->
                              Xmlt.xml_return
                                (LTS_Termination_Prover.Fresh_Variable_Addition
                                  (Fresh_Variable_Addition.Fresh_Variable_Addition_Info
                                    x1 x2 x3)
                                  prof)))))))
            (Xmlt.xml_or
              (Xmlt.xml_do "cutTransitionSplit"
                (Xmlt.xml_take_many_sub [] Arith.zero_nat
                  Extended_Nat.Infinity_enat
                  (Xmlt.xml_do "cutTransitionsWithProof"
                    (Xmlt.xml_take
                      (Xmlt.xml_do "cutTransitions"
                        (Xmlt.xml_take_many_sub [] Arith.zero_nat
                          Extended_Nat.Infinity_enat trans_parser
                          Xmlt.xml_return))
                      (\ cuts ->
                        Xmlt.xml_take
                          (cooperation_proof_parser location_id_parser
                            exp_parser atom_parser tatom_parser variable_parser
                            type_parser dom_type trans_parser)
                          (\ prof -> Xmlt.xml_return (cuts, prof)))))
                  (\ ps ->
                    Xmlt.xml_return
                      (LTS_Termination_Prover.Cut_Transition_Split ps))))
              (Xmlt.xml_do "sccDecomposition"
                (Xmlt.xml_take_many_sub [] Arith.zero_nat
                  Extended_Nat.Infinity_enat
                  (Xmlt.xml_do "sccWithProof"
                    (Xmlt.xml_take
                      (Xmlt.xml_do "scc"
                        (Xmlt.xml_take_many_sub [] Arith.one_nat
                          Extended_Nat.Infinity_enat
                          (sharp_location_parser location_id_parser)
                          Xmlt.xml_return))
                      (\ scc ->
                        Xmlt.xml_take
                          (cooperation_proof_parser location_id_parser
                            exp_parser atom_parser tatom_parser variable_parser
                            type_parser dom_type trans_parser)
                          (\ prof -> Xmlt.xml_return (scc, prof)))))
                  (\ sccs ->
                    Xmlt.xml_return
                      (LTS_Termination_Prover.Scc_Decomp sccs)))))))))
    xs;

termination_proof_parser ::
  forall a b c d e f.
    (Collection_Order.Ccompare a, Eq a, Collection_Order.Ccompare b, Eq b,
      HOL.Default f) => (String ->
                          (Xml.Xml,
                            ([([Str.Char], [Str.Char])],
                              (Bool, ([String], [String])))) ->
                            Strict_Sum.Sum_bot (Xmlt.Xml_error String) a) ->
                          (String ->
                            (Xml.Xml,
                              ([([Str.Char], [Str.Char])],
                                (Bool, ([String], [String])))) ->
                              Strict_Sum.Sum_bot (Xmlt.Xml_error String) b) ->
                            ((Xml.Xml,
                               ([([Str.Char], [Str.Char])],
                                 (Bool, ([String], [String])))) ->
                              Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                (Term.Term c (d, e))) ->
                              ((Xml.Xml,
                                 ([([Str.Char], [Str.Char])],
                                   (Bool, ([String], [String])))) ->
                                Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                  (Formula.Formula (Term.Term c (d, e)))) ->
                                ((Xml.Xml,
                                   ([([Str.Char], [Str.Char])],
                                     (Bool, ([String], [String])))) ->
                                  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                    (Formula.Formula
                                      (Term.Term c (LTS.Trans_var d, e)))) ->
                                  ((Xml.Xml,
                                     ([([Str.Char], [Str.Char])],
                                       (Bool, ([String], [String])))) ->
                                    Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                                      d) ->
                                    ((Xml.Xml,
                                       ([([Str.Char], [Str.Char])],
 (Bool, ([String], [String])))) ->
                                      Strict_Sum.Sum_bot (Xmlt.Xml_error String)
e) ->
                                      e ->
(Xml.Xml, ([([Str.Char], [Str.Char])], (Bool, ([String], [String])))) ->
  Strict_Sum.Sum_bot (Xmlt.Xml_error String)
    (LTS_Termination_Prover.Termination_proof c d e a b f);
termination_proof_parser location_id_parser trans_id_parser exp_parser
  atom_parser tatom_parser variable_parser type_parser dom_type xml =
  Xmlt.xml_or
    (Xmlt.xml_do "trivial" (Xmlt.xml_return LTS_Termination_Prover.Triviala))
    (Xmlt.xml_or
      (Xmlt.xml_do "newInvariants"
        (Xmlt.xml_take
          (invariants_parser (location_parser location_id_parser) atom_parser)
          (\ i ->
            Xmlt.xml_take
              (invariant_proof_parser (location_parser location_id_parser)
                (trans_id trans_id_parser) atom_parser i)
              (\ p ->
                Xmlt.xml_take
                  (termination_proof_parser location_id_parser trans_id_parser
                    exp_parser atom_parser tatom_parser variable_parser
                    type_parser dom_type)
                  (\ cp ->
                    Xmlt.xml_return
                      (LTS_Termination_Prover.Invariants_Update_LTS p cp))))))
      (Xmlt.xml_do "switchToCooperationTermination"
        (Xmlt.xml_take
          (cutPoints_parser location_id_parser trans_id_parser tatom_parser)
          (\ cp ->
            Xmlt.xml_take
              (cooperation_proof_parser location_id_parser exp_parser
                atom_parser tatom_parser variable_parser type_parser dom_type
                (sharp_trans_id trans_id_parser))
              (\ p ->
                Xmlt.xml_return
                  (LTS_Termination_Prover.Via_Cooperation [(cp, p)]))))))
    xml;

lts_termination_proof_parser ::
  forall a.
    (HOL.Default a) => (Xml.Xml,
                         ([([Str.Char], [Str.Char])],
                           (Bool, ([String], [String])))) ->
                         Strict_Sum.Sum_bot (Xmlt.Xml_error String)
                           (LTS_Termination_Prover.Termination_proof
                             Integer_Arithmetic.Sig [Str.Char]
                             Integer_Arithmetic.Ty [Str.Char] [Str.Char] a);
lts_termination_proof_parser =
  termination_proof_parser Xmlt.xml_text Xmlt.xml_text exp_parser atom_parser
    tatom_parser variable_parser type_parser Integer_Arithmetic.IntT;

}
