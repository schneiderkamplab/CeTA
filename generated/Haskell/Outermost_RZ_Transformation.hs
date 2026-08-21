{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Outermost_RZ_Transformation(rz_cover_check, rz_linear_lhss,
                               rz_transformed_rules_list)
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
import qualified Exact_Tree_Automata_Completion;
import qualified Tree_Automata_Wit_Impl;
import qualified Tree_Automata_Containment_Impl;
import qualified Tree_Automata_Containment;
import qualified Compare;
import qualified Compare_Order_Instances;
import qualified HOL;
import qualified Name;
import qualified Term_Rewriting;
import qualified Arith;

rz_vars :: forall a. Arith.Nat -> [Term_Rewriting.Term a [Arith.Char]];
rz_vars n = map Term_Rewriting.Var (Name.x_1_to_x_n n);

rz_reset_rule ::
  forall a b.
    a -> a -> a -> b -> (Term_Rewriting.Term a b, Term_Rewriting.Term a b);
rz_reset_rule top_sym up down x =
  (Term_Rewriting.Fun top_sym [Term_Rewriting.Fun up [Term_Rewriting.Var x]],
    Term_Rewriting.Fun top_sym
      [Term_Rewriting.Fun down [Term_Rewriting.Var x]]);

rz_blocked_args ::
  forall a b. a -> [Term_Rewriting.Term a b] -> [Term_Rewriting.Term a b];
rz_blocked_args block ts = map (\ t -> Term_Rewriting.Fun block [t]) ts;

rz_ascent_rule ::
  forall a.
    a -> a -> ((a, Arith.Nat) -> a) ->
                (a, Arith.Nat) ->
                  Arith.Nat ->
                    (Term_Rewriting.Term a [Arith.Char],
                      Term_Rewriting.Term a [Arith.Char]);
rz_ascent_rule up block flat fn i =
  let {
    f = fst fn;
    n = snd fn;
    xs = rz_vars n;
  } in (Term_Rewriting.Fun (flat fn)
          (Arith.list_update (rz_blocked_args block xs) i
            (Term_Rewriting.Fun up [Arith.nth xs i])),
         Term_Rewriting.Fun up [Term_Rewriting.Fun f xs]);

rz_sig_rules_list ::
  forall a b c.
    [(a, Arith.Nat)] ->
      b -> [Term_Rewriting.Ta_rule (Term_Rewriting.Term b c) a];
rz_sig_rules_list f d =
  map (\ fn ->
        Term_Rewriting.TA_rule (fst fn)
          (Arith.replicate (snd fn) (Term_Rewriting.Fun d []))
          (Term_Rewriting.Fun d []))
    f;

rz_ground_instances_rules_list ::
  forall a b.
    [(a, Arith.Nat)] ->
      a -> Term_Rewriting.Term a b ->
             [Term_Rewriting.Ta_rule (Term_Rewriting.Term a b) a];
rz_ground_instances_rules_list f d (Term_Rewriting.Var x) =
  rz_sig_rules_list f d;
rz_ground_instances_rules_list fa d (Term_Rewriting.Fun f ts) =
  Term_Rewriting.TA_rule f (map (Exact_Tree_Automata_Completion.star d) ts)
    (Exact_Tree_Automata_Completion.star d (Term_Rewriting.Fun f ts)) :
    concatMap (rz_ground_instances_rules_list fa d) ts;

rz_map_ta_rule ::
  forall a b c.
    (a -> b) -> Term_Rewriting.Ta_rule a c -> Term_Rewriting.Ta_rule b c;
rz_map_ta_rule h (Term_Rewriting.TA_rule f qs q) =
  Term_Rewriting.TA_rule f (map h qs) (h q);

rz_pattern_rules_list ::
  forall a b c.
    [(a, Arith.Nat)] ->
      a -> b -> Term_Rewriting.Term a c ->
                  [Term_Rewriting.Ta_rule (b, Term_Rewriting.Term a c) a];
rz_pattern_rules_list f d i t =
  map (rz_map_ta_rule (\ a -> (i, a))) (rz_ground_instances_rules_list f d t);

rz_patterns_rules_list_from ::
  forall a b.
    [(a, Arith.Nat)] ->
      a -> Arith.Nat ->
             [Term_Rewriting.Term a b] ->
               [Term_Rewriting.Ta_rule (Arith.Nat, Term_Rewriting.Term a b) a];
rz_patterns_rules_list_from f d i [] = [];
rz_patterns_rules_list_from f d i (t : ts) =
  rz_pattern_rules_list f d i t ++
    rz_patterns_rules_list_from f d (Arith.suc i) ts;

rz_pattern_final_list ::
  forall a b c.
    a -> b -> Term_Rewriting.Term a c -> [(b, Term_Rewriting.Term a c)];
rz_pattern_final_list d i t = [(i, Exact_Tree_Automata_Completion.star d t)];

rz_patterns_final_list_from ::
  forall a b.
    a -> Arith.Nat ->
           [Term_Rewriting.Term a b] -> [(Arith.Nat, Term_Rewriting.Term a b)];
rz_patterns_final_list_from d i [] = [];
rz_patterns_final_list_from d i (t : ts) =
  rz_pattern_final_list d i t ++ rz_patterns_final_list_from d (Arith.suc i) ts;

rz_patterns_ta_code ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare b) => [(a, Arith.Nat)] ->
                              a -> [Term_Rewriting.Term a b] ->
                                     (Arith.Rbt
(Arith.Nat, Term_Rewriting.Term a b) (),
                                       (Arith.Rbt
  (Term_Rewriting.Ta_rule (Arith.Nat, Term_Rewriting.Term a b) a) (),
 ([((Arith.Nat, Term_Rewriting.Term a b),
     (Arith.Nat, Term_Rewriting.Term a b))],
   (Arith.Rbt (Arith.Nat, Term_Rewriting.Term a b) (),
     (Arith.Rbt (a, Arith.Nat)
        (Arith.Rbt
          ([(Arith.Nat, Term_Rewriting.Term a b)],
            (Arith.Nat, Term_Rewriting.Term a b))
          ()),
       (Bool,
         ((Arith.Nat, Term_Rewriting.Term a b) ->
            Arith.Rbt (Arith.Nat, Term_Rewriting.Term a b) (),
           (Arith.Nat, Term_Rewriting.Term a b) ->
             Arith.Rbt (Arith.Nat, Term_Rewriting.Term a b) ())))))));
rz_patterns_ta_code f d ts =
  Tree_Automata_Wit_Impl.ta_make_ls_code
    (rz_patterns_final_list_from d Arith.zero_nat ts)
    (rz_patterns_rules_list_from f d Arith.zero_nat ts) [];

rz_pattern_ta_code ::
  forall a b c.
    (Compare.Compare_order a, Compare.Compare_order b,
      Compare.Compare c) => [(a, Arith.Nat)] ->
                              a -> b -> Term_Rewriting.Term a c ->
  (Arith.Rbt (b, Term_Rewriting.Term a c) (),
    (Arith.Rbt (Term_Rewriting.Ta_rule (b, Term_Rewriting.Term a c) a) (),
      ([((b, Term_Rewriting.Term a c), (b, Term_Rewriting.Term a c))],
        (Arith.Rbt (b, Term_Rewriting.Term a c) (),
          (Arith.Rbt (a, Arith.Nat)
             (Arith.Rbt
               ([(b, Term_Rewriting.Term a c)], (b, Term_Rewriting.Term a c))
               ()),
            (Bool,
              ((b, Term_Rewriting.Term a c) ->
                 Arith.Rbt (b, Term_Rewriting.Term a c) (),
                (b, Term_Rewriting.Term a c) ->
                  Arith.Rbt (b, Term_Rewriting.Term a c) ())))))));
rz_pattern_ta_code f d i t =
  Tree_Automata_Wit_Impl.ta_make_ls_code (rz_pattern_final_list d i t)
    (rz_pattern_rules_list f d i t) [];

rz_cover_check ::
  forall a b.
    (Compare.Compare_order a, Eq a,
      Compare.Compare_order b) => [(a, Arith.Nat)] ->
                                    a -> b -> [Term_Rewriting.Term a b] -> Bool;
rz_cover_check f d cover_var patterns =
  (Tree_Automata_Containment.equal_xoption ::
    Tree_Automata_Containment.Xoption (Term_Rewriting.Term a ()) ->
      Tree_Automata_Containment.Xoption (Term_Rewriting.Term a ()) -> Bool)
    ((Tree_Automata_Containment_Impl.ta_lang_containment_impl ::
       (Arith.Rbt (Arith.Nat, Term_Rewriting.Term a b) (),
         (Arith.Rbt
            (Term_Rewriting.Ta_rule (Arith.Nat, Term_Rewriting.Term a b) a) (),
           ([((Arith.Nat, Term_Rewriting.Term a b),
               (Arith.Nat, Term_Rewriting.Term a b))],
             (Arith.Rbt (Arith.Nat, Term_Rewriting.Term a b) (),
               (Arith.Rbt (a, Arith.Nat)
                  (Arith.Rbt
                    ([(Arith.Nat, Term_Rewriting.Term a b)],
                      (Arith.Nat, Term_Rewriting.Term a b))
                    ()),
                 (Bool,
                   ((Arith.Nat, Term_Rewriting.Term a b) ->
                      Arith.Rbt (Arith.Nat, Term_Rewriting.Term a b) (),
                     (Arith.Nat, Term_Rewriting.Term a b) ->
                       Arith.Rbt (Arith.Nat, Term_Rewriting.Term a b)
                         ()))))))) ->
         (Arith.Rbt (Arith.Nat, Term_Rewriting.Term a b) (),
           (Arith.Rbt
              (Term_Rewriting.Ta_rule (Arith.Nat, Term_Rewriting.Term a b) a)
              (),
             ([((Arith.Nat, Term_Rewriting.Term a b),
                 (Arith.Nat, Term_Rewriting.Term a b))],
               (Arith.Rbt (Arith.Nat, Term_Rewriting.Term a b) (),
                 (Arith.Rbt (a, Arith.Nat)
                    (Arith.Rbt
                      ([(Arith.Nat, Term_Rewriting.Term a b)],
                        (Arith.Nat, Term_Rewriting.Term a b))
                      ()),
                   (Bool,
                     ((Arith.Nat, Term_Rewriting.Term a b) ->
                        Arith.Rbt (Arith.Nat, Term_Rewriting.Term a b) (),
                       (Arith.Nat, Term_Rewriting.Term a b) ->
                         Arith.Rbt (Arith.Nat, Term_Rewriting.Term a b)
                           ()))))))) ->
           Tree_Automata_Containment.Xoption (Term_Rewriting.Term a ()))
      (rz_pattern_ta_code f d Arith.zero_nat (Term_Rewriting.Var cover_var))
      (rz_patterns_ta_code f d patterns))
    Tree_Automata_Containment.XNone;

rz_linear_lhss ::
  forall a b c.
    (Arith.Ceq b, Arith.Ccompare b,
      Arith.Set_impl b) => [(Term_Rewriting.Term a b, c)] ->
                             [Term_Rewriting.Term a b];
rz_linear_lhss r = filter Term_Rewriting.linear_term (map fst r);

rz_source_rule ::
  forall a b c d.
    a -> b -> (Term_Rewriting.Term a c, Term_Rewriting.Term b d) ->
                (Term_Rewriting.Term a c, Term_Rewriting.Term b d);
rz_source_rule down up lr =
  (Term_Rewriting.Fun down [fst lr], Term_Rewriting.Fun up [snd lr]);

rz_descent_rule ::
  forall a b.
    a -> a -> ((a, Arith.Nat) -> a) ->
                Term_Rewriting.Term a b ->
                  Arith.Nat ->
                    (Term_Rewriting.Term a b, Term_Rewriting.Term a b);
rz_descent_rule down block flat (Term_Rewriting.Var x) i =
  (Term_Rewriting.Var x, Term_Rewriting.Var x);
rz_descent_rule down block flat (Term_Rewriting.Fun f ts) i =
  (Term_Rewriting.Fun down [Term_Rewriting.Fun f ts],
    Term_Rewriting.Fun (flat (f, Arith.size_list ts))
      (Arith.list_update (rz_blocked_args block ts) i
        (Term_Rewriting.Fun down [Arith.nth ts i])));

rz_ascent_rules_list ::
  forall a.
    a -> a -> ((a, Arith.Nat) -> a) ->
                [(a, Arith.Nat)] ->
                  [(Term_Rewriting.Term a [Arith.Char],
                     Term_Rewriting.Term a [Arith.Char])];
rz_ascent_rules_list up block flat f =
  concatMap
    (\ fn ->
      map (rz_ascent_rule up block flat fn) (Arith.upt Arith.zero_nat (snd fn)))
    f;

rz_descent_rules_list ::
  forall a b.
    a -> a -> ((a, Arith.Nat) -> a) ->
                [Term_Rewriting.Term a b] ->
                  [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
rz_descent_rules_list down block flat patterns =
  concatMap
    (\ s ->
      map (rz_descent_rule down block flat s)
        (Arith.upt Arith.zero_nat (Arith.size_list (Term_Rewriting.args s))))
    patterns;

rz_transformed_rules_list ::
  forall a.
    a -> a -> a -> a -> ((a, Arith.Nat) -> a) ->
                          [Arith.Char] ->
                            [(a, Arith.Nat)] ->
                              [(Term_Rewriting.Term a [Arith.Char],
                                 Term_Rewriting.Term a [Arith.Char])] ->
                                [Term_Rewriting.Term a [Arith.Char]] ->
                                  [(Term_Rewriting.Term a [Arith.Char],
                                     Term_Rewriting.Term a [Arith.Char])];
rz_transformed_rules_list top_sym up down block flat reset_var f r patterns =
  map (rz_source_rule down up) r ++
    [rz_reset_rule top_sym up down reset_var] ++
      rz_descent_rules_list down block flat patterns ++
        rz_ascent_rules_list up block flat f;

}
