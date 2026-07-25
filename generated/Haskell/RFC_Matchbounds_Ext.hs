{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  RFC_Matchbounds_Ext(rfc_relative_bounds_tt, rfc_automaton_closed_bounds_tt,
                       rfc_matchbox_relative_bounds_tt,
                       rfc_automaton_closed_relative_bounds_tt,
                       rfc_native_rel_matchbox_relative_bounds_tt)
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
import qualified Product_Lexorder;
import qualified List_Lexorder;
import qualified Map_Choice;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Termination_Problem_Spec;
import qualified Matchbounds_Impl;
import qualified Sum_Type;
import qualified Mapping;
import qualified Quasi_Order;
import qualified Matchbounds;
import qualified RBT_Map_Set_Extension;
import qualified RBTSetImpl;
import qualified HOL;
import qualified Tree_Automata_Impl;
import qualified RBT;
import qualified Compare;
import qualified Compare_Order_Instances;
import qualified Arith;
import qualified Term_Rewriting;

rfc_term_word ::
  forall a. Term_Rewriting.Term a [Arith.Char] -> Maybe ([a], [Arith.Char]);
rfc_term_word (Term_Rewriting.Var x) = Just ([], x);
rfc_term_word (Term_Rewriting.Fun f [t]) = (case rfc_term_word t of {
     Nothing -> Nothing;
     Just (w, x) -> Just (f : w, x);
   });
rfc_term_word (Term_Rewriting.Fun f []) = Nothing;
rfc_term_word (Term_Rewriting.Fun f (v : vb : vc)) = Nothing;

rfc_word_term :: forall a b. [a] -> b -> Term_Rewriting.Term a b;
rfc_word_term [] x = Term_Rewriting.Var x;
rfc_word_term (f : fs) x = Term_Rewriting.Fun f [rfc_word_term fs x];

rfc_rule_words ::
  forall a.
    (Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char]) ->
      Maybe ([a], [a]);
rfc_rule_words lr =
  (case lr of {
    (l, r) ->
      (case (rfc_term_word l, rfc_term_word r) of {
        (Nothing, _) -> Nothing;
        (Just (_, _), Nothing) -> Nothing;
        (Just (lw, x), Just (rw, y)) ->
          (if x == y then Just (lw, rw) else Nothing);
      });
  });

rfc_word_res_impl ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare_order b) => RBT.Rbt ((a, Arith.Nat), Arith.Nat)
                                    [Tree_Automata_Impl.Ta_rule_impl b
                                       (a, Arith.Nat)] ->
                                    (b -> RBT.Rbt b ()) ->
                                      b -> Arith.Nat -> [a] -> RBT.Rbt b ();
rfc_word_res_impl ta eps q h [] = eps q;
rfc_word_res_impl ta eps q h (f : fs) =
  let {
    rec = rfc_word_res_impl ta eps q h fs;
    rules = RBT_Map_Set_Extension.rm_set_lookup ta ((f, h), Arith.one_nat);
    arules =
      filter
        (\ rule ->
          RBTSetImpl.memb_rm_basic_ops
            (Arith.nth (Tree_Automata_Impl.r_lhs_states_impl rule)
              Arith.zero_nat)
            rec)
        rules;
  } in RBT_Map_Set_Extension.rs_Union (map Tree_Automata_Impl.rqss_impl arules);

rfc_initial_covers ::
  forall a.
    (Eq a) => [(Term_Rewriting.Term a [Arith.Char],
                 Term_Rewriting.Term a [Arith.Char])] ->
                [Term_Rewriting.Term a [Arith.Char]] -> Bool;
rfc_initial_covers r i = all (\ (_, a) -> Arith.membera i a) r;

rfc_word_reaches_height_impl ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare_order b) => Tree_Automata_Impl.Ta_impl a (b, Arith.Nat) ->
                                    a -> Arith.Nat -> [b] -> a -> Bool;
rfc_word_reaches_height_impl ta q h w p =
  RBTSetImpl.memb_rm_basic_ops p
    (rfc_word_res_impl (Tree_Automata_Impl.ta_rules_impl ta)
      (Tree_Automata_Impl.ta_epss_impl ta) q h w);

rfc_rule_has_top_redex_impl ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare_order b) => Tree_Automata_Impl.Ta_impl a (b, Arith.Nat) ->
                                    [a] ->
                                      Arith.Nat ->
(Term_Rewriting.Term b [Arith.Char], Term_Rewriting.Term b [Arith.Char]) ->
  Bool;
rfc_rule_has_top_redex_impl ta qs c lr =
  (case rfc_rule_words lr of {
    Nothing -> True;
    Just (lw, _) ->
      not (all (\ q ->
                 all (\ p -> not (rfc_word_reaches_height_impl ta q c lw p)) qs)
            qs);
  });

rfc_no_top_redex_impl ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare_order b) => Tree_Automata_Impl.Ta_impl a (b, Arith.Nat) ->
                                    [a] ->
                                      Arith.Nat ->
[(Term_Rewriting.Term b [Arith.Char], Term_Rewriting.Term b [Arith.Char])] ->
  Bool;
rfc_no_top_redex_impl ta qs c r =
  all (\ lr -> not (rfc_rule_has_top_redex_impl ta qs c lr)) r;

rfc_word_reaches_impl ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare_order b) => Tree_Automata_Impl.Ta_impl a (b, Arith.Nat) ->
                                    a -> [b] -> a -> Bool;
rfc_word_reaches_impl ta q w p =
  RBTSetImpl.memb_rm_basic_ops p
    (Tree_Automata_Impl.ta_res_impl (Tree_Automata_Impl.ta_rules_impl ta)
      (Tree_Automata_Impl.ta_epss_impl ta)
      (Term_Rewriting.map_term (\ x -> x) (\ _ -> q)
        (Term_Rewriting.map_term (Matchbounds.lift Arith.zero_nat) (\ x -> x)
          (rfc_word_term w [Arith.char_0x78]))));

rfc_unary_rule_index_impl ::
  forall a b.
    (Compare.Compare_order a) => [Tree_Automata_Impl.Ta_rule_impl a b] ->
                                   RBT.Rbt a
                                     [Tree_Automata_Impl.Ta_rule_impl a b];
rfc_unary_rule_index_impl rules =
  RBT_Map_Set_Extension.elem_list_to_rm
    (\ rule ->
      Arith.nth (Tree_Automata_Impl.r_lhs_states_impl rule) Arith.zero_nat)
    rules;

rfc_word_indexed_step_impl ::
  forall a b.
    (Compare.Compare_order a) => [Tree_Automata_Impl.Ta_rule_impl a b] ->
                                   RBT.Rbt a () -> RBT.Rbt a ();
rfc_word_indexed_step_impl rules rec =
  let {
    idx = rfc_unary_rule_index_impl rules;
  } in RBT_Map_Set_Extension.rs_Union
         (map (\ p ->
                RBT_Map_Set_Extension.rs_Union
                  (map Tree_Automata_Impl.rqss_impl
                    (RBT_Map_Set_Extension.rm_set_lookup idx p)))
           (RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops rec));

rfc_word_results_impl ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare_order b) => RBT.Rbt ((a, Arith.Nat), Arith.Nat)
                                    [Tree_Automata_Impl.Ta_rule_impl b
                                       (a, Arith.Nat)] ->
                                    (b -> RBT.Rbt b ()) ->
                                      Arith.Nat -> [a] -> [b] -> [RBT.Rbt b ()];
rfc_word_results_impl ta eps h [] qs = map eps qs;
rfc_word_results_impl ta eps h (f : fs) qs =
  let {
    recs = rfc_word_results_impl ta eps h fs qs;
    rules = RBT_Map_Set_Extension.rm_set_lookup ta ((f, h), Arith.one_nat);
  } in map (rfc_word_indexed_step_impl rules) recs;

rfc_initial_single_var ::
  forall a. [Term_Rewriting.Term a [Arith.Char]] -> Bool;
rfc_initial_single_var i =
  all (\ t ->
        Arith.less_eq_nat
          (Arith.size_list (Arith.remdups (Term_Rewriting.vars_term_list t)))
          Arith.one_nat)
    i;

rfc_relative_bounds_tt ::
  forall a b c.
    (Compare.Compare_order b, Eq b, Term_Rewriting.Showl b, Arith.Ccompare c,
      Eq c, Mapping.Mapping_impl c, Quasi_Order.Linorder c,
      Term_Rewriting.Showl c) => Termination_Problem_Spec.Tp_ops_ext a b
                                   [Arith.Char] () ->
                                   Matchbounds_Impl.Bounds_info b c ->
                                     [Term_Rewriting.Term b [Arith.Char]] ->
                                       [(Term_Rewriting.Term b [Arith.Char],
  Term_Rewriting.Term b [Arith.Char])] ->
 a -> Sum_Type.Sum (String -> String) a;
rfc_relative_bounds_tt i info initial_terms rdelete tp =
  (case Matchbounds_Impl.get_integer_bounds_info info of {
    (Matchbounds_Impl.Bounds_Info _ _ qfin preTA rel, _) ->
      Error_Monad.bind (Tree_Automata_Impl.generate_ta_cond preTA rel)
        (\ ta ->
          Error_Monad.bind
            (Check_Monad.check (Termination_Problem_Spec.q_empty i tp)
              (Term_Rewriting.showsl_lit
                "RFC relative bounds currently require an empty Q component"))
            (\ _ ->
              Error_Monad.bind
                (Check_Monad.check (null (Termination_Problem_Spec.rw i tp))
                  (Term_Rewriting.showsl_lit
                    "RFC relative bounds currently require no weak rules"))
                (\ _ ->
                  Error_Monad.bind
                    (Check_Monad.check (not (Termination_Problem_Spec.nfs i tp))
                      (Term_Rewriting.showsl_lit
                        "RFC relative bounds currently certify full rewriting, not innermost rewriting"))
                    (\ _ ->
                      Error_Monad.bind
                        (Check_Monad.check
                          (rdelete == Termination_Problem_Spec.r i tp)
                          (Term_Rewriting.showsl_lit
                            "RFC relative bounds currently require deleting exactly all strict rules"))
                        (\ _ ->
                          Error_Monad.bind
                            (Term_Rewriting.check_wf_trs
                              (Termination_Problem_Spec.r i tp))
                            (\ _ ->
                              Error_Monad.bind
                                (Check_Monad.check
                                  (all (\ (_, a) ->
 Term_Rewriting.linear_term a)
                                    (Termination_Problem_Spec.r i tp))
                                  (Term_Rewriting.showsl_lit
                                    "RFC relative bounds require right-linear removed rules"))
                                (\ _ ->
                                  Error_Monad.bind
                                    (Check_Monad.check
                                      (Matchbounds_Impl.rfc_initial_single_var
initial_terms)
                                      (Term_Rewriting.showsl_lit
"RFC relative bounds finite initial language templates must contain at most one variable"))
                                    (\ _ ->
                                      Error_Monad.bind
(Check_Monad.check
  (Matchbounds_Impl.rfc_initial_covers (Termination_Problem_Spec.r i tp)
    initial_terms)
  (Term_Rewriting.showsl_lit
    "RFC relative initial language does not contain all removed-rule right-hand sides"))
(\ _ ->
  Error_Monad.bind
    (Check_Monad.check
      (Matchbounds_Impl.rfc_initial_closed (Termination_Problem_Spec.r i tp)
        initial_terms)
      (Term_Rewriting.showsl_lit
        "RFC relative initial language is not closed under removed-rule one-step right-forward narrowing"))
    (\ _ ->
      Error_Monad.bind
        (Check_Monad.check
          (Matchbounds_Impl.rfc_initial_accepted_with_tail_states_impl HOL.Type
            ta qfin initial_terms)
          (Term_Rewriting.showsl_lit
            "RFC relative finite initial language is not accepted by the automaton for all tail states"))
        (\ _ ->
          Error_Monad.bind
            (Matchbounds_Impl.check_bounds_generic_without_contains info
              (Termination_Problem_Spec.r i tp) [])
            (\ _ ->
              Sum_Type.Inr
                (Termination_Problem_Spec.mk i
                  (Termination_Problem_Spec.nfs i tp)
                  (Termination_Problem_Spec.q i tp) [] rdelete)))))))))))));
  });

rfc_lifted_lhs_top_impl ::
  forall a b. Arith.Nat -> Term_Rewriting.Term (a, Arith.Nat) b -> Bool;
rfc_lifted_lhs_top_impl c l =
  all (\ (f, _) -> Arith.equal_nat (Matchbounds.height f) c)
    (Term_Rewriting.funas_term_list l);

rfc_native_word_res_impl ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare_order b) => RBT.Rbt ((a, Arith.Nat), Arith.Nat)
                                    [Tree_Automata_Impl.Ta_rule_impl b
                                       (a, Arith.Nat)] ->
                                    (b -> RBT.Rbt b ()) ->
                                      b -> Arith.Nat -> [a] -> RBT.Rbt b ();
rfc_native_word_res_impl ta eps q h [] =
  RBTSetImpl.g_from_list_dflt_basic_oops_rm_basic_ops [q];
rfc_native_word_res_impl ta eps q h (f : fs) =
  let {
    rec0 = rfc_native_word_res_impl ta eps q h fs;
    rec = (if null fs then rec0
            else RBT_Map_Set_Extension.rs_Union
                   (map eps
                     (RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops rec0)));
    rules = RBT_Map_Set_Extension.rm_set_lookup ta ((f, h), Arith.one_nat);
    arules =
      filter
        (\ rule ->
          RBTSetImpl.memb_rm_basic_ops
            (Arith.nth (Tree_Automata_Impl.r_lhs_states_impl rule)
              Arith.zero_nat)
            rec)
        rules;
  } in RBTSetImpl.g_from_list_dflt_basic_oops_rm_basic_ops
         (map Tree_Automata_Impl.r_rhs_impl arules);

rfc_rule_automaton_closed_impl ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare_order b) => Tree_Automata_Impl.Ta_impl a (b, Arith.Nat) ->
                                    [a] ->
                                      (Term_Rewriting.Term b [Arith.Char],
Term_Rewriting.Term b [Arith.Char]) ->
Bool;
rfc_rule_automaton_closed_impl ta qs lr =
  (case rfc_rule_words lr of {
    Nothing -> False;
    Just (lw, rw) ->
      all (\ i ->
            let {
              prefix = Arith.take i lw;
              suffix = Arith.drop i lw;
            } in all (\ q ->
                       all (\ m ->
                             all (\ p ->
                                   not (rfc_word_reaches_impl ta q suffix m &&
 rfc_word_reaches_impl ta m prefix p) ||
                                     rfc_word_reaches_impl ta q rw p)
                               qs)
                         qs)
                   qs)
        (Arith.upt Arith.one_nat (Arith.suc (Arith.size_list lw)));
  });

rfc_automaton_closed_impl ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare_order b) => Tree_Automata_Impl.Ta_impl a (b, Arith.Nat) ->
                                    [a] ->
                                      [(Term_Rewriting.Term b [Arith.Char],
 Term_Rewriting.Term b [Arith.Char])] ->
Bool;
rfc_automaton_closed_impl ta qs r =
  all (rfc_rule_automaton_closed_impl ta qs) r;

rfc_word_reaches_some_impl ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare_order b) => Tree_Automata_Impl.Ta_impl a (b, Arith.Nat) ->
                                    [a] -> [b] -> a -> Bool;
rfc_word_reaches_some_impl ta qs w q =
  not (all (\ m -> not (rfc_word_reaches_impl ta q w m)) qs);

rfc_rule_lhs_suffix_total_impl ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare_order b) => Tree_Automata_Impl.Ta_impl a (b, Arith.Nat) ->
                                    [a] ->
                                      (Term_Rewriting.Term b [Arith.Char],
Term_Rewriting.Term b [Arith.Char]) ->
Bool;
rfc_rule_lhs_suffix_total_impl ta qs lr =
  (case rfc_rule_words lr of {
    Nothing -> False;
    Just (lw, _) ->
      not (null lw) &&
        all (\ i -> all (rfc_word_reaches_some_impl ta qs (Arith.drop i lw)) qs)
          (Arith.upt Arith.one_nat (Arith.size_list lw));
  });

rfc_lhs_suffix_total_impl ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare_order b) => Tree_Automata_Impl.Ta_impl a (b, Arith.Nat) ->
                                    [a] ->
                                      [(Term_Rewriting.Term b [Arith.Char],
 Term_Rewriting.Term b [Arith.Char])] ->
Bool;
rfc_lhs_suffix_total_impl ta qs r =
  all (rfc_rule_lhs_suffix_total_impl ta qs) r;

rfc_strict_below_bound_list ::
  forall a b.
    (Eq a,
      Eq b) => (Term_Rewriting.Term (a, Arith.Nat) b -> Bool) ->
                 ((Term_Rewriting.Term a b, Term_Rewriting.Term a b) ->
                   Term_Rewriting.Term a b -> Bool) ->
                   Arith.Nat ->
                     [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                       [(Term_Rewriting.Term (a, Arith.Nat) b,
                          Term_Rewriting.Term (a, Arith.Nat) b)];
rfc_strict_below_bound_list filt ff c r =
  filter (\ (l, _) -> not (rfc_lifted_lhs_top_impl c l))
    (Matchbounds_Impl.cover_bound_list_filter filt ff Matchbounds.Strict_TRS c
      r);

rfc_rule_no_top_redex_indexed_impl ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare_order b) => Tree_Automata_Impl.Ta_impl a (b, Arith.Nat) ->
                                    [a] ->
                                      Arith.Nat ->
(Term_Rewriting.Term b [Arith.Char], Term_Rewriting.Term b [Arith.Char]) ->
  Bool;
rfc_rule_no_top_redex_indexed_impl ta qs c lr =
  let {
    qset = RBTSetImpl.g_from_list_dflt_basic_oops_rm_basic_ops qs;
  } in (case rfc_rule_words lr of {
         Nothing -> False;
         Just (lw, _) ->
           all (\ res ->
                 RBTSetImpl.g_isEmpty_dflt_basic_oops_rm_basic_ops
                   (RBTSetImpl.g_inter_dflt_basic_oops_rm_basic_ops qset res))
             (rfc_word_results_impl (Tree_Automata_Impl.ta_rules_impl ta)
               (Tree_Automata_Impl.ta_epss_impl ta) c lw qs);
       });

rfc_no_top_redex_indexed_impl ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare_order b) => Tree_Automata_Impl.Ta_impl a (b, Arith.Nat) ->
                                    [a] ->
                                      Arith.Nat ->
[(Term_Rewriting.Term b [Arith.Char], Term_Rewriting.Term b [Arith.Char])] ->
  Bool;
rfc_no_top_redex_indexed_impl ta qs c r =
  all (rfc_rule_no_top_redex_indexed_impl ta qs c) r;

rfc_term_accepted_with_tail_states_impl ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare_order b) => HOL.Itself a ->
                                    Tree_Automata_Impl.Ta_impl b
                                      (a, Arith.Nat) ->
                                      [b] ->
Term_Rewriting.Term a [Arith.Char] -> Bool;
rfc_term_accepted_with_tail_states_impl uu ta qfin t =
  all (\ q ->
        not (RBTSetImpl.g_isEmpty_dflt_basic_oops_rm_basic_ops
              (RBTSetImpl.g_inter_dflt_basic_oops_rm_basic_ops
                (Tree_Automata_Impl.ta_final_impl ta)
                (Tree_Automata_Impl.ta_res_impl
                  (Tree_Automata_Impl.ta_rules_impl ta)
                  (Tree_Automata_Impl.ta_epss_impl ta)
                  (Term_Rewriting.map_term (\ x -> x) (\ _ -> q)
                    (Term_Rewriting.map_term (Matchbounds.lift Arith.zero_nat)
                      (\ x -> x) t))))))
    qfin;

rfc_initial_accepted_with_tail_states_impl ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare_order b) => HOL.Itself a ->
                                    Tree_Automata_Impl.Ta_impl b
                                      (a, Arith.Nat) ->
                                      [b] ->
[Term_Rewriting.Term a [Arith.Char]] -> Bool;
rfc_initial_accepted_with_tail_states_impl t ta qfin i =
  all (rfc_term_accepted_with_tail_states_impl t ta qfin) i;

rfc_automaton_closed_bounds_tt ::
  forall a b c.
    (Compare.Compare_order b, Eq b, Term_Rewriting.Showl b, Arith.Ccompare c,
      Eq c, Mapping.Mapping_impl c, Quasi_Order.Linorder c,
      Term_Rewriting.Showl c) => Termination_Problem_Spec.Tp_ops_ext a b
                                   [Arith.Char] () ->
                                   Matchbounds_Impl.Bounds_info b c ->
                                     [Term_Rewriting.Term b [Arith.Char]] ->
                                       a -> Sum_Type.Sum (String -> String) ();
rfc_automaton_closed_bounds_tt i info initial_terms tp =
  (case Matchbounds_Impl.get_integer_bounds_info info of {
    (Matchbounds_Impl.Bounds_Info _ _ _ preTA rel, _) ->
      Error_Monad.bind (Tree_Automata_Impl.generate_ta_cond preTA rel)
        (\ ta ->
          Error_Monad.bind
            (Check_Monad.check (Termination_Problem_Spec.q_empty i tp)
              (Term_Rewriting.showsl_lit
                "RFC automaton-closed bounds currently require an empty Q component"))
            (\ _ ->
              Error_Monad.bind
                (Check_Monad.check (null (Termination_Problem_Spec.rw i tp))
                  (Term_Rewriting.showsl_lit
                    "RFC automaton-closed bounds currently require no weak rules"))
                (\ _ ->
                  Error_Monad.bind
                    (Check_Monad.check (not (Termination_Problem_Spec.nfs i tp))
                      (Term_Rewriting.showsl_lit
                        "RFC automaton-closed bounds currently certify full rewriting, not innermost rewriting"))
                    (\ _ ->
                      Error_Monad.bind
                        (Term_Rewriting.check_wf_trs
                          (Termination_Problem_Spec.r i tp))
                        (\ _ ->
                          Error_Monad.bind
                            (Check_Monad.check
                              (all (\ (_, a) -> Term_Rewriting.linear_term a)
                                (Termination_Problem_Spec.r i tp))
                              (Term_Rewriting.showsl_lit
                                "RFC automaton-closed bounds require right-linear rules"))
                            (\ _ ->
                              Error_Monad.bind
                                (Check_Monad.check
                                  (rfc_initial_single_var initial_terms)
                                  (Term_Rewriting.showsl_lit
                                    "RFC automaton-closed initial language templates must contain at most one variable"))
                                (\ _ ->
                                  Error_Monad.bind
                                    (Check_Monad.check
                                      (rfc_initial_covers
(Termination_Problem_Spec.r i tp) initial_terms)
                                      (Term_Rewriting.showsl_lit
"RFC automaton-closed initial language does not contain all right-hand sides"))
                                    (\ _ ->
                                      Error_Monad.bind
(Check_Monad.check
  (rfc_initial_accepted_with_tail_states_impl HOL.Type ta
    (Arith.remdups (Matchbounds_Impl.states_of_tree_automata_dup preTA))
    initial_terms)
  (Term_Rewriting.showsl_lit
    "RFC automaton-closed initial language is not accepted by the automaton for all automaton states"))
(\ _ ->
  Error_Monad.bind
    (Check_Monad.check
      (rfc_automaton_closed_impl ta
        (Arith.remdups (Matchbounds_Impl.states_of_tree_automata_dup preTA))
        (Termination_Problem_Spec.r i tp))
      (Term_Rewriting.showsl_lit "RFC automaton-closed split condition failed"))
    (\ _ ->
      Error_Monad.bind
        (Check_Monad.check
          (rfc_lhs_suffix_total_impl ta
            (Arith.remdups (Matchbounds_Impl.states_of_tree_automata_dup preTA))
            (Termination_Problem_Spec.r i tp))
          (Term_Rewriting.showsl_lit
            "RFC automaton-closed lhs suffix totality condition failed"))
        (\ _ ->
          Matchbounds_Impl.check_bounds_generic_without_contains info
            (Termination_Problem_Spec.r i tp) [])))))))))));
  });

rfc_rule_matchbox_ext_right_indexed_impl ::
  forall a b.
    (Compare.Compare_order a, Eq a,
      Compare.Compare_order b) => Tree_Automata_Impl.Ta_impl a (b, Arith.Nat) ->
                                    Tree_Automata_Impl.Ta_relation a ->
                                      [a] ->
[a] ->
  (Term_Rewriting.Term b [Arith.Char], Term_Rewriting.Term b [Arith.Char]) ->
    Bool;
rfc_rule_matchbox_ext_right_indexed_impl ta rel tails qs lr =
  (case rfc_rule_words lr of {
    Nothing -> False;
    Just (lw, rw) ->
      not (null lw) &&
        let {
          rhs = rfc_word_results_impl (Tree_Automata_Impl.ta_rules_impl ta)
                  (Tree_Automata_Impl.ta_epss_impl ta) Arith.zero_nat rw tails;
        } in all (\ i ->
                   let {
                     prefix = Arith.take i lw;
                   } in Arith.list_all2
                          (\ lhs rhsa ->
                            Arith.is_none
                              (Tree_Automata_Impl.rel_checker rel lhs rhsa))
                          (rfc_word_results_impl
                            (Tree_Automata_Impl.ta_rules_impl ta)
                            (Tree_Automata_Impl.ta_epss_impl ta) Arith.zero_nat
                            prefix tails)
                          rhs)
               (Arith.upt Arith.one_nat (Arith.size_list lw));
  });

rfc_matchbox_ext_right_indexed_impl ::
  forall a b.
    (Compare.Compare_order a, Eq a,
      Compare.Compare_order b) => Tree_Automata_Impl.Ta_impl a (b, Arith.Nat) ->
                                    Tree_Automata_Impl.Ta_relation a ->
                                      [a] ->
[a] ->
  [(Term_Rewriting.Term b [Arith.Char], Term_Rewriting.Term b [Arith.Char])] ->
    Bool;
rfc_matchbox_ext_right_indexed_impl ta rel tails qs r =
  all (rfc_rule_matchbox_ext_right_indexed_impl ta rel tails qs) r;

check_bounds_generic_rfc_relative ::
  forall a b.
    (Compare.Compare_order a, Eq a, Term_Rewriting.Showl a, Arith.Ccompare b,
      Eq b, Mapping.Mapping_impl b, Quasi_Order.Linorder b,
      Term_Rewriting.Showl b) => Matchbounds_Impl.Bounds_info a b ->
                                   [(Term_Rewriting.Term a [Arith.Char],
                                      Term_Rewriting.Term a [Arith.Char])] ->
                                     [(Term_Rewriting.Term a [Arith.Char],
Term_Rewriting.Term a [Arith.Char])] ->
                                       Sum_Type.Sum (String -> String) ();
check_bounds_generic_rfc_relative bi r s =
  (case Matchbounds_Impl.get_integer_bounds_info bi of {
    (Matchbounds_Impl.Bounds_Info typea c qfin preTA rel, ren) ->
      Error_Monad.catch_error
        (let {
           c_opt = Matchbounds_Impl.construct_c_opt c r;
           rs = r ++ s;
         } in Error_Monad.bind (Tree_Automata_Impl.generate_ta_cond preTA rel)
                (\ ta ->
                  let {
                    rell = Tree_Automata_Impl.rel_checker rel;
                  } in Error_Monad.bind (Term_Rewriting.check_wf_trs rs)
                         (\ _ ->
                           Error_Monad.bind
                             (Check_Monad.check
                               (Arith.less_eq_set (Arith.set qfin)
                                 (RBTSetImpl.alpha_rm_basic_ops
                                   (Tree_Automata_Impl.ta_final_impl ta)))
                               (Term_Rewriting.showsl_lit
                                 "explicitly mentioned final states must be final"))
                             (\ _ ->
                               Error_Monad.bind
                                 (Error_Monad.catch_error
                                   (Term_Rewriting.check_left_linear_trs rs)
                                   (\ x ->
                                     Sum_Type.Inl
                                       (Term_Rewriting.showsl_lit
  "RFC automaton-closed relative bounds currently require left-linear rules\n" .
 x)))
                                 (\ _ ->
                                   Error_Monad.bind
                                     (Matchbounds_Impl.bounds_condition typea
                                       rs)
                                     (\ _ ->
                                       Error_Monad.bind
 (Matchbounds_Impl.check_ta_bounded ta c)
 (\ _ ->
   Error_Monad.bind
     (Check_Monad.check
       (any (\ q ->
              RBTSetImpl.memb_rm_basic_ops q
                (Tree_Automata_Impl.ta_rhs_states_set ta))
         qfin)
       (Term_Rewriting.showsl_lit "did not find mentioned final state in TA"))
     (\ _ ->
       Error_Monad.bind
         (Error_Monad.catch_error
           (Tree_Automata_Impl.state_compatible_eff_list ta rell
             (rfc_strict_below_bound_list
               (\ l ->
                 not (Tree_Automata_Impl.rule_state_compatible_heuristic ta l))
               (Matchbounds_Impl.boundstype_fun typea) c r))
           (\ x ->
             Sum_Type.Inl
               (case x of {
                 (lr, (lr_rhs, q)) ->
                   ((((((Term_Rewriting.showsl_lit
                           "TA is not compatible with below-top strict RFC TRS\n" .
                          Term_Rewriting.showsl_lit "for rule ") .
                         Term_Rewriting.showsl_rule lr) .
                        Term_Rewriting.showsl_lit
                          "\nwhich is instantiated by states to ") .
                       Term_Rewriting.showsl_rule lr_rhs) .
                      Term_Rewriting.showsl_lit "\nthe state ") .
                     Term_Rewriting.showsl_integer q) .
                     Term_Rewriting.showsl_lit
                       " is only reachable from the lhs\n";
               })))
         (\ _ ->
           Error_Monad.catch_error
             (Tree_Automata_Impl.state_compatible_eff_list ta rell
               (Matchbounds_Impl.cover_bound_list_filter
                 (\ l ->
                   not (Tree_Automata_Impl.rule_state_compatible_heuristic ta
                         l))
                 Matchbounds.match (Matchbounds.Weak_TRS c_opt) c s))
             (\ x ->
               Sum_Type.Inl
                 (case x of {
                   (lr, (lr_rhs, q)) ->
                     ((((((Term_Rewriting.showsl_lit
                             "TA is not compatible with relative RFC TRS\n" .
                            Term_Rewriting.showsl_lit "for rule ") .
                           Term_Rewriting.showsl_rule lr) .
                          Term_Rewriting.showsl_lit
                            "\nwhich is instantiated by states to ") .
                         Term_Rewriting.showsl_rule lr_rhs) .
                        Term_Rewriting.showsl_lit "\nthe state ") .
                       Term_Rewriting.showsl_integer q) .
                       Term_Rewriting.showsl_lit
                         " is only reachable from the lhs\n";
                 })))))))))))
        (\ x ->
          Sum_Type.Inl
            (((Term_Rewriting.showsl_lit
                 "problem during checking RFC-relative local bounds conditions of automaton\n" .
                Matchbounds_Impl.get_renaming_info ren) .
               Term_Rewriting.showsl_lit "\nerror:\n") .
              x));
  });

rfc_rule_matchbox_closed_indexed_impl ::
  forall a b.
    (Compare.Compare_order a, Eq a,
      Compare.Compare_order b) => Tree_Automata_Impl.Ta_impl a (b, Arith.Nat) ->
                                    Tree_Automata_Impl.Ta_relation a ->
                                      [a] ->
(Term_Rewriting.Term b [Arith.Char], Term_Rewriting.Term b [Arith.Char]) ->
  Bool;
rfc_rule_matchbox_closed_indexed_impl ta rel qs lr =
  (case rfc_rule_words lr of {
    Nothing -> False;
    Just (lw, rw) ->
      Arith.list_all2
        (\ lhs rhs ->
          Arith.is_none (Tree_Automata_Impl.rel_checker rel lhs rhs))
        (rfc_word_results_impl (Tree_Automata_Impl.ta_rules_impl ta)
          (Tree_Automata_Impl.ta_epss_impl ta) Arith.zero_nat lw qs)
        (rfc_word_results_impl (Tree_Automata_Impl.ta_rules_impl ta)
          (Tree_Automata_Impl.ta_epss_impl ta) Arith.zero_nat rw qs);
  });

rfc_matchbox_closed_indexed_impl ::
  forall a b.
    (Compare.Compare_order a, Eq a,
      Compare.Compare_order b) => Tree_Automata_Impl.Ta_impl a (b, Arith.Nat) ->
                                    Tree_Automata_Impl.Ta_relation a ->
                                      [a] ->
[(Term_Rewriting.Term b [Arith.Char], Term_Rewriting.Term b [Arith.Char])] ->
  Bool;
rfc_matchbox_closed_indexed_impl ta rel qs r =
  all (rfc_rule_matchbox_closed_indexed_impl ta rel qs) r;

rfc_initial_paired_accepted_impl ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare_order b) => HOL.Itself a ->
                                    Tree_Automata_Impl.Ta_impl b
                                      (a, Arith.Nat) ->
                                      [b] ->
[Term_Rewriting.Term a [Arith.Char]] -> Bool;
rfc_initial_paired_accepted_impl uu ta tails i =
  Arith.equal_nat (Arith.size_list tails) (Arith.size_list i) &&
    all (\ (t, q) -> rfc_term_accepted_with_tail_states_impl HOL.Type ta [q] t)
      (zip i tails);

rfc_matchbox_relative_bounds_tt ::
  forall a b c.
    (Compare.Compare_order b, Eq b, Term_Rewriting.Showl b, Arith.Ccompare c,
      Compare.Compare_order c, Eq c, Mapping.Mapping_impl c,
      Term_Rewriting.Showl c) => Termination_Problem_Spec.Tp_ops_ext a b
                                   [Arith.Char] () ->
                                   Matchbounds_Impl.Bounds_info b c ->
                                     [Term_Rewriting.Term b [Arith.Char]] ->
                                       [(Term_Rewriting.Term b [Arith.Char],
  Term_Rewriting.Term b [Arith.Char])] ->
 a -> Sum_Type.Sum (String -> String) a;
rfc_matchbox_relative_bounds_tt i info initial_terms rdelete tp =
  (case Matchbounds_Impl.get_integer_bounds_info info of {
    (Matchbounds_Impl.Bounds_Info _ c qfin preTA rel, _) ->
      Error_Monad.bind (Tree_Automata_Impl.generate_ta_cond preTA rel)
        (\ ta ->
          let {
            states =
              Arith.remdups
                (Matchbounds_Impl.states_of_tree_automata_dup preTA);
            rstrict = Termination_Problem_Spec.r i tp;
            rkeep = Map_Choice.ceta_list_diff rstrict rdelete;
          } in Error_Monad.bind
                 (Check_Monad.check (Termination_Problem_Spec.q_empty i tp)
                   (Term_Rewriting.showsl_lit
                     "RFC Matchbox-relative bounds currently require an empty Q component"))
                 (\ _ ->
                   Error_Monad.bind
                     (Check_Monad.check
                       (null (Termination_Problem_Spec.rw i tp))
                       (Term_Rewriting.showsl_lit
                         "RFC Matchbox-relative bounds currently require no weak rules"))
                     (\ _ ->
                       Error_Monad.bind
                         (Check_Monad.check
                           (not (Termination_Problem_Spec.nfs i tp))
                           (Term_Rewriting.showsl_lit
                             "RFC Matchbox-relative bounds currently certify full rewriting, not innermost rewriting"))
                         (\ _ ->
                           Error_Monad.bind
                             (Error_Monad.catch_error
                               (Check_Monad.check_subseteq rdelete rstrict)
                               (\ x ->
                                 Sum_Type.Inl
                                   ((Term_Rewriting.showsl_lit
                                       "could not find removed rule " .
                                      Term_Rewriting.showsl_rule x) .
                                     Term_Rewriting.showsl_lit
                                       " among current strict rules")))
                             (\ _ ->
                               Error_Monad.bind
                                 (Check_Monad.check
                                   (Matchbounds_Impl.equal_boundstype
                                     (Matchbounds_Impl.boundstype info)
                                     Matchbounds_Impl.Match)
                                   (Term_Rewriting.showsl_lit
                                     "RFC Matchbox-relative bounds require boundstype match"))
                                 (\ _ ->
                                   Error_Monad.bind
                                     (Term_Rewriting.check_wf_trs rstrict)
                                     (\ _ ->
                                       Error_Monad.bind
 (Check_Monad.check (all (\ (_, a) -> Term_Rewriting.linear_term a) rstrict)
   (Term_Rewriting.showsl_lit
     "RFC Matchbox-relative bounds require right-linear rules"))
 (\ _ ->
   Error_Monad.bind
     (Check_Monad.check (rfc_initial_single_var initial_terms)
       (Term_Rewriting.showsl_lit
         "RFC Matchbox-relative initial language templates must contain at most one variable"))
     (\ _ ->
       Error_Monad.bind
         (Check_Monad.check (rfc_initial_covers rstrict initial_terms)
           (Term_Rewriting.showsl_lit
             "RFC Matchbox-relative initial language does not cover all right-hand sides"))
         (\ _ ->
           Error_Monad.bind
             (Check_Monad.check
               (all (\ q ->
                      RBTSetImpl.memb_rm_basic_ops q
                        (Tree_Automata_Impl.ta_rhs_states_set ta))
                 qfin)
               (Term_Rewriting.showsl_lit
                 "RFC Matchbox-relative tail states must occur as automaton right-hand-side states"))
             (\ _ ->
               Error_Monad.bind
                 (Check_Monad.check
                   (rfc_initial_paired_accepted_impl HOL.Type ta qfin
                     initial_terms)
                   (Term_Rewriting.showsl_lit
                     "RFC Matchbox-relative right-hand sides are not accepted by their paired tail states"))
                 (\ _ ->
                   Error_Monad.bind
                     (Check_Monad.check
                       (rfc_matchbox_closed_indexed_impl ta rel states rstrict)
                       (Term_Rewriting.showsl_lit
                         "RFC Matchbox-relative merge/epsilon split condition failed"))
                     (\ _ ->
                       Error_Monad.bind
                         (Check_Monad.check
                           (rfc_matchbox_ext_right_indexed_impl ta rel qfin
                             states rstrict)
                           (Term_Rewriting.showsl_lit
                             "RFC Matchbox-relative right-extension condition failed"))
                         (\ _ ->
                           Error_Monad.bind
                             (Check_Monad.check
                               (rfc_no_top_redex_indexed_impl ta states c
                                 rdelete)
                               (Term_Rewriting.showsl_lit
                                 "RFC Matchbox-relative removed rules have a redex at the top match-bound layer"))
                             (\ _ ->
                               Error_Monad.bind
                                 (check_bounds_generic_rfc_relative info rdelete
                                   rkeep)
                                 (\ _ ->
                                   Sum_Type.Inr
                                     (Termination_Problem_Spec.mk i
                                       (Termination_Problem_Spec.nfs i tp)
                                       (Termination_Problem_Spec.q i tp) rkeep
                                       rdelete)))))))))))))))));
  });

rfc_rule_native_matchbox_closed_impl ::
  forall a b.
    (Compare.Compare_order a, Eq a,
      Compare.Compare_order b) => Tree_Automata_Impl.Ta_impl a (b, Arith.Nat) ->
                                    Tree_Automata_Impl.Ta_relation a ->
                                      [a] ->
(Term_Rewriting.Term b [Arith.Char], Term_Rewriting.Term b [Arith.Char]) ->
  Bool;
rfc_rule_native_matchbox_closed_impl ta rel qs lr =
  (case rfc_rule_words lr of {
    Nothing -> False;
    Just (lw, rw) ->
      all (\ q ->
            Arith.is_none
              (Tree_Automata_Impl.rel_checker rel
                (rfc_native_word_res_impl (Tree_Automata_Impl.ta_rules_impl ta)
                  (Tree_Automata_Impl.ta_epss_impl ta) q Arith.zero_nat lw)
                (rfc_native_word_res_impl (Tree_Automata_Impl.ta_rules_impl ta)
                  (Tree_Automata_Impl.ta_epss_impl ta) q Arith.zero_nat rw)))
        qs;
  });

rfc_native_matchbox_closed_impl ::
  forall a b.
    (Compare.Compare_order a, Eq a,
      Compare.Compare_order b) => Tree_Automata_Impl.Ta_impl a (b, Arith.Nat) ->
                                    Tree_Automata_Impl.Ta_relation a ->
                                      [a] ->
[(Term_Rewriting.Term b [Arith.Char], Term_Rewriting.Term b [Arith.Char])] ->
  Bool;
rfc_native_matchbox_closed_impl ta rel qs r =
  all (rfc_rule_native_matchbox_closed_impl ta rel qs) r;

rfc_tail_states_eps_closed_impl ::
  forall a b.
    (Compare.Compare_order a,
      Quasi_Order.Linorder b) => Tree_Automata_Impl.Ta_impl a b -> [a] -> Bool;
rfc_tail_states_eps_closed_impl ta tails =
  let {
    qset = RBTSetImpl.g_from_list_dflt_basic_oops_rm_basic_ops tails;
  } in all (\ q ->
             all (\ p -> RBTSetImpl.memb_rm_basic_ops p qset)
               (RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops
                 (Tree_Automata_Impl.ta_epss_impl ta q)))
         tails;

rfc_rule_native_matchbox_ext_right_impl ::
  forall a b.
    (Compare.Compare_order a, Eq a,
      Compare.Compare_order b) => Tree_Automata_Impl.Ta_impl a (b, Arith.Nat) ->
                                    Tree_Automata_Impl.Ta_relation a ->
                                      [a] ->
(Term_Rewriting.Term b [Arith.Char], Term_Rewriting.Term b [Arith.Char]) ->
  Bool;
rfc_rule_native_matchbox_ext_right_impl ta rel tails lr =
  (case rfc_rule_words lr of {
    Nothing -> False;
    Just (lw, rw) ->
      not (null lw) &&
        all (\ q ->
              let {
                rhs = rfc_native_word_res_impl
                        (Tree_Automata_Impl.ta_rules_impl ta)
                        (Tree_Automata_Impl.ta_epss_impl ta) q Arith.zero_nat
                        rw;
              } in all (\ i ->
                         Arith.is_none
                           (Tree_Automata_Impl.rel_checker rel
                             (rfc_native_word_res_impl
                               (Tree_Automata_Impl.ta_rules_impl ta)
                               (Tree_Automata_Impl.ta_epss_impl ta) q
                               Arith.zero_nat (Arith.take i lw))
                             rhs))
                     (Arith.upt Arith.one_nat (Arith.size_list lw)))
          tails;
  });

rfc_native_matchbox_ext_right_impl ::
  forall a b.
    (Compare.Compare_order a, Eq a,
      Compare.Compare_order b) => Tree_Automata_Impl.Ta_impl a (b, Arith.Nat) ->
                                    Tree_Automata_Impl.Ta_relation a ->
                                      [a] ->
[(Term_Rewriting.Term b [Arith.Char], Term_Rewriting.Term b [Arith.Char])] ->
  Bool;
rfc_native_matchbox_ext_right_impl ta rel tails r =
  all (rfc_rule_native_matchbox_ext_right_impl ta rel tails) r;

rfc_automaton_closed_relative_bounds_tt ::
  forall a b c.
    (Compare.Compare_order b, Eq b, Term_Rewriting.Showl b, Arith.Ccompare c,
      Eq c, Mapping.Mapping_impl c, Quasi_Order.Linorder c,
      Term_Rewriting.Showl c) => Termination_Problem_Spec.Tp_ops_ext a b
                                   [Arith.Char] () ->
                                   Matchbounds_Impl.Bounds_info b c ->
                                     [Term_Rewriting.Term b [Arith.Char]] ->
                                       [(Term_Rewriting.Term b [Arith.Char],
  Term_Rewriting.Term b [Arith.Char])] ->
 a -> Sum_Type.Sum (String -> String) a;
rfc_automaton_closed_relative_bounds_tt i info initial_terms rdelete tp =
  (case Matchbounds_Impl.get_integer_bounds_info info of {
    (Matchbounds_Impl.Bounds_Info _ c _ preTA rel, _) ->
      Error_Monad.bind (Tree_Automata_Impl.generate_ta_cond preTA rel)
        (\ ta ->
          let {
            states =
              Arith.remdups
                (Matchbounds_Impl.states_of_tree_automata_dup preTA);
            rstrict = Termination_Problem_Spec.r i tp;
            rkeep = Map_Choice.ceta_list_diff rstrict rdelete;
          } in Error_Monad.bind
                 (Check_Monad.check (Termination_Problem_Spec.q_empty i tp)
                   (Term_Rewriting.showsl_lit
                     "RFC automaton-closed relative bounds currently require an empty Q component"))
                 (\ _ ->
                   Error_Monad.bind
                     (Check_Monad.check
                       (null (Termination_Problem_Spec.rw i tp))
                       (Term_Rewriting.showsl_lit
                         "RFC automaton-closed relative bounds currently require no weak rules"))
                     (\ _ ->
                       Error_Monad.bind
                         (Check_Monad.check
                           (not (Termination_Problem_Spec.nfs i tp))
                           (Term_Rewriting.showsl_lit
                             "RFC automaton-closed relative bounds currently certify full rewriting, not innermost rewriting"))
                         (\ _ ->
                           Error_Monad.bind
                             (Error_Monad.catch_error
                               (Check_Monad.check_subseteq rdelete rstrict)
                               (\ x ->
                                 Sum_Type.Inl
                                   ((Term_Rewriting.showsl_lit
                                       "could not find removed rule " .
                                      Term_Rewriting.showsl_rule x) .
                                     Term_Rewriting.showsl_lit
                                       " among current strict rules")))
                             (\ _ ->
                               Error_Monad.bind
                                 (Check_Monad.check
                                   (Matchbounds_Impl.equal_boundstype
                                     (Matchbounds_Impl.boundstype info)
                                     Matchbounds_Impl.Match)
                                   (Term_Rewriting.showsl_lit
                                     "RFC automaton-closed relative bounds require boundstype match"))
                                 (\ _ ->
                                   Error_Monad.bind
                                     (Term_Rewriting.check_wf_trs rstrict)
                                     (\ _ ->
                                       Error_Monad.bind
 (Check_Monad.check (all (\ (_, a) -> Term_Rewriting.linear_term a) rstrict)
   (Term_Rewriting.showsl_lit
     "RFC automaton-closed relative bounds require right-linear rules"))
 (\ _ ->
   Error_Monad.bind
     (Check_Monad.check (rfc_initial_single_var initial_terms)
       (Term_Rewriting.showsl_lit
         "RFC automaton-closed relative initial language templates must contain at most one variable"))
     (\ _ ->
       Error_Monad.bind
         (Check_Monad.check (rfc_initial_covers rstrict initial_terms)
           (Term_Rewriting.showsl_lit
             "RFC automaton-closed relative initial language does not contain all right-hand sides"))
         (\ _ ->
           Error_Monad.bind
             (Check_Monad.check
               (rfc_initial_accepted_with_tail_states_impl HOL.Type ta states
                 initial_terms)
               (Term_Rewriting.showsl_lit
                 "RFC automaton-closed relative initial language is not accepted by the automaton for all automaton states"))
             (\ _ ->
               Error_Monad.bind
                 (Check_Monad.check
                   (rfc_automaton_closed_impl ta states rstrict)
                   (Term_Rewriting.showsl_lit
                     "RFC automaton-closed relative split condition failed"))
                 (\ _ ->
                   Error_Monad.bind
                     (Check_Monad.check
                       (rfc_lhs_suffix_total_impl ta states rstrict)
                       (Term_Rewriting.showsl_lit
                         "RFC automaton-closed relative lhs suffix totality condition failed"))
                     (\ _ ->
                       Error_Monad.bind
                         (Check_Monad.check
                           (rfc_no_top_redex_impl ta states c rdelete)
                           (Term_Rewriting.showsl_lit
                             "RFC automaton-closed relative removed rules have a redex at the top match-bound layer"))
                         (\ _ ->
                           Error_Monad.bind
                             (check_bounds_generic_rfc_relative info rdelete
                               rkeep)
                             (\ _ ->
                               Sum_Type.Inr
                                 (Termination_Problem_Spec.mk i
                                   (Termination_Problem_Spec.nfs i tp)
                                   (Termination_Problem_Spec.q i tp) rkeep
                                   rdelete))))))))))))))));
  });

rfc_native_rel_matchbox_relative_bounds_tt ::
  forall a b c.
    (Compare.Compare_order b, Eq b, Term_Rewriting.Showl b, Arith.Ccompare c,
      Compare.Compare_order c, Eq c, Mapping.Mapping_impl c,
      Term_Rewriting.Showl c) => Termination_Problem_Spec.Tp_ops_ext a b
                                   [Arith.Char] () ->
                                   Matchbounds_Impl.Bounds_info b c ->
                                     [Term_Rewriting.Term b [Arith.Char]] ->
                                       [(Term_Rewriting.Term b [Arith.Char],
  Term_Rewriting.Term b [Arith.Char])] ->
 a -> Sum_Type.Sum (String -> String) a;
rfc_native_rel_matchbox_relative_bounds_tt i info initial_terms rdelete tp =
  (case Matchbounds_Impl.get_integer_bounds_info info of {
    (Matchbounds_Impl.Bounds_Info _ c qfin preTA rel, _) ->
      Error_Monad.bind (Tree_Automata_Impl.generate_ta_cond preTA rel)
        (\ ta ->
          let {
            states =
              Arith.remdups
                (Matchbounds_Impl.states_of_tree_automata_dup preTA);
            rstrict = Termination_Problem_Spec.r i tp;
            rkeep = Map_Choice.ceta_list_diff rstrict rdelete;
          } in Error_Monad.bind
                 (Check_Monad.check (Termination_Problem_Spec.q_empty i tp)
                   (Term_Rewriting.showsl_lit
                     "native relational RFC bounds require an empty Q component"))
                 (\ _ ->
                   Error_Monad.bind
                     (Check_Monad.check
                       (null (Termination_Problem_Spec.rw i tp))
                       (Term_Rewriting.showsl_lit
                         "native relational RFC bounds require no weak rules"))
                     (\ _ ->
                       Error_Monad.bind
                         (Check_Monad.check
                           (not (Termination_Problem_Spec.nfs i tp))
                           (Term_Rewriting.showsl_lit
                             "native relational RFC bounds certify full rewriting"))
                         (\ _ ->
                           Error_Monad.bind
                             (Error_Monad.catch_error
                               (Check_Monad.check_subseteq rdelete rstrict)
                               (\ x ->
                                 Sum_Type.Inl
                                   (Term_Rewriting.showsl_lit
                                      "could not find removed rule " .
                                     Term_Rewriting.showsl_rule x)))
                             (\ _ ->
                               Error_Monad.bind
                                 (Check_Monad.check
                                   (Matchbounds_Impl.equal_boundstype
                                     (Matchbounds_Impl.boundstype info)
                                     Matchbounds_Impl.Match)
                                   (Term_Rewriting.showsl_lit
                                     "native relational RFC bounds require boundstype match"))
                                 (\ _ ->
                                   Error_Monad.bind
                                     (Term_Rewriting.check_wf_trs rstrict)
                                     (\ _ ->
                                       Error_Monad.bind
 (Check_Monad.check (all (\ (_, a) -> Term_Rewriting.linear_term a) rstrict)
   (Term_Rewriting.showsl_lit
     "native relational RFC bounds require right-linear rules"))
 (\ _ ->
   Error_Monad.bind
     (Check_Monad.check (rfc_initial_single_var initial_terms)
       (Term_Rewriting.showsl_lit
         "native relational RFC initial templates contain too many variables"))
     (\ _ ->
       Error_Monad.bind
         (Check_Monad.check (rfc_initial_covers rstrict initial_terms)
           (Term_Rewriting.showsl_lit
             "native relational RFC initial language misses a right-hand side"))
         (\ _ ->
           Error_Monad.bind
             (Check_Monad.check
               (all (\ q ->
                      RBTSetImpl.memb_rm_basic_ops q
                        (Tree_Automata_Impl.ta_rhs_states_set ta))
                 qfin)
               (Term_Rewriting.showsl_lit
                 "native relational RFC tail state is not a right-hand-side state"))
             (\ _ ->
               Error_Monad.bind
                 (Check_Monad.check
                   (rfc_initial_paired_accepted_impl HOL.Type ta qfin
                     initial_terms)
                   (Term_Rewriting.showsl_lit
                     "native relational RFC initial language is not accepted"))
                 (\ _ ->
                   Error_Monad.bind
                     (Check_Monad.check
                       (rfc_native_matchbox_closed_impl ta rel states rstrict)
                       (Term_Rewriting.showsl_lit
                         "native relational RFC merge closure failed"))
                     (\ _ ->
                       Error_Monad.bind
                         (Check_Monad.check
                           (rfc_tail_states_eps_closed_impl ta qfin)
                           (Term_Rewriting.showsl_lit
                             "native relational RFC tail states are not epsilon-closed"))
                         (\ _ ->
                           Error_Monad.bind
                             (Check_Monad.check
                               (rfc_native_matchbox_ext_right_impl ta rel qfin
                                 rstrict)
                               (Term_Rewriting.showsl_lit
                                 "native relational RFC right-extension closure failed"))
                             (\ _ ->
                               Error_Monad.bind
                                 (Check_Monad.check
                                   (rfc_no_top_redex_indexed_impl ta states c
                                     rdelete)
                                   (Term_Rewriting.showsl_lit
                                     "native relational RFC removed rule has a top-layer redex"))
                                 (\ _ ->
                                   Error_Monad.bind
                                     (check_bounds_generic_rfc_relative info
                                       rdelete rkeep)
                                     (\ _ ->
                                       Sum_Type.Inr
 (Termination_Problem_Spec.mk i (Termination_Problem_Spec.nfs i tp)
   (Termination_Problem_Spec.q i tp) rkeep rdelete))))))))))))))))));
  });

}
