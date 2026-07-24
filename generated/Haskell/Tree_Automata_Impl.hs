{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Tree_Automata_Impl(showsl_ta_rule, Ta_rule_impl, Ta_impl, Ta_relation(..),
                      Tree_automaton(..), ta_of_ta, check_det, rqss_impl,
                      r_rhs_impl, rel_checker, r_lhs_states_impl, ta_res_impl,
                      generate_ta_cond, ta_rhs_states_set, ta_rules_impl,
                      ta_epss_impl, state_compatible_eff_list,
                      tree_aut_trs_closed, non_join_with_ta, ta_final_impl,
                      ta_contains_impl, ta_rules_impla,
                      rule_state_compatible_heuristic, equal_ta_relation)
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
import qualified Util;
import qualified Tree_Automata_Wit_Impl;
import qualified Transitive_Closure;
import qualified Relation;
import qualified Missing_List;
import qualified Product_Lexorder;
import qualified Tree_Automata_Det;
import qualified List_Lexorder;
import qualified Quasi_Order;
import qualified RBTSetImpl;
import qualified Transitive_Closure_RBT_Impl;
import qualified RBT_Map_Set_Extension;
import qualified HOL;
import qualified Compare;
import qualified Compare_Order_Instances;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified RBT;
import qualified Arith;
import qualified Term_Rewriting;

showsl_ta_rule ::
  forall a b.
    (Term_Rewriting.Showl a,
      Term_Rewriting.Showl b) => Term_Rewriting.Ta_rule a b -> String -> String;
showsl_ta_rule (Term_Rewriting.TA_rule f qs q) =
  ((Term_Rewriting.showsl f . Term_Rewriting.showsl_list qs) .
    Term_Rewriting.showsl_lit " -> ") .
    Term_Rewriting.showsl q;

showsl_list_ta_rule ::
  forall a b.
    (Term_Rewriting.Showl a,
      Term_Rewriting.Showl b) => [Term_Rewriting.Ta_rule a b] ->
                                   String -> String;
showsl_list_ta_rule xs = Term_Rewriting.default_showsl_list showsl_ta_rule xs;

instance (Term_Rewriting.Showl a,
           Term_Rewriting.Showl b) => Term_Rewriting.Showl (Term_Rewriting.Ta_rule
                     a b) where {
  showsl = showsl_ta_rule;
  showsl_list = showsl_list_ta_rule;
};

data Ta_rule_impl a b = TA_rule_impl b [a] a (RBT.Rbt a ());

data Ta_impl a b =
  TA_Impl (RBT.Rbt a ()) (RBT.Rbt (b, Arith.Nat) [Ta_rule_impl a b]) [a]
    (RBT.Rbt a ()) [(a, a)] (a -> RBT.Rbt a ()) (a -> RBT.Rbt a ());

data Ta_relation a = Decision_Proc_Old | Decision_Proc | Id_Relation
  | Some_Relation [(a, a)];

data Tree_automaton a b =
  Tree_Automaton [a] [Term_Rewriting.Ta_rule a b] [(a, a)];

ta_of_ta ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Eq a, Arith.Set_impl a, Arith.Ccompare b,
      Eq b) => Tree_automaton a b -> Term_Rewriting.Ta_ext a b ();
ta_of_ta (Tree_Automaton fin rules eps) =
  Term_Rewriting.Ta_ext (Arith.set fin) (Arith.set rules) (Arith.set eps) ();

check_det ::
  forall a b.
    (Eq a, Eq b) => Tree_automaton a b -> Sum_Type.Sum (String -> String) ();
check_det (Tree_Automaton fin rules eps) =
  Error_Monad.catch_error
    (Error_Monad.bind
      (Check_Monad.check (null eps)
        (Term_Rewriting.showsl_lit "epsilon transitions not allowed"))
      (\ _ ->
        Check_Monad.check
          (Arith.distinct
            (map (\ (Term_Rewriting.TA_rule f qs _) -> (f, qs))
              (Arith.remdups rules)))
          (Term_Rewriting.showsl_lit "some lhs occurs twice")))
    (\ x ->
      Sum_Type.Inl
        (Term_Rewriting.showsl_lit
           "problem when ensuring determinism of automata\n" .
          x));

rqss_impl :: forall a b. Ta_rule_impl a b -> RBT.Rbt a ();
rqss_impl (TA_rule_impl f qsa q qs) = qs;

r_rhs_impl :: forall a b. Ta_rule_impl a b -> a;
r_rhs_impl (TA_rule_impl f qsa q qs) = q;

r_sym_impl :: forall a b. Ta_rule_impl a b -> (b, Arith.Nat);
r_sym_impl (TA_rule_impl f qsa q qs) = (f, Arith.size_list qsa);

conv_ta_rule ::
  forall a b.
    (a -> RBT.Rbt a ()) -> Term_Rewriting.Ta_rule a b -> Ta_rule_impl a b;
conv_ta_rule eps (Term_Rewriting.TA_rule f qs q) = TA_rule_impl f qs q (eps q);

generate_ta ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare_order b) => Tree_automaton a b -> Ta_impl a b;
generate_ta (Tree_Automaton fin rules eps) =
  let {
    ep = Transitive_Closure_RBT_Impl.memo_rbt_rtrancl eps;
    epr = Transitive_Closure_RBT_Impl.memo_rbt_rtrancl
            (map (\ (q, qa) -> (qa, q)) eps);
    rqs_rs =
      RBT_Map_Set_Extension.rs_Union
        (map (\ rule -> ep (Term_Rewriting.r_rhs rule)) rules);
    rrules = map (conv_ta_rule ep) rules;
  } in TA_Impl (RBTSetImpl.g_from_list_dflt_basic_oops_rm_basic_ops fin)
         (RBT_Map_Set_Extension.elem_list_to_rm r_sym_impl rrules)
         (RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops rqs_rs) rqs_rs eps
         ep epr;

rel_checker ::
  forall a.
    (Eq a,
      Quasi_Order.Linorder a) => Ta_relation a ->
                                   RBT.Rbt a () -> RBT.Rbt a () -> Maybe a;
rel_checker (Some_Relation rel) =
  (\ lhs rhs ->
    let {
      rlist = RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops rhs;
    } in (case Error_Monad.catch_error
                 (Error_Monad.forallM
                   (\ l ->
                     Check_Monad.check
                       (any (\ r -> Arith.membera rel (l, r)) rlist) l)
                   (RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops lhs))
                 (\ x -> Sum_Type.Inl (snd x))
           of {
           Sum_Type.Inl a -> Just a;
           Sum_Type.Inr _ -> Nothing;
         }));
rel_checker Id_Relation = RBT_Map_Set_Extension.rs_subset;
rel_checker Decision_Proc = RBT_Map_Set_Extension.rs_subset;
rel_checker Decision_Proc_Old = RBT_Map_Set_Extension.rs_subset;

r_lhs_states_impl :: forall a b. Ta_rule_impl a b -> [a];
r_lhs_states_impl (TA_rule_impl f qsa q qs) = qsa;

ta_res_impl ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare_order b) => RBT.Rbt (a, Arith.Nat) [Ta_rule_impl b a] ->
                                    (b -> RBT.Rbt b ()) ->
                                      Term_Rewriting.Term a b -> RBT.Rbt b ();
ta_res_impl ta eps (Term_Rewriting.Var q) = eps q;
ta_res_impl ta eps (Term_Rewriting.Fun f ts) =
  let {
    rec = map (ta_res_impl ta eps) ts;
    n = Arith.size_list ts;
    rules = RBT_Map_Set_Extension.rm_set_lookup ta (f, n);
    arules =
      filter
        (\ rule ->
          let {
            qs = r_lhs_states_impl rule;
          } in all (\ i ->
                     RBTSetImpl.memb_rm_basic_ops (Arith.nth qs i)
                       (Arith.nth rec i))
                 (Arith.upt Arith.zero_nat n))
        rules;
    a = map rqss_impl arules;
  } in RBT_Map_Set_Extension.rs_Union a;

sorted_ps_ta ::
  forall a b.
    (Arith.Card_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Compare.Compare a, Eq a, Quasi_Order.Linorder a, Arith.Set_impl a,
      Arith.Ceq b, Arith.Ccompare b, Compare.Compare b, Eq b,
      Arith.Set_impl b) => Term_Rewriting.Ta_ext a b () -> Tree_automaton [a] b;
sorted_ps_ta ta =
  Tree_Automaton
    (Arith.sorted_list_of_set
      (Arith.image Arith.sorted_list_of_set
        (Term_Rewriting.ta_final (Tree_Automata_Det.ps_ta ta))))
    (Arith.sorted_list_of_set
      (Arith.image
        (\ (Term_Rewriting.TA_rule g qs q) ->
          Term_Rewriting.TA_rule g (map Arith.sorted_list_of_set qs)
            (Arith.sorted_list_of_set q))
        (Term_Rewriting.ta_rules (Tree_Automata_Det.ps_ta ta))))
    [];

ta_match_impl ::
  forall a b c.
    (Compare.Compare_order a, Compare.Compare_order b, Eq b,
      Compare.Compare_order c,
      Eq c) => RBT.Rbt (a, Arith.Nat) [Ta_rule_impl b a] ->
                 RBT.Rbt b () ->
                   (b -> RBT.Rbt b ()) ->
                     Term_Rewriting.Term a c -> [b] -> RBT.Rbt [(c, b)] ();
ta_match_impl ta qsig eps (Term_Rewriting.Var x) q =
  RBTSetImpl.g_from_list_dflt_basic_oops_rm_basic_ops
    (map (\ qa -> [(x, qa)])
      (RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops
        (RBTSetImpl.g_inter_dflt_basic_oops_rm_basic_ops
          (RBT_Map_Set_Extension.rs_Union (map eps q)) qsig)));
ta_match_impl ta qsig eps (Term_Rewriting.Fun f ts) q =
  let {
    n = Arith.size_list ts;
    rules = RBT_Map_Set_Extension.rm_set_lookup ta (f, n);
    ep = RBT_Map_Set_Extension.rs_Union (map eps q);
    fa = (\ rule ->
           RBTSetImpl.g_from_list_dflt_basic_oops_rm_basic_ops
             (case rule of {
               TA_rule_impl _ qs qa _ ->
                 (if RBTSetImpl.memb_rm_basic_ops qa ep
                   then let {
                          rec = map (\ (tsi, qsi) ->
                                      RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops
(ta_match_impl ta qsig eps tsi [qsi]))
                                  (zip ts qs);
                        } in map concat (Missing_List.concat_lists rec)
                   else []);
             }));
  } in RBT_Map_Set_Extension.rs_Union (map fa rules);

check_coherent_rule ::
  forall a b.
    (Compare.Compare_order a, Eq a, Term_Rewriting.Showl a, Eq b,
      Term_Rewriting.Showl b) => (a -> [a]) ->
                                   RBT.Rbt (a, a) () ->
                                     [Term_Rewriting.Ta_rule a b] ->
                                       Term_Rewriting.Ta_rule a b ->
 Sum_Type.Sum (String -> String) ();
check_coherent_rule iter rel rules (Term_Rewriting.TA_rule f qs q) =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ i ->
        let {
          qi = Arith.nth qs i;
        } in Error_Monad.catch_error
               (Error_Monad.forallM
                 (\ qia ->
                   let {
                     qsa = Arith.list_update qs i qia;
                   } in Check_Monad.check
                          (not (null (filter
                                       (\ (Term_Rewriting.TA_rule g qsb qa) ->
 f == g && qsa == qsb && RBTSetImpl.memb_rm_basic_ops (q, qa) rel)
                                       rules)))
                          ((((((((((Term_Rewriting.showsl_lit "rule " .
                                     Term_Rewriting.showsl f) .
                                    Term_Rewriting.showsl_lit "(") .
                                   Term_Rewriting.showsl_list qs) .
                                  Term_Rewriting.showsl_lit ") -> ") .
                                 Term_Rewriting.showsl q) .
                                Term_Rewriting.showsl_lit " with ") .
                               Term_Rewriting.showsl_nat (Arith.suc i)) .
                              Term_Rewriting.showsl_lit
                                ". argument decreased to ") .
                             Term_Rewriting.showsl qia) .
                            Term_Rewriting.showsl_lit " has no counterpart"))
                 (iter qi))
               (\ x -> Sum_Type.Inl (snd x)))
      (Arith.upt Arith.zero_nat (Arith.size_list qs)))
    (\ x -> Sum_Type.Inl (snd x));

check_coherent ::
  forall a b.
    (Arith.Card_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a,
      Compare.Compare_order a, Eq a, Arith.Set_impl a, Term_Rewriting.Showl a,
      Eq b,
      Term_Rewriting.Showl b) => Tree_automaton a b ->
                                   Ta_relation a ->
                                     Sum_Type.Sum (String -> String) ();
check_coherent (Tree_Automaton fin rules eps) (Some_Relation rel) =
  let {
    iter =
      (\ q ->
        Arith.map_filter
          (\ x -> (if (case x of {
                        (a, _) -> a == q;
                      })
                    then Just (snd x) else Nothing))
          rel);
    rs = RBTSetImpl.g_from_list_dflt_basic_oops_rm_basic_ops rel;
    ep = Arith.set eps;
    rell = Relation.converse (Arith.set rel);
  } in Error_Monad.bind
         (Error_Monad.catch_error
           (Check_Monad.check_subseteq (concatMap iter fin) fin)
           (\ x ->
             Sum_Type.Inl
               (Term_Rewriting.showsl x .
                 Term_Rewriting.showsl_lit
                   " is in relation to a final state, but not a final state itself")))
         (\ _ ->
           Error_Monad.bind
             (Error_Monad.catch_error
               (Error_Monad.forallM (check_coherent_rule iter rs rules) rules)
               (\ x -> Sum_Type.Inl (snd x)))
             (\ _ ->
               Check_Monad.check
                 (Arith.less_eq_set (Relation.relcomp rell ep)
                   (Arith.sup_set
                     (Relation.relcomp (Transitive_Closure.trancl ep) rell)
                     rell))
                 (Term_Rewriting.showsl_lit
                   "problem in coherence of epsilon rules")));
check_coherent uu Decision_Proc_Old = Sum_Type.Inr ();
check_coherent uu Decision_Proc = Sum_Type.Inr ();
check_coherent uu Id_Relation = Sum_Type.Inr ();

ta_match_impla ::
  forall a b c.
    (Compare.Compare_order a, Compare.Compare_order b, Eq b,
      Compare.Compare_order c,
      Eq c) => RBT.Rbt (a, Arith.Nat) [Ta_rule_impl b a] ->
                 RBT.Rbt b () ->
                   (b -> RBT.Rbt b ()) ->
                     [b] -> Term_Rewriting.Term a c -> RBT.Rbt [(c, b)] ();
ta_match_impla ta qsig eps rhs t = ta_match_impl ta qsig eps t rhs;

ta_res_impl_all ::
  forall a b c.
    (Compare.Compare_order a,
      Compare.Compare_order b) => RBT.Rbt a () ->
                                    RBT.Rbt (b, Arith.Nat) [Ta_rule_impl a b] ->
                                      Term_Rewriting.Term b c -> RBT.Rbt a ();
ta_res_impl_all q ta (Term_Rewriting.Var uu) = q;
ta_res_impl_all q ta (Term_Rewriting.Fun f ts) =
  let {
    rec = map (ta_res_impl_all q ta) ts;
    n = Arith.size_list ts;
    rules = RBT_Map_Set_Extension.rm_set_lookup ta (f, n);
    arules =
      filter
        (\ rule ->
          let {
            qs = r_lhs_states_impl rule;
          } in all (\ i ->
                     RBTSetImpl.memb_rm_basic_ops (Arith.nth qs i)
                       (Arith.nth rec i))
                 (Arith.upt Arith.zero_nat n))
        rules;
    a = map rqss_impl arules;
  } in RBT_Map_Set_Extension.rs_Union a;

generate_ta_cond ::
  forall a b.
    (Arith.Card_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a,
      Compare.Compare_order a, Eq a, Arith.Set_impl a, Term_Rewriting.Showl a,
      Compare.Compare_order b, Eq b,
      Term_Rewriting.Showl b) => Tree_automaton a b ->
                                   Ta_relation a ->
                                     Sum_Type.Sum (String -> String)
                                       (Ta_impl a b);
generate_ta_cond ta rel =
  Error_Monad.bind
    (Error_Monad.catch_error (check_coherent ta rel)
      (\ x ->
        Sum_Type.Inl
          (Term_Rewriting.showsl_lit
             "automaton is not coherent w.r.t. relation\n" .
            x)))
    (\ _ -> Sum_Type.Inr (generate_ta ta));

showsl_tree_automaton ::
  forall a b.
    (Term_Rewriting.Showl a,
      Term_Rewriting.Showl b) => Tree_automaton a b -> String -> String;
showsl_tree_automaton (Tree_Automaton fin rules eps) =
  (((((Term_Rewriting.showsl_lit "final: " . Term_Rewriting.showsl_list fin) .
       Term_Rewriting.showsl_lit "\nrules: ") .
      Term_Rewriting.showsl_lines "empty" rules) .
     Term_Rewriting.showsl_lit "\nepsilon: ") .
    Term_Rewriting.showsl_list_prod eps) .
    Term_Rewriting.showsl_literal "\n";

ta_rhs_states_set :: forall a b. Ta_impl a b -> RBT.Rbt a ();
ta_rhs_states_set (TA_Impl x1 x2 x3 x4 x5 x6 x7) = x4;

ta_rules_impl ::
  forall a b. Ta_impl a b -> RBT.Rbt (b, Arith.Nat) [Ta_rule_impl a b];
ta_rules_impl (TA_Impl x1 x2 x3 x4 x5 x6 x7) = x2;

ta_epsrs_impl :: forall a b. Ta_impl a b -> a -> RBT.Rbt a ();
ta_epsrs_impl (TA_Impl x1 x2 x3 x4 x5 x6 x7) = x7;

ta_epss_impl :: forall a b. Ta_impl a b -> a -> RBT.Rbt a ();
ta_epss_impl (TA_Impl x1 x2 x3 x4 x5 x6 x7) = x6;

rule_state_compatible_eff_list ::
  forall a b c.
    (Compare.Compare_order a, Eq a, Compare.Compare_order b,
      Compare.Compare_order c,
      Eq c) => Ta_impl a b ->
                 (RBT.Rbt a () -> RBT.Rbt a () -> Maybe a) ->
                   (Term_Rewriting.Term b c, Term_Rewriting.Term b c) ->
                     Sum_Type.Sum
                       ((Term_Rewriting.Term b a, Term_Rewriting.Term b a), a)
                       ();
rule_state_compatible_eff_list ta rel =
  let {
    rm = ta_rules_impl ta;
    eps = ta_epss_impl ta;
    epsa = ta_epsrs_impl ta;
    ta_res = ta_res_impl rm eps;
    rhs_rbt = ta_rhs_states_set ta;
    rhs = RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops rhs_rbt;
  } in (\ (l, r) ->
         Error_Monad.catch_error
           (Error_Monad.forallM
             (\ sigma ->
               let {
                 sigmaa = Util.fun_of sigma;
                 l_sigma = Term_Rewriting.map_term (\ x -> x) sigmaa l;
                 r_sigma = Term_Rewriting.map_term (\ x -> x) sigmaa r;
                 qsl = ta_res l_sigma;
                 qsr = ta_res r_sigma;
               } in (case rel qsl qsr of {
                      Nothing -> Sum_Type.Inr ();
                      Just q -> Sum_Type.Inl ((l_sigma, r_sigma), q);
                    }))
             (RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops
               (ta_match_impla rm rhs_rbt epsa rhs l)))
           (\ x -> Sum_Type.Inl (snd x)));

state_compatible_eff_list ::
  forall a b c.
    (Compare.Compare_order a, Eq a, Compare.Compare_order b,
      Compare.Compare_order c,
      Eq c) => Ta_impl a b ->
                 (RBT.Rbt a () -> RBT.Rbt a () -> Maybe a) ->
                   [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
                     Sum_Type.Sum
                       ((Term_Rewriting.Term b c, Term_Rewriting.Term b c),
                         ((Term_Rewriting.Term b a, Term_Rewriting.Term b a),
                           a))
                       ();
state_compatible_eff_list ta rel r =
  let {
    check = rule_state_compatible_eff_list ta rel;
  } in Error_Monad.catch_error
         (Error_Monad.forallM
           (\ lr ->
             Error_Monad.catch_error (check lr) (\ x -> Sum_Type.Inl (lr, x)))
           r)
         (\ x -> Sum_Type.Inl (snd x));

ta_code_make_impl ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare_order b) => Tree_automaton a b ->
                                    Tree_Automata_Wit_Impl.Ta_code a b;
ta_code_make_impl (Tree_Automaton fin rs eps) =
  Tree_Automata_Wit_Impl.make_ls fin rs eps;

tree_aut_trs_closed ::
  forall a b c.
    (Arith.Card_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Compare.Compare_order a, Eq a, Arith.Set_impl a, Term_Rewriting.Showl a,
      Arith.Ceq b, Arith.Ccompare b, Compare.Compare_order b, HOL.Default b,
      Eq b, Arith.Set_impl b, Term_Rewriting.Showl b, Arith.Ceq c,
      Arith.Ccompare c, Compare.Compare_order c, Eq c, Arith.Set_impl c,
      Term_Rewriting.Showl c) => Tree_automaton a b ->
                                   Ta_relation a ->
                                     [(Term_Rewriting.Term b c,
Term_Rewriting.Term b c)] ->
                                       Sum_Type.Sum (String -> String) ();
tree_aut_trs_closed ta rel r =
  Error_Monad.bind (Term_Rewriting.check_varcond_subset r)
    (\ _ ->
      Error_Monad.catch_error
        (case rel of {
          Decision_Proc_Old ->
            Error_Monad.bind
              (Error_Monad.catch_error (check_det ta)
                (\ x ->
                  Sum_Type.Inl
                    (Term_Rewriting.showsl_lit
                       "decision procedure requires det. TA as input\n" .
                      x)))
              (\ _ ->
                Check_Monad.check
                  (Term_Rewriting.closed_under_rewriting (ta_of_ta ta)
                    (Arith.set r))
                  (Term_Rewriting.showsl_lit
                    "TA is not closed under rewriting"));
          Decision_Proc ->
            let {
              tc = ta_code_make_impl ta;
            } in (if Tree_Automata_Wit_Impl.det tc
                   then (case Tree_Automata_Wit_Impl.check_comcoh_wit_ls tc r of
                          {
                          Nothing -> Sum_Type.Inr ();
                          Just (wl, wr) ->
                            Sum_Type.Inl
                              ((((Term_Rewriting.showsl_lit
                                    "TA is not closed under rewriting\n" .
                                   Term_Rewriting.showsl_terma wl) .
                                  Term_Rewriting.showsl_lit
                                    " is accepted by TA and rewrites to\n") .
                                 Term_Rewriting.showsl_terma wr) .
                                Term_Rewriting.showsl_lit
                                  " which is not accepted by TA");
                        })
                   else let {
                          tca = ta_code_make_impl
                                  (sorted_ps_ta
                                    (Term_Rewriting.trim_ta (ta_of_ta ta)));
                        } in (case Tree_Automata_Wit_Impl.check_comcoh_wit_ls
                                     tca r
                               of {
                               Nothing -> Sum_Type.Inr ();
                               Just (wl, wr) ->
                                 Sum_Type.Inl
                                   ((((Term_Rewriting.showsl_lit
 "TA is not closed under rewriting\n" .
Term_Rewriting.showsl_terma wl) .
                                       Term_Rewriting.showsl_lit
 " is accepted by TA and rewrites to\n") .
                                      Term_Rewriting.showsl_terma wr) .
                                     Term_Rewriting.showsl_lit
                                       " which is not accepted by TA");
                             }));
          Id_Relation ->
            Error_Monad.bind (generate_ta_cond ta rel)
              (\ taa ->
                Error_Monad.bind
                  (Error_Monad.catch_error
                    (if Error_Monad.isOK
                          (Term_Rewriting.check_left_linear_trs r)
                      then Sum_Type.Inr () else check_det ta)
                    (\ x ->
                      Sum_Type.Inl
                        (Term_Rewriting.showsl_lit
                           "could not ensure left-linearity or determinism\n" .
                          x)))
                  (\ _ ->
                    Error_Monad.catch_error
                      (state_compatible_eff_list taa (rel_checker rel) r)
                      (\ x ->
                        Sum_Type.Inl
                          (case x of {
                            (lr, (lrq, q)) ->
                              ((((((Term_Rewriting.showsl_lit
                                      "TA is not compatible with R\n" .
                                     Term_Rewriting.showsl_lit "for rule ") .
                                    Term_Rewriting.showsl_rule lr) .
                                   Term_Rewriting.showsl_lit
                                     "\nwhich is instantiated by states to ") .
                                  Term_Rewriting.showsl_rule lrq) .
                                 Term_Rewriting.showsl_lit "\nthe state ") .
                                Term_Rewriting.showsl q) .
                                Term_Rewriting.showsl_lit
                                  " is only reachable from the lhs\n";
                          }))));
          Some_Relation _ ->
            Error_Monad.bind (generate_ta_cond ta rel)
              (\ taa ->
                Error_Monad.bind
                  (Error_Monad.catch_error
                    (if Error_Monad.isOK
                          (Term_Rewriting.check_left_linear_trs r)
                      then Sum_Type.Inr () else check_det ta)
                    (\ x ->
                      Sum_Type.Inl
                        (Term_Rewriting.showsl_lit
                           "could not ensure left-linearity or determinism\n" .
                          x)))
                  (\ _ ->
                    Error_Monad.catch_error
                      (state_compatible_eff_list taa (rel_checker rel) r)
                      (\ x ->
                        Sum_Type.Inl
                          (case x of {
                            (lr, (lrq, q)) ->
                              ((((((Term_Rewriting.showsl_lit
                                      "TA is not compatible with R\n" .
                                     Term_Rewriting.showsl_lit "for rule ") .
                                    Term_Rewriting.showsl_rule lr) .
                                   Term_Rewriting.showsl_lit
                                     "\nwhich is instantiated by states to ") .
                                  Term_Rewriting.showsl_rule lrq) .
                                 Term_Rewriting.showsl_lit "\nthe state ") .
                                Term_Rewriting.showsl q) .
                                Term_Rewriting.showsl_lit
                                  " is only reachable from the lhs\n";
                          }))));
        })
        (\ x ->
          Sum_Type.Inl
            (((Term_Rewriting.showsl_lit
                 "problem when ensuring (state-)compatibility of TRS with TA\n" .
                showsl_tree_automaton ta) .
               Term_Rewriting.showsl_literal "\n") .
              x)));

non_join_with_ta ::
  forall a b c d e f g.
    (Arith.Card_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Compare.Compare_order a, Eq a, Arith.Set_impl a, Term_Rewriting.Showl a,
      Arith.Ceq b, Arith.Ccompare b, Compare.Compare_order b, HOL.Default b,
      Eq b, Arith.Set_impl b, Term_Rewriting.Showl b, Arith.Ceq c,
      Arith.Ccompare c, Compare.Compare_order c, Eq c, Arith.Set_impl c,
      Term_Rewriting.Showl c, Term_Rewriting.Showl d, Arith.Card_UNIV e,
      Arith.Cenum e, Arith.Ceq e, Arith.Cproper_interval e,
      Compare.Compare_order e, Eq e, Arith.Set_impl e, Term_Rewriting.Showl e,
      Arith.Ceq f, Arith.Ccompare f, Compare.Compare_order f, Eq f,
      Arith.Set_impl f, Term_Rewriting.Showl f,
      Term_Rewriting.Showl g) => Tree_automaton a b ->
                                   Ta_relation a ->
                                     [(Term_Rewriting.Term b c,
Term_Rewriting.Term b c)] ->
                                       Term_Rewriting.Term b d ->
 Tree_automaton e b ->
   Ta_relation e ->
     [(Term_Rewriting.Term b f, Term_Rewriting.Term b f)] ->
       Term_Rewriting.Term b g -> Sum_Type.Sum (String -> String) ();
non_join_with_ta ta1 rel1 r1 t1 ta2 rel2 r2 t2 =
  let {
    tA1 = ta_of_ta ta1;
    tA2 = ta_of_ta ta2;
  } in Error_Monad.bind
         (Check_Monad.check (Term_Rewriting.ta_member t1 tA1)
           (Term_Rewriting.showsl_terma t1 .
             Term_Rewriting.showsl_lit " is not accepted by first automaton"))
         (\ _ ->
           Error_Monad.bind
             (Check_Monad.check (Term_Rewriting.ta_member t2 tA2)
               (Term_Rewriting.showsl_terma t2 .
                 Term_Rewriting.showsl_lit
                   " is not accepted by second automaton"))
             (\ _ ->
               Error_Monad.bind
                 (Check_Monad.check
                   (Term_Rewriting.ta_empty
                     (Term_Rewriting.intersect_ta tA1 tA2))
                   (Term_Rewriting.showsl_lit
                     "intersection of automata is non-empty"))
                 (\ _ ->
                   Error_Monad.bind
                     (Error_Monad.catch_error (tree_aut_trs_closed ta1 rel1 r1)
                       (\ x ->
                         Sum_Type.Inl
                           (Term_Rewriting.showsl_lit
                              "could not ensure closure under rewriting for first automaton\n" .
                             x)))
                     (\ _ ->
                       Error_Monad.catch_error (tree_aut_trs_closed ta2 rel2 r2)
                         (\ x ->
                           Sum_Type.Inl
                             (Term_Rewriting.showsl_lit
                                "could not ensure closure under rewriting for second automaton\n" .
                               x))))));

ta_final_impl :: forall a b. Ta_impl a b -> RBT.Rbt a ();
ta_final_impl (TA_Impl x1 x2 x3 x4 x5 x6 x7) = x1;

ta_contains_aux_impl ::
  forall a b.
    (Compare.Compare_order a, Arith.Ceq b, Arith.Ccompare b, Eq b,
      Quasi_Order.Linorder b) => [(a, Arith.Nat)] ->
                                   [b] ->
                                     Ta_impl b a ->
                                       Arith.Set b ->
 Sum_Type.Sum (Term_Rewriting.Term a b) ();
ta_contains_aux_impl f qs ta q =
  let {
    _ = ta_final_impl ta;
    look = RBT_Map_Set_Extension.rm_set_lookup (ta_rules_impl ta);
    _ = ta_epss_impl ta;
  } in Error_Monad.catch_error
         (Error_Monad.forallM
           (\ (fa, n) ->
             let {
               rules = look (fa, n);
             } in Error_Monad.catch_error
                    (Error_Monad.catch_error
                      (Error_Monad.forallM
                        (\ x ->
                          (if any (\ rule ->
                                    r_lhs_states_impl rule == x &&
                                      let {
qq = rqss_impl rule;
                                      } in
RBTSetImpl.g_bex_dflt_basic_oops_rm_basic_ops qq (\ qa -> Arith.member qa q))
                                rules
                            then Sum_Type.Inr () else Sum_Type.Inl x))
                        (Missing_List.concat_lists (Arith.replicate n qs)))
                      (\ x -> Sum_Type.Inl (snd x)))
                    (\ x ->
                      Sum_Type.Inl
                        (Term_Rewriting.Fun fa (map Term_Rewriting.Var x))))
           f)
         (\ x -> Sum_Type.Inl (snd x));

ta_contains_impl ::
  forall a b.
    (Compare.Compare_order a, Arith.Cenum b, Arith.Ceq b, Arith.Ccompare b,
      Compare.Compare_order b, Eq b,
      Arith.Set_impl b) => [(a, Arith.Nat)] ->
                             [(a, Arith.Nat)] ->
                               Ta_impl b a ->
                                 [b] ->
                                   Sum_Type.Sum (Term_Rewriting.Term a b) ();
ta_contains_impl f g ta qs =
  Error_Monad.bind (ta_contains_aux_impl f qs ta (Arith.set qs))
    (\ _ ->
      ta_contains_aux_impl g qs ta
        (RBTSetImpl.alpha_rm_basic_ops (ta_final_impl ta)));

ta_rules_impla ::
  forall a b. Tree_automaton a b -> [Term_Rewriting.Ta_rule a b];
ta_rules_impla (Tree_Automaton x1 x2 x3) = x2;

rule_state_compatible_heuristic ::
  forall a b c.
    (Compare.Compare_order a, Compare.Compare_order b,
      Quasi_Order.Linorder c) => Ta_impl a b -> Term_Rewriting.Term b c -> Bool;
rule_state_compatible_heuristic ta l =
  RBTSetImpl.g_isEmpty_dflt_basic_oops_rm_basic_ops
    (ta_res_impl_all (ta_rhs_states_set ta) (ta_rules_impl ta) l);

equal_ta_relation :: forall a. (Eq a) => Ta_relation a -> Ta_relation a -> Bool;
equal_ta_relation Id_Relation (Some_Relation x4) = False;
equal_ta_relation (Some_Relation x4) Id_Relation = False;
equal_ta_relation Decision_Proc (Some_Relation x4) = False;
equal_ta_relation (Some_Relation x4) Decision_Proc = False;
equal_ta_relation Decision_Proc Id_Relation = False;
equal_ta_relation Id_Relation Decision_Proc = False;
equal_ta_relation Decision_Proc_Old (Some_Relation x4) = False;
equal_ta_relation (Some_Relation x4) Decision_Proc_Old = False;
equal_ta_relation Decision_Proc_Old Id_Relation = False;
equal_ta_relation Id_Relation Decision_Proc_Old = False;
equal_ta_relation Decision_Proc_Old Decision_Proc = False;
equal_ta_relation Decision_Proc Decision_Proc_Old = False;
equal_ta_relation (Some_Relation x4) (Some_Relation y4) = x4 == y4;
equal_ta_relation Id_Relation Id_Relation = True;
equal_ta_relation Decision_Proc Decision_Proc = True;
equal_ta_relation Decision_Proc_Old Decision_Proc_Old = True;

}
