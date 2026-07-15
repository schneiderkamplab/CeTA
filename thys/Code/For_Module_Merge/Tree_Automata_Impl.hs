{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Tree_Automata_Impl(showsl_ta_rule, Ta_rule_impl, Ta_impl, Ta_relation(..),
                      Tree_automaton(..), ta_of_ta, check_det, rel_checker,
                      generate_ta_cond, ta_rhs_states_set, ta_rules_impl,
                      state_compatible_eff_list, tree_aut_trs_closed,
                      non_join_with_ta, ta_final_impl, ta_contains_impl,
                      ta_rules_impla, rule_state_compatible_heuristic)
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
import qualified Option;
import qualified Trs_Impl;
import qualified Tree_Automata_Wit_Impl;
import qualified Term_More;
import qualified Transitive_Closure;
import qualified Relation;
import qualified Missing_List;
import qualified Product_Lexorder;
import qualified Tree_Automata_Det;
import qualified Collection_Enum;
import qualified Cardinality;
import qualified Tree_Automata_Autoref_Setup;
import qualified List_Lexorder;
import qualified Term;
import qualified Orderings;
import qualified RBTSetImpl;
import qualified Transitive_Closure_RBT_Impl;
import qualified RBT_Map_Set_Extension;
import qualified Product_Type;
import qualified HOL;
import qualified Compare;
import qualified Compare_Order_Instances;
import qualified Compare_Instances;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified List;
import qualified Set;
import qualified Container_Setup;
import qualified Collection_Order;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified RBT;
import qualified Arith;
import qualified Tree_Automata;
import qualified Shows_Literal;

showsl_ta_rule ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => Tree_Automata.Ta_rule a b -> String -> String;
showsl_ta_rule (Tree_Automata.TA_rule f qs q) =
  ((Shows_Literal.showsl f . Shows_Literal.showsl_list qs) .
    Shows_Literal.showsl_lit " -> ") .
    Shows_Literal.showsl q;

showsl_list_ta_rule ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => [Tree_Automata.Ta_rule a b] -> String -> String;
showsl_list_ta_rule xs = Shows_Literal.default_showsl_list showsl_ta_rule xs;

instance (Shows_Literal.Showl a,
           Shows_Literal.Showl b) => Shows_Literal.Showl (Tree_Automata.Ta_rule
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
  Tree_Automaton [a] [Tree_Automata.Ta_rule a b] [(a, a)];

ta_of_ta ::
  forall a b.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Eq a,
      Set_Impl.Set_impl a, Collection_Order.Ccompare b,
      Eq b) => Tree_automaton a b -> Tree_Automata.Ta_ext a b ();
ta_of_ta (Tree_Automaton fin rules eps) =
  Tree_Automata.Ta_ext (List.set fin) (List.set rules) (List.set eps) ();

check_det ::
  forall a b.
    (Eq a, Eq b) => Tree_automaton a b -> Sum_Type.Sum (String -> String) ();
check_det (Tree_Automaton fin rules eps) =
  Error_Monad.catch_error
    (Error_Monad.bind
      (Check_Monad.check (null eps)
        (Shows_Literal.showsl_lit "epsilon transitions not allowed"))
      (\ _ ->
        Check_Monad.check
          (List.distinct
            (map (\ (Tree_Automata.TA_rule f qs _) -> (f, qs))
              (List.remdups rules)))
          (Shows_Literal.showsl_lit "some lhs occurs twice")))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "problem when ensuring determinism of automata\n" .
          x));

rqss_impl :: forall a b. Ta_rule_impl a b -> RBT.Rbt a ();
rqss_impl (TA_rule_impl f qsa q qs) = qs;

r_sym_impl :: forall a b. Ta_rule_impl a b -> (b, Arith.Nat);
r_sym_impl (TA_rule_impl f qsa q qs) = (f, List.size_list qsa);

conv_ta_rule ::
  forall a b.
    (a -> RBT.Rbt a ()) -> Tree_Automata.Ta_rule a b -> Ta_rule_impl a b;
conv_ta_rule eps (Tree_Automata.TA_rule f qs q) = TA_rule_impl f qs q (eps q);

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
        (map (\ rule -> ep (Tree_Automata.r_rhs rule)) rules);
    rrules = map (conv_ta_rule ep) rules;
  } in TA_Impl (RBTSetImpl.g_from_list_dflt_basic_oops_rm_basic_ops fin)
         (RBT_Map_Set_Extension.elem_list_to_rm r_sym_impl rrules)
         (RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops rqs_rs) rqs_rs eps
         ep epr;

rel_checker ::
  forall a.
    (Eq a,
      Orderings.Linorder a) => Ta_relation a ->
                                 RBT.Rbt a () -> RBT.Rbt a () -> Maybe a;
rel_checker (Some_Relation rel) =
  (\ lhs rhs ->
    let {
      rlist = RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops rhs;
    } in (case Error_Monad.catch_error
                 (Error_Monad.forallM
                   (\ l ->
                     Check_Monad.check
                       (any (\ r -> List.member rel (l, r)) rlist) l)
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
                                      Term.Term a b -> RBT.Rbt b ();
ta_res_impl ta eps (Term.Var q) = eps q;
ta_res_impl ta eps (Term.Fun f ts) =
  let {
    rec = map (ta_res_impl ta eps) ts;
    n = List.size_list ts;
    rules = RBT_Map_Set_Extension.rm_set_lookup ta (f, n);
    arules =
      filter
        (\ rule ->
          let {
            qs = r_lhs_states_impl rule;
          } in all (\ i ->
                     RBTSetImpl.memb_rm_basic_ops (List.nth qs i)
                       (List.nth rec i))
                 (List.upt Arith.zero_nat n))
        rules;
    a = map rqss_impl arules;
  } in RBT_Map_Set_Extension.rs_Union a;

sorted_ps_ta ::
  forall a b.
    (Cardinality.Card_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Compare.Compare a, Eq a,
      Orderings.Linorder a, Set_Impl.Set_impl a, Collection_Eq.Ceq b,
      Collection_Order.Ccompare b, Compare.Compare b, Eq b,
      Set_Impl.Set_impl b) => Tree_Automata.Ta_ext a b () ->
                                Tree_automaton [a] b;
sorted_ps_ta ta =
  Tree_Automaton
    (List.sorted_list_of_set
      (Set.image List.sorted_list_of_set
        (Tree_Automata.ta_final (Tree_Automata_Det.ps_ta ta))))
    (List.sorted_list_of_set
      (Set.image
        (\ (Tree_Automata.TA_rule g qs q) ->
          Tree_Automata.TA_rule g (map List.sorted_list_of_set qs)
            (List.sorted_list_of_set q))
        (Tree_Automata.ta_rules (Tree_Automata_Det.ps_ta ta))))
    [];

ta_match_impl ::
  forall a b c.
    (Compare.Compare_order a, Compare.Compare_order b, Eq b,
      Compare.Compare_order c,
      Eq c) => RBT.Rbt (a, Arith.Nat) [Ta_rule_impl b a] ->
                 RBT.Rbt b () ->
                   (b -> RBT.Rbt b ()) ->
                     Term.Term a c -> [b] -> RBT.Rbt [(c, b)] ();
ta_match_impl ta qsig eps (Term.Var x) q =
  RBTSetImpl.g_from_list_dflt_basic_oops_rm_basic_ops
    (map (\ qa -> [(x, qa)])
      (RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops
        (RBTSetImpl.g_inter_dflt_basic_oops_rm_basic_ops
          (RBT_Map_Set_Extension.rs_Union (map eps q)) qsig)));
ta_match_impl ta qsig eps (Term.Fun f ts) q =
  let {
    n = List.size_list ts;
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
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => (a -> [a]) ->
                                  RBT.Rbt (a, a) () ->
                                    [Tree_Automata.Ta_rule a b] ->
                                      Tree_Automata.Ta_rule a b ->
Sum_Type.Sum (String -> String) ();
check_coherent_rule iter rel rules (Tree_Automata.TA_rule f qs q) =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ i ->
        let {
          qi = List.nth qs i;
        } in Error_Monad.catch_error
               (Error_Monad.forallM
                 (\ qia ->
                   let {
                     qsa = List.list_update qs i qia;
                   } in Check_Monad.check
                          (not (null (filter
                                       (\ (Tree_Automata.TA_rule g qsb qa) ->
 f == g && qsa == qsb && RBTSetImpl.memb_rm_basic_ops (q, qa) rel)
                                       rules)))
                          ((((((((((Shows_Literal.showsl_lit "rule " .
                                     Shows_Literal.showsl f) .
                                    Shows_Literal.showsl_lit "(") .
                                   Shows_Literal.showsl_list qs) .
                                  Shows_Literal.showsl_lit ") -> ") .
                                 Shows_Literal.showsl q) .
                                Shows_Literal.showsl_lit " with ") .
                               Shows_Literal.showsl_nat (Arith.suc i)) .
                              Shows_Literal.showsl_lit
                                ". argument decreased to ") .
                             Shows_Literal.showsl qia) .
                            Shows_Literal.showsl_lit " has no counterpart"))
                 (iter qi))
               (\ x -> Sum_Type.Inl (snd x)))
      (List.upt Arith.zero_nat (List.size_list qs)))
    (\ x -> Sum_Type.Inl (snd x));

check_coherent ::
  forall a b.
    (Cardinality.Card_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Ccompare a, Compare.Compare_order a, Eq a,
      Set_Impl.Set_impl a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => Tree_automaton a b ->
                                  Ta_relation a ->
                                    Sum_Type.Sum (String -> String) ();
check_coherent (Tree_Automaton fin rules eps) (Some_Relation rel) =
  let {
    iter =
      (\ q ->
        List.map_filter
          (\ x -> (if (case x of {
                        (a, _) -> a == q;
                      })
                    then Just (snd x) else Nothing))
          rel);
    rs = RBTSetImpl.g_from_list_dflt_basic_oops_rm_basic_ops rel;
    ep = List.set eps;
    rell = Relation.converse (List.set rel);
  } in Error_Monad.bind
         (Error_Monad.catch_error
           (Check_Monad.check_subseteq (concatMap iter fin) fin)
           (\ x ->
             Sum_Type.Inl
               (Shows_Literal.showsl x .
                 Shows_Literal.showsl_lit
                   " is in relation to a final state, but not a final state itself")))
         (\ _ ->
           Error_Monad.bind
             (Error_Monad.catch_error
               (Error_Monad.forallM (check_coherent_rule iter rs rules) rules)
               (\ x -> Sum_Type.Inl (snd x)))
             (\ _ ->
               Check_Monad.check
                 (Set.less_eq_set (Relation.relcomp rell ep)
                   (Set.sup_set
                     (Relation.relcomp (Transitive_Closure.trancl ep) rell)
                     rell))
                 (Shows_Literal.showsl_lit
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
                     [b] -> Term.Term a c -> RBT.Rbt [(c, b)] ();
ta_match_impla ta qsig eps rhs t = ta_match_impl ta qsig eps t rhs;

ta_res_impl_all ::
  forall a b c.
    (Compare.Compare_order a,
      Compare.Compare_order b) => RBT.Rbt a () ->
                                    RBT.Rbt (b, Arith.Nat) [Ta_rule_impl a b] ->
                                      Term.Term b c -> RBT.Rbt a ();
ta_res_impl_all q ta (Term.Var uu) = q;
ta_res_impl_all q ta (Term.Fun f ts) =
  let {
    rec = map (ta_res_impl_all q ta) ts;
    n = List.size_list ts;
    rules = RBT_Map_Set_Extension.rm_set_lookup ta (f, n);
    arules =
      filter
        (\ rule ->
          let {
            qs = r_lhs_states_impl rule;
          } in all (\ i ->
                     RBTSetImpl.memb_rm_basic_ops (List.nth qs i)
                       (List.nth rec i))
                 (List.upt Arith.zero_nat n))
        rules;
    a = map rqss_impl arules;
  } in RBT_Map_Set_Extension.rs_Union a;

generate_ta_cond ::
  forall a b.
    (Cardinality.Card_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Ccompare a, Compare.Compare_order a, Eq a,
      Set_Impl.Set_impl a, Shows_Literal.Showl a, Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => Tree_automaton a b ->
                                  Ta_relation a ->
                                    Sum_Type.Sum (String -> String)
                                      (Ta_impl a b);
generate_ta_cond ta rel =
  Error_Monad.bind
    (Error_Monad.catch_error (check_coherent ta rel)
      (\ x ->
        Sum_Type.Inl
          (Shows_Literal.showsl_lit
             "automaton is not coherent w.r.t. relation\n" .
            x)))
    (\ _ -> Sum_Type.Inr (generate_ta ta));

showsl_tree_automaton ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => Tree_automaton a b -> String -> String;
showsl_tree_automaton (Tree_Automaton fin rules eps) =
  (((((Shows_Literal.showsl_lit "final: " . Shows_Literal.showsl_list fin) .
       Shows_Literal.showsl_lit "\nrules: ") .
      Shows_Literal.showsl_lines "empty" rules) .
     Shows_Literal.showsl_lit "\nepsilon: ") .
    Shows_Literal.showsl_list_prod eps) .
    Shows_Literal.showsl_literal "\n";

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
                   (Term.Term b c, Term.Term b c) ->
                     Sum_Type.Sum ((Term.Term b a, Term.Term b a), a) ();
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
             (\ sigma -> let {
                           sigmaa = Util.fun_of sigma;
                           l_sigma = Term.map_term (\ x -> x) sigmaa l;
                           r_sigma = Term.map_term (\ x -> x) sigmaa r;
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
                   [(Term.Term b c, Term.Term b c)] ->
                     Sum_Type.Sum
                       ((Term.Term b c, Term.Term b c),
                         ((Term.Term b a, Term.Term b a), a))
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
    (Cardinality.Card_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Compare.Compare_order a, Eq a,
      Set_Impl.Set_impl a, Shows_Literal.Showl a, Collection_Eq.Ceq b,
      Collection_Order.Ccompare b, Compare.Compare_order b, HOL.Default b, Eq b,
      Set_Impl.Set_impl b, Shows_Literal.Showl b, Collection_Eq.Ceq c,
      Collection_Order.Ccompare c, Compare.Compare_order c, Eq c,
      Set_Impl.Set_impl c,
      Shows_Literal.Showl c) => Tree_automaton a b ->
                                  Ta_relation a ->
                                    [(Term.Term b c, Term.Term b c)] ->
                                      Sum_Type.Sum (String -> String) ();
tree_aut_trs_closed ta rel r =
  Error_Monad.bind (Trs_Impl.check_varcond_subset r)
    (\ _ ->
      Error_Monad.catch_error
        (case rel of {
          Decision_Proc_Old ->
            Error_Monad.bind
              (Error_Monad.catch_error (check_det ta)
                (\ x ->
                  Sum_Type.Inl
                    (Shows_Literal.showsl_lit
                       "decision procedure requires det. TA as input\n" .
                      x)))
              (\ _ ->
                Check_Monad.check
                  (Tree_Automata.closed_under_rewriting (ta_of_ta ta)
                    (List.set r))
                  (Shows_Literal.showsl_lit
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
                              ((((Shows_Literal.showsl_lit
                                    "TA is not closed under rewriting\n" .
                                   Term_More.showsl_terma wl) .
                                  Shows_Literal.showsl_lit
                                    " is accepted by TA and rewrites to\n") .
                                 Term_More.showsl_terma wr) .
                                Shows_Literal.showsl_lit
                                  " which is not accepted by TA");
                        })
                   else let {
                          tca = ta_code_make_impl
                                  (sorted_ps_ta
                                    (Tree_Automata.trim_ta (ta_of_ta ta)));
                        } in (case Tree_Automata_Wit_Impl.check_comcoh_wit_ls
                                     tca r
                               of {
                               Nothing -> Sum_Type.Inr ();
                               Just (wl, wr) ->
                                 Sum_Type.Inl
                                   ((((Shows_Literal.showsl_lit
 "TA is not closed under rewriting\n" .
Term_More.showsl_terma wl) .
                                       Shows_Literal.showsl_lit
 " is accepted by TA and rewrites to\n") .
                                      Term_More.showsl_terma wr) .
                                     Shows_Literal.showsl_lit
                                       " which is not accepted by TA");
                             }));
          Id_Relation ->
            Error_Monad.bind (generate_ta_cond ta rel)
              (\ taa ->
                Error_Monad.bind
                  (Error_Monad.catch_error
                    (if Error_Monad.isOK (Trs_Impl.check_left_linear_trs r)
                      then Sum_Type.Inr () else check_det ta)
                    (\ x ->
                      Sum_Type.Inl
                        (Shows_Literal.showsl_lit
                           "could not ensure left-linearity or determinism\n" .
                          x)))
                  (\ _ ->
                    Error_Monad.catch_error
                      (state_compatible_eff_list taa (rel_checker rel) r)
                      (\ x ->
                        Sum_Type.Inl
                          (case x of {
                            (lr, (lrq, q)) ->
                              ((((((Shows_Literal.showsl_lit
                                      "TA is not compatible with R\n" .
                                     Shows_Literal.showsl_lit "for rule ") .
                                    Trs_Impl.showsl_rule lr) .
                                   Shows_Literal.showsl_lit
                                     "\nwhich is instantiated by states to ") .
                                  Trs_Impl.showsl_rule lrq) .
                                 Shows_Literal.showsl_lit "\nthe state ") .
                                Shows_Literal.showsl q) .
                                Shows_Literal.showsl_lit
                                  " is only reachable from the lhs\n";
                          }))));
          Some_Relation _ ->
            Error_Monad.bind (generate_ta_cond ta rel)
              (\ taa ->
                Error_Monad.bind
                  (Error_Monad.catch_error
                    (if Error_Monad.isOK (Trs_Impl.check_left_linear_trs r)
                      then Sum_Type.Inr () else check_det ta)
                    (\ x ->
                      Sum_Type.Inl
                        (Shows_Literal.showsl_lit
                           "could not ensure left-linearity or determinism\n" .
                          x)))
                  (\ _ ->
                    Error_Monad.catch_error
                      (state_compatible_eff_list taa (rel_checker rel) r)
                      (\ x ->
                        Sum_Type.Inl
                          (case x of {
                            (lr, (lrq, q)) ->
                              ((((((Shows_Literal.showsl_lit
                                      "TA is not compatible with R\n" .
                                     Shows_Literal.showsl_lit "for rule ") .
                                    Trs_Impl.showsl_rule lr) .
                                   Shows_Literal.showsl_lit
                                     "\nwhich is instantiated by states to ") .
                                  Trs_Impl.showsl_rule lrq) .
                                 Shows_Literal.showsl_lit "\nthe state ") .
                                Shows_Literal.showsl q) .
                                Shows_Literal.showsl_lit
                                  " is only reachable from the lhs\n";
                          }))));
        })
        (\ x ->
          Sum_Type.Inl
            (((Shows_Literal.showsl_lit
                 "problem when ensuring (state-)compatibility of TRS with TA\n" .
                showsl_tree_automaton ta) .
               Shows_Literal.showsl_literal "\n") .
              x)));

non_join_with_ta ::
  forall a b c d e f g.
    (Cardinality.Card_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Compare.Compare_order a, Eq a,
      Set_Impl.Set_impl a, Shows_Literal.Showl a, Collection_Eq.Ceq b,
      Collection_Order.Ccompare b, Compare.Compare_order b, HOL.Default b, Eq b,
      Set_Impl.Set_impl b, Shows_Literal.Showl b, Collection_Eq.Ceq c,
      Collection_Order.Ccompare c, Compare.Compare_order c, Eq c,
      Set_Impl.Set_impl c, Shows_Literal.Showl c, Shows_Literal.Showl d,
      Cardinality.Card_UNIV e, Collection_Enum.Cenum e, Collection_Eq.Ceq e,
      Collection_Order.Cproper_interval e, Compare.Compare_order e, Eq e,
      Set_Impl.Set_impl e, Shows_Literal.Showl e, Collection_Eq.Ceq f,
      Collection_Order.Ccompare f, Compare.Compare_order f, Eq f,
      Set_Impl.Set_impl f, Shows_Literal.Showl f,
      Shows_Literal.Showl g) => Tree_automaton a b ->
                                  Ta_relation a ->
                                    [(Term.Term b c, Term.Term b c)] ->
                                      Term.Term b d ->
Tree_automaton e b ->
  Ta_relation e ->
    [(Term.Term b f, Term.Term b f)] ->
      Term.Term b g -> Sum_Type.Sum (String -> String) ();
non_join_with_ta ta1 rel1 r1 t1 ta2 rel2 r2 t2 =
  let {
    tA1 = ta_of_ta ta1;
    tA2 = ta_of_ta ta2;
  } in Error_Monad.bind
         (Check_Monad.check (Tree_Automata.ta_member t1 tA1)
           (Term_More.showsl_terma t1 .
             Shows_Literal.showsl_lit " is not accepted by first automaton"))
         (\ _ ->
           Error_Monad.bind
             (Check_Monad.check (Tree_Automata.ta_member t2 tA2)
               (Term_More.showsl_terma t2 .
                 Shows_Literal.showsl_lit
                   " is not accepted by second automaton"))
             (\ _ ->
               Error_Monad.bind
                 (Check_Monad.check
                   (Tree_Automata.ta_empty (Tree_Automata.intersect_ta tA1 tA2))
                   (Shows_Literal.showsl_lit
                     "intersection of automata is non-empty"))
                 (\ _ ->
                   Error_Monad.bind
                     (Error_Monad.catch_error (tree_aut_trs_closed ta1 rel1 r1)
                       (\ x ->
                         Sum_Type.Inl
                           (Shows_Literal.showsl_lit
                              "could not ensure closure under rewriting for first automaton\n" .
                             x)))
                     (\ _ ->
                       Error_Monad.catch_error (tree_aut_trs_closed ta2 rel2 r2)
                         (\ x ->
                           Sum_Type.Inl
                             (Shows_Literal.showsl_lit
                                "could not ensure closure under rewriting for second automaton\n" .
                               x))))));

ta_final_impl :: forall a b. Ta_impl a b -> RBT.Rbt a ();
ta_final_impl (TA_Impl x1 x2 x3 x4 x5 x6 x7) = x1;

ta_contains_aux_impl ::
  forall a b.
    (Compare.Compare_order a, Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Eq b,
      Orderings.Linorder b) => [(a, Arith.Nat)] ->
                                 [b] ->
                                   Ta_impl b a ->
                                     Set.Set b ->
                                       Sum_Type.Sum (Term.Term a b) ();
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
RBTSetImpl.g_bex_dflt_basic_oops_rm_basic_ops qq (\ qa -> Set.member qa q))
                                rules
                            then Sum_Type.Inr () else Sum_Type.Inl x))
                        (Missing_List.concat_lists (List.replicate n qs)))
                      (\ x -> Sum_Type.Inl (snd x)))
                    (\ x -> Sum_Type.Inl (Term.Fun fa (map Term.Var x))))
           f)
         (\ x -> Sum_Type.Inl (snd x));

ta_contains_impl ::
  forall a b.
    (Compare.Compare_order a, Collection_Enum.Cenum b, Collection_Eq.Ceq b,
      Collection_Order.Ccompare b, Compare.Compare_order b, Eq b,
      Set_Impl.Set_impl b) => [(a, Arith.Nat)] ->
                                [(a, Arith.Nat)] ->
                                  Ta_impl b a ->
                                    [b] -> Sum_Type.Sum (Term.Term a b) ();
ta_contains_impl f g ta qs =
  Error_Monad.bind (ta_contains_aux_impl f qs ta (List.set qs))
    (\ _ ->
      ta_contains_aux_impl g qs ta
        (RBTSetImpl.alpha_rm_basic_ops (ta_final_impl ta)));

ta_rules_impla :: forall a b. Tree_automaton a b -> [Tree_Automata.Ta_rule a b];
ta_rules_impla (Tree_Automaton x1 x2 x3) = x2;

rule_state_compatible_heuristic ::
  forall a b c.
    (Compare.Compare_order a, Compare.Compare_order b,
      Orderings.Linorder c) => Ta_impl a b -> Term.Term b c -> Bool;
rule_state_compatible_heuristic ta l =
  RBTSetImpl.g_isEmpty_dflt_basic_oops_rm_basic_ops
    (ta_res_impl_all (ta_rhs_states_set ta) (ta_rules_impl ta) l);

}
