{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Exact_Tree_Automata_Completion_Impl(map_states_impl, check_etac_nonreachable)
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
import qualified Trs_Impl;
import qualified HOL;
import qualified Term_More;
import qualified Error_Monad;
import qualified Complete_Lattices;
import qualified Cardinality;
import qualified Collection_Enum;
import qualified Tree_Automata_Impl;
import qualified Shows_Literal;
import qualified Check_Monad;
import qualified Collection_Eq;
import qualified Arith;
import qualified Product_Type;
import qualified Util;
import qualified List;
import qualified Tree_Automata;
import qualified Phantom_Type;
import qualified Set_Impl;
import qualified Sum_Type;
import qualified Set;
import qualified Collection_Order;
import qualified Compare;
import qualified Container_Setup;
import qualified Exact_Tree_Automata_Completion;
import qualified Term_Impl;
import qualified Term;

qi :: forall a b.
        (Eq b) => a -> Term.Term a b ->
                         (b -> Term.Term a b) -> Term.Term a b -> Term.Term a b;
qi c t g (Term.Var x) =
  (if Term_Impl.contains_var_term x t then g x
    else Exact_Tree_Automata_Completion.star c (Term.Var x));
qi c t g (Term.Fun f ts) =
  Exact_Tree_Automata_Completion.star c (Term.Fun f ts);

combs :: forall a b. [a] -> [b] -> [[(a, b)]];
combs [] ys = [[]];
combs (x : xs) ys = concatMap (\ l -> map (\ y -> (x, y) : l) ys) (combs xs ys);

inf_step ::
  forall a b.
    (Collection_Order.Ccompare a, Compare.Compare a, Eq a, Compare.Compare b,
      Eq b) => a -> [(Term.Term a b, Term.Term a b)] ->
                      [[(b, Term.Term a b)]] ->
                        Set.Set (Tree_Automata.Ta_rule (Term.Term a b) a) ->
                          Set.Set (Tree_Automata.Ta_rule (Term.Term a b) a);
inf_step c r s delta =
  List.foldr
    (Set.sup_set .
      (\ (a, b) ->
        (case a of {
          (l, ra) ->
            (\ theta ->
              (case l of {
                Term.Fun f ls ->
                  Set.image
                    (Tree_Automata.TA_rule f
                      (map (qi c ra (Util.fun_of theta)) ls))
                    ((Exact_Tree_Automata_Completion.reachable_states ::
                       Set.Set (Tree_Automata.Ta_rule (Term.Term a b) a) ->
                         Term.Term (Sum_Type.Sum a (Term.Term a b)) b ->
                           Set.Set (Term.Term a b))
                      delta
                      (Term.eval_term Term.Fun
                        (Term.map_term Sum_Type.Inl (\ x -> x) ra)
                        ((\ fa -> Term.Fun (Sum_Type.Inr fa) []) .
                          Util.fun_of theta)));
              }));
        })
          b))
    (List.product r s)
    (Set_Impl.set_empty
      (Phantom_Type.of_phantom Container_Setup.set_impl_ta_rule));

lhss_impl :: forall a b. (Eq a) => [(a, b)] -> [a];
lhss_impl r = List.remdups (map fst r);

sig_rules_list ::
  forall a b. [(a, Arith.Nat)] -> b -> [Tree_Automata.Ta_rule b a];
sig_rules_list f c =
  map (\ (fa, n) -> Tree_Automata.TA_rule fa (List.replicate n c) c) f;

gi_rules_list ::
  forall a b.
    [(a, Arith.Nat)] ->
      a -> Term.Term a b -> [Tree_Automata.Ta_rule (Term.Term a b) a];
gi_rules_list f c (Term.Var x) = sig_rules_list f (Term.Fun c []);
gi_rules_list fa c (Term.Fun f ts) =
  Tree_Automata.TA_rule f (map (Exact_Tree_Automata_Completion.star c) ts)
    (Exact_Tree_Automata_Completion.star c (Term.Fun f ts)) :
    concatMap (gi_rules_list fa c) ts;

mp_ta_rules ::
  forall a b c.
    (Eq a,
      Eq b) => [(Term.Term a b, c)] ->
                 [(a, Arith.Nat)] ->
                   a -> [Tree_Automata.Ta_rule (Term.Term a b) a];
mp_ta_rules r f c = concatMap (gi_rules_list f c) (lhss_impl r);

state_substs :: forall a b. [a] -> [b] -> [[(a, b)]];
state_substs v q = combs v q;

check_growing ::
  forall a b.
    (Compare.Compare a, Eq a, Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Compare.Compare b, Eq b,
      Set_Impl.Set_impl b) => [(Term.Term a b, Term.Term a b)] ->
                                Sum_Type.Sum (String -> String) ();
check_growing r =
  Check_Monad.check (Exact_Tree_Automata_Completion.growing (List.set r))
    (Shows_Literal.showsl_lit "TRS is not growing");

add_rule_states ::
  forall a b. (Eq a) => [Tree_Automata.Ta_rule a b] -> [a] -> [a];
add_rule_states rs ss =
  List.fold
    (\ r ssa ->
      (case r of {
        Tree_Automata.TA_rule _ qs q ->
          List.insert q (List.fold List.insert qs ssa);
      }))
    rs ss;

map_states_impl ::
  forall a b c.
    (a -> b) ->
      Tree_Automata_Impl.Tree_automaton a c ->
        Tree_Automata_Impl.Tree_automaton b c;
map_states_impl f (Tree_Automata_Impl.Tree_Automaton qs ts eps) =
  Tree_Automata_Impl.Tree_Automaton (map f qs)
    (map (Exact_Tree_Automata_Completion.map_r_states f) ts)
    (map (\ (p, q) -> (f p, f q)) eps);

ta_inter_eps_empty ::
  forall a b c d.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Eq a,
      Set_Impl.Set_impl a, Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Eq b, Set_Impl.Set_impl b, Collection_Eq.Ceq c,
      Collection_Order.Ccompare c, Eq c,
      Set_Impl.Set_impl c) => Tree_Automata.Ta_ext a b () ->
                                Tree_Automata.Ta_ext c b d ->
                                  Tree_Automata.Ta_ext (a, c) b ();
ta_inter_eps_empty ta t =
  Tree_Automata.Ta_ext
    (Product_Type.product (Tree_Automata.ta_final ta)
      (Tree_Automata.ta_final t))
    (Set.image
      (\ (Tree_Automata.TA_rule f ps p, Tree_Automata.TA_rule _ qs q) ->
        Tree_Automata.TA_rule f (zip ps qs) (p, q))
      (Complete_Lattices.sup_set
        (Set.image
          (\ f ->
            Product_Type.product
              (Set.filtera (\ r -> Tree_Automata.r_sym r == f)
                (Tree_Automata.ta_rules ta))
              (Set.filtera (\ r -> Tree_Automata.r_sym r == f)
                (Tree_Automata.ta_rules t)))
          (Tree_Automata.ta_syms ta))))
    Set.bot_set ();

check_rules_subseteq ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => [Tree_Automata.Ta_rule a b] ->
                                  Tree_Automata_Impl.Tree_automaton a b ->
                                    Sum_Type.Sum (String -> String) ();
check_rules_subseteq rs a =
  Error_Monad.catch_error
    (Check_Monad.check_subseteq rs (Tree_Automata_Impl.ta_rules_impla a))
    (\ x ->
      Sum_Type.Inl
        ((Shows_Literal.showsl_lit "rule " .
           Tree_Automata_Impl.showsl_ta_rule x) .
          Shows_Literal.showsl_lit " is missing"));

check_etac_nonreachable ::
  forall a b.
    (Cardinality.Finite_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Compare.Compare a, HOL.Default a,
      Eq a, Set_Impl.Set_impl a, Shows_Literal.Showl a, Collection_Eq.Ceq b,
      Collection_Order.Ccompare b, Compare.Compare b, Eq b, Set_Impl.Set_impl b,
      Shows_Literal.Showl b) => [(a, Arith.Nat)] ->
                                  a -> a ->
 Tree_Automata_Impl.Tree_automaton (Term.Term a b) a ->
   [(Term.Term a b, Term.Term a b)] ->
     Term.Term a b -> Term.Term a b -> Sum_Type.Sum (String -> String) ();
check_etac_nonreachable f aa c a r s t =
  let {
    fa = List.set f;
  } in Error_Monad.bind
         (Check_Monad.check (Set.member (aa, Arith.zero_nat) fa)
           ((Shows_Literal.showsl_lit "constant " . Shows_Literal.showsl aa) .
             Shows_Literal.showsl_lit " is not in signature"))
         (\ _ ->
           Error_Monad.bind
             (Check_Monad.check (not (Set.member (c, Arith.zero_nat) fa))
               (Shows_Literal.showsl_lit
                 "star-symbol is not fresh w.r.t. signature"))
             (\ _ ->
               Error_Monad.bind
                 (Error_Monad.catch_error
                   (Check_Monad.check_subseteq
                     (Term_Impl.insert_funas_term s []) f)
                   (\ _ ->
                     Sum_Type.Inl
                       (Shows_Literal.showsl_lit "lhs violates signature")))
                 (\ _ ->
                   Error_Monad.bind
                     (Error_Monad.catch_error
                       (Check_Monad.check_subseteq
                         (Term_Impl.insert_funas_term t []) f)
                       (\ _ ->
                         Sum_Type.Inl
                           (Shows_Literal.showsl_lit "rhs violates signature")))
                     (\ _ ->
                       let {
                         fs = Trs_Impl.insert_funas_trs r [];
                       } in Error_Monad.bind
                              (Error_Monad.catch_error
                                (Check_Monad.check_subseteq fs f)
                                (\ _ ->
                                  Sum_Type.Inl
                                    (Shows_Literal.showsl_lit
                                      "TRS violates signature")))
                              (\ _ ->
                                Error_Monad.bind
                                  (Trs_Impl.check_varcond_no_Var_lhs r)
                                  (\ _ ->
                                    Error_Monad.bind
                                      (Trs_Impl.check_linear_trs r)
                                      (\ _ ->
Error_Monad.bind (check_growing r)
  (\ _ ->
    let {
      aaa = Tree_Automata_Impl.ta_of_ta a;
    } in Error_Monad.bind
           (Check_Monad.check
             (Collection_Eq.set_eq (Tree_Automata.ta_eps aaa)
               (Set_Impl.set_empty
                 (Phantom_Type.of_phantom
                   (Set_Impl.set_impl_prod ::
                     Phantom_Type.Phantom (Term.Term a b, Term.Term a b)
                       Set_Impl.Set_impla))))
             (Shows_Literal.showsl_lit "no epsilon transitions allowed"))
           (\ _ ->
             Error_Monad.bind
               (Check_Monad.check
                 (Set.member (Exact_Tree_Automata_Completion.star c t)
                   (Tree_Automata.ta_final aaa))
                 ((Shows_Literal.showsl_lit "final state for " .
                    Term_More.showsl_terma t) .
                   Shows_Literal.showsl_lit " is missing"))
               (\ _ ->
                 Error_Monad.bind
                   (Check_Monad.check
                     (Set.less_eq_set
                       (Exact_Tree_Automata_Completion.funas_ta aaa) fa)
                     (Shows_Literal.showsl_lit
                       "the given automaton does not respect the signature"))
                   (\ _ ->
                     let {
                       ts = gi_rules_list f c t;
                       ms = mp_ta_rules r f c;
                     } in Error_Monad.bind (check_rules_subseteq ts a)
                            (\ _ ->
                              Error_Monad.bind (check_rules_subseteq ms a)
                                (\ _ ->
                                  let {
                                    q = add_rule_states ts
  (add_rule_states ms []);
                                    ss = state_substs
   (List.remdups (concatMap (Term_More.vars_term_list . snd) r)) q;
                                    d = List.set
  (Tree_Automata_Impl.ta_rules_impla a);
                                    da = inf_step c r ss d;
                                  } in Error_Monad.bind
 (Check_Monad.check (Set.less_eq_set da d)
   (Shows_Literal.showsl_lit
     "the given tree automaton is not closed under completion rules"))
 (\ _ ->
   Check_Monad.check
     (Tree_Automata.ta_empty
       (ta_inter_eps_empty aaa
         (Exact_Tree_Automata_Completion.ground_instances_ta fa c s)))
     (Shows_Literal.showsl_lit
       "the given tree automaton does not certify non-reachability")))))))))))))));

}
