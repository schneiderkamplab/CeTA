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
import qualified HOL;
import qualified Error_Monad;
import qualified Complete_Lattices;
import qualified Tree_Automata_Impl;
import qualified Check_Monad;
import qualified Util;
import qualified Phantom_Type;
import qualified Sum_Type;
import qualified Arith;
import qualified Compare;
import qualified Exact_Tree_Automata_Completion;
import qualified Term_Rewriting;

qi :: forall a b.
        (Eq b) => a -> Term_Rewriting.Term a b ->
                         (b -> Term_Rewriting.Term a b) ->
                           Term_Rewriting.Term a b -> Term_Rewriting.Term a b;
qi c t g (Term_Rewriting.Var x) =
  (if Term_Rewriting.contains_var_term x t then g x
    else Exact_Tree_Automata_Completion.star c (Term_Rewriting.Var x));
qi c t g (Term_Rewriting.Fun f ts) =
  Exact_Tree_Automata_Completion.star c (Term_Rewriting.Fun f ts);

combs :: forall a b. [a] -> [b] -> [[(a, b)]];
combs [] ys = [[]];
combs (x : xs) ys = concatMap (\ l -> map (\ y -> (x, y) : l) ys) (combs xs ys);

inf_step ::
  forall a b.
    (Arith.Ccompare a, Compare.Compare a, Eq a, Compare.Compare b,
      Eq b) => a -> [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                      [[(b, Term_Rewriting.Term a b)]] ->
                        Arith.Set
                          (Term_Rewriting.Ta_rule (Term_Rewriting.Term a b)
                            a) ->
                          Arith.Set
                            (Term_Rewriting.Ta_rule (Term_Rewriting.Term a b)
                              a);
inf_step c r s delta =
  Arith.foldr
    (Arith.sup_set .
      (\ (a, b) ->
        (case a of {
          (l, ra) ->
            (\ theta ->
              (case l of {
                Term_Rewriting.Fun f ls ->
                  Arith.image
                    (Term_Rewriting.TA_rule f
                      (map (qi c ra (Util.fun_of theta)) ls))
                    ((Exact_Tree_Automata_Completion.reachable_states ::
                       Arith.Set
                         (Term_Rewriting.Ta_rule (Term_Rewriting.Term a b) a) ->
                         Term_Rewriting.Term
                           (Sum_Type.Sum a (Term_Rewriting.Term a b)) b ->
                           Arith.Set (Term_Rewriting.Term a b))
                      delta
                      (Term_Rewriting.eval_term Term_Rewriting.Fun
                        (Term_Rewriting.map_term Sum_Type.Inl (\ x -> x) ra)
                        ((\ fa -> Term_Rewriting.Fun (Sum_Type.Inr fa) []) .
                          Util.fun_of theta)));
              }));
        })
          b))
    (Arith.product r s)
    (Arith.set_empty (Phantom_Type.of_phantom Term_Rewriting.set_impl_ta_rule));

lhss_impl :: forall a b. (Eq a) => [(a, b)] -> [a];
lhss_impl r = Arith.remdups (map fst r);

sig_rules_list ::
  forall a b. [(a, Arith.Nat)] -> b -> [Term_Rewriting.Ta_rule b a];
sig_rules_list f c =
  map (\ (fa, n) -> Term_Rewriting.TA_rule fa (Arith.replicate n c) c) f;

gi_rules_list ::
  forall a b.
    [(a, Arith.Nat)] ->
      a -> Term_Rewriting.Term a b ->
             [Term_Rewriting.Ta_rule (Term_Rewriting.Term a b) a];
gi_rules_list f c (Term_Rewriting.Var x) =
  sig_rules_list f (Term_Rewriting.Fun c []);
gi_rules_list fa c (Term_Rewriting.Fun f ts) =
  Term_Rewriting.TA_rule f (map (Exact_Tree_Automata_Completion.star c) ts)
    (Exact_Tree_Automata_Completion.star c (Term_Rewriting.Fun f ts)) :
    concatMap (gi_rules_list fa c) ts;

mp_ta_rules ::
  forall a b c.
    (Eq a,
      Eq b) => [(Term_Rewriting.Term a b, c)] ->
                 [(a, Arith.Nat)] ->
                   a -> [Term_Rewriting.Ta_rule (Term_Rewriting.Term a b) a];
mp_ta_rules r f c = concatMap (gi_rules_list f c) (lhss_impl r);

state_substs :: forall a b. [a] -> [b] -> [[(a, b)]];
state_substs v q = combs v q;

check_growing ::
  forall a b.
    (Compare.Compare a, Eq a, Arith.Ceq b, Arith.Ccompare b, Compare.Compare b,
      Eq b,
      Arith.Set_impl b) => [(Term_Rewriting.Term a b,
                              Term_Rewriting.Term a b)] ->
                             Sum_Type.Sum (String -> String) ();
check_growing r =
  Check_Monad.check (Exact_Tree_Automata_Completion.growing (Arith.set r))
    (Term_Rewriting.showsl_lit "TRS is not growing");

add_rule_states ::
  forall a b. (Eq a) => [Term_Rewriting.Ta_rule a b] -> [a] -> [a];
add_rule_states rs ss =
  Arith.fold
    (\ r ssa ->
      (case r of {
        Term_Rewriting.TA_rule _ qs q ->
          Arith.inserta q (Arith.fold Arith.inserta qs ssa);
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
    (Arith.Ceq a, Arith.Ccompare a, Eq a, Arith.Set_impl a, Arith.Ceq b,
      Arith.Ccompare b, Eq b, Arith.Set_impl b, Arith.Ceq c, Arith.Ccompare c,
      Eq c,
      Arith.Set_impl c) => Term_Rewriting.Ta_ext a b () ->
                             Term_Rewriting.Ta_ext c b d ->
                               Term_Rewriting.Ta_ext (a, c) b ();
ta_inter_eps_empty ta t =
  Term_Rewriting.Ta_ext
    (Arith.productc (Term_Rewriting.ta_final ta) (Term_Rewriting.ta_final t))
    (Arith.image
      (\ (Term_Rewriting.TA_rule f ps p, Term_Rewriting.TA_rule _ qs q) ->
        Term_Rewriting.TA_rule f (zip ps qs) (p, q))
      (Complete_Lattices.sup_set
        (Arith.image
          (\ f ->
            Arith.productc
              (Arith.filtera (\ r -> Term_Rewriting.r_sym r == f)
                (Term_Rewriting.ta_rules ta))
              (Arith.filtera (\ r -> Term_Rewriting.r_sym r == f)
                (Term_Rewriting.ta_rules t)))
          (Term_Rewriting.ta_syms ta))))
    Arith.bot_set ();

check_rules_subseteq ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Eq b,
      Term_Rewriting.Showl b) => [Term_Rewriting.Ta_rule a b] ->
                                   Tree_Automata_Impl.Tree_automaton a b ->
                                     Sum_Type.Sum (String -> String) ();
check_rules_subseteq rs a =
  Error_Monad.catch_error
    (Check_Monad.check_subseteq rs (Tree_Automata_Impl.ta_rules_impla a))
    (\ x ->
      Sum_Type.Inl
        ((Term_Rewriting.showsl_lit "rule " .
           Tree_Automata_Impl.showsl_ta_rule x) .
          Term_Rewriting.showsl_lit " is missing"));

check_etac_nonreachable ::
  forall a b.
    (Arith.Finite_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Compare.Compare a, HOL.Default a, Eq a, Arith.Set_impl a,
      Term_Rewriting.Showl a, Arith.Ceq b, Arith.Ccompare b, Compare.Compare b,
      Eq b, Arith.Set_impl b,
      Term_Rewriting.Showl b) => [(a, Arith.Nat)] ->
                                   a -> a ->
  Tree_Automata_Impl.Tree_automaton (Term_Rewriting.Term a b) a ->
    [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
      Term_Rewriting.Term a b ->
        Term_Rewriting.Term a b -> Sum_Type.Sum (String -> String) ();
check_etac_nonreachable f aa c a r s t =
  let {
    fa = Arith.set f;
  } in Error_Monad.bind
         (Check_Monad.check (Arith.member (aa, Arith.zero_nat) fa)
           ((Term_Rewriting.showsl_lit "constant " . Term_Rewriting.showsl aa) .
             Term_Rewriting.showsl_lit " is not in signature"))
         (\ _ ->
           Error_Monad.bind
             (Check_Monad.check (not (Arith.member (c, Arith.zero_nat) fa))
               (Term_Rewriting.showsl_lit
                 "star-symbol is not fresh w.r.t. signature"))
             (\ _ ->
               Error_Monad.bind
                 (Error_Monad.catch_error
                   (Check_Monad.check_subseteq
                     (Term_Rewriting.insert_funas_term s []) f)
                   (\ _ ->
                     Sum_Type.Inl
                       (Term_Rewriting.showsl_lit "lhs violates signature")))
                 (\ _ ->
                   Error_Monad.bind
                     (Error_Monad.catch_error
                       (Check_Monad.check_subseteq
                         (Term_Rewriting.insert_funas_term t []) f)
                       (\ _ ->
                         Sum_Type.Inl
                           (Term_Rewriting.showsl_lit
                             "rhs violates signature")))
                     (\ _ ->
                       let {
                         fs = Term_Rewriting.insert_funas_trs r [];
                       } in Error_Monad.bind
                              (Error_Monad.catch_error
                                (Check_Monad.check_subseteq fs f)
                                (\ _ ->
                                  Sum_Type.Inl
                                    (Term_Rewriting.showsl_lit
                                      "TRS violates signature")))
                              (\ _ ->
                                Error_Monad.bind
                                  (Term_Rewriting.check_varcond_no_Var_lhs r)
                                  (\ _ ->
                                    Error_Monad.bind
                                      (Term_Rewriting.check_linear_trs r)
                                      (\ _ ->
Error_Monad.bind (check_growing r)
  (\ _ ->
    let {
      aaa = Tree_Automata_Impl.ta_of_ta a;
    } in Error_Monad.bind
           (Check_Monad.check
             (Arith.set_eq (Term_Rewriting.ta_eps aaa)
               (Arith.set_empty
                 (Phantom_Type.of_phantom
                   (Arith.set_impl_prod ::
                     Phantom_Type.Phantom
                       (Term_Rewriting.Term a b, Term_Rewriting.Term a b)
                       Arith.Set_impla))))
             (Term_Rewriting.showsl_lit "no epsilon transitions allowed"))
           (\ _ ->
             Error_Monad.bind
               (Check_Monad.check
                 (Arith.member (Exact_Tree_Automata_Completion.star c t)
                   (Term_Rewriting.ta_final aaa))
                 ((Term_Rewriting.showsl_lit "final state for " .
                    Term_Rewriting.showsl_terma t) .
                   Term_Rewriting.showsl_lit " is missing"))
               (\ _ ->
                 Error_Monad.bind
                   (Check_Monad.check
                     (Arith.less_eq_set
                       (Exact_Tree_Automata_Completion.funas_ta aaa) fa)
                     (Term_Rewriting.showsl_lit
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
   (Arith.remdups (concatMap (Term_Rewriting.vars_term_list . snd) r)) q;
                                    d = Arith.set
  (Tree_Automata_Impl.ta_rules_impla a);
                                    da = inf_step c r ss d;
                                  } in Error_Monad.bind
 (Check_Monad.check (Arith.less_eq_set da d)
   (Term_Rewriting.showsl_lit
     "the given tree automaton is not closed under completion rules"))
 (\ _ ->
   Check_Monad.check
     (Term_Rewriting.ta_empty
       (ta_inter_eps_empty aaa
         (Exact_Tree_Automata_Completion.ground_instances_ta fa c s)))
     (Term_Rewriting.showsl_lit
       "the given tree automaton does not certify non-reachability")))))))))))))));

}
