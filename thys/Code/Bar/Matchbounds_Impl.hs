{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Matchbounds_Impl(Boundstype(..), Bounds_info(..), bounds_tt,
                    bounds_complexity, bounds_complexity_rel)
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
import qualified Map_Choice;
import qualified Missing_List;
import qualified RBTSetImpl;
import qualified Compare_Order_Instances;
import qualified QDP_Framework_Impl;
import qualified Check_Monad;
import qualified Complexity;
import qualified RBTMapImpl;
import qualified RBT;
import qualified Product_Lexorder;
import qualified Error_Monad;
import qualified Multiset;
import qualified Matchbounds;
import qualified HOL;
import qualified Termination_Problem_Spec;
import qualified Sum_Type;
import qualified Term_Rewriting;
import qualified Mapping;
import qualified Compare;
import qualified Shows_Literal;
import qualified Quasi_Order;
import qualified Tree_Automata_Impl;
import qualified Arith;

data Boundstype = Roof | Match;

data Bounds_info a b =
  Bounds_Info Boundstype Arith.Nat [b]
    (Tree_Automata_Impl.Tree_automaton b (a, Arith.Nat))
    (Tree_Automata_Impl.Ta_relation b);

check_state_raise_consistent ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Eq a, Quasi_Order.Linorder a,
      Arith.Set_impl a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => Tree_Automata_Impl.Tree_automaton a
                                  (b, Arith.Nat) ->
                                  [(a, a)] ->
                                    Sum_Type.Sum (String -> String) ();
check_state_raise_consistent ta rel =
  let {
    rels = Arith.set rel;
    rls = Tree_Automata_Impl.ta_rules_impla ta;
  } in Error_Monad.catch_error
         (Error_Monad.forallM
           (\ r1 ->
             (case r1 of {
               Term_Rewriting.TA_rule (f1, i1) qs1 q1 ->
                 Error_Monad.catch_error
                   (Error_Monad.forallM
                     (\ r2 ->
                       (case r2 of {
                         Term_Rewriting.TA_rule (f2, i2) qs2 q2 ->
                           (if f1 == f2 && Arith.less_nat i1 i2 && qs1 == qs2
                             then Check_Monad.check (Arith.member (q1, q2) rels)
                                    (((((((Shows_Literal.showsl_lit
     "problem with raise consistency because of automaton-rules\n " .
    Tree_Automata_Impl.showsl_ta_rule r1) .
   Shows_Literal.showsl_literal "\n") .
  Tree_Automata_Impl.showsl_ta_rule r2) .
 Shows_Literal.showsl_literal "\n") .
Shows_Literal.showsl q1) .
                                       Shows_Literal.showsl_lit
 " is not >>^* ") .
                                      Shows_Literal.showsl q2)
                             else Sum_Type.Inr ());
                       }))
                     rls)
                   (\ x -> Sum_Type.Inl (snd x));
             }))
           rls)
         (\ x -> Sum_Type.Inl (snd x));

states_of_tree_automata_dup ::
  forall a b. Tree_Automata_Impl.Tree_automaton a b -> [a];
states_of_tree_automata_dup (Tree_Automata_Impl.Tree_Automaton qfin rules eps) =
  qfin ++
    map fst eps ++
      map snd eps ++
        concatMap Term_Rewriting.r_lhs_states rules ++
          map Term_Rewriting.r_rhs rules;

states_of_ta_relation_dup :: forall a. Tree_Automata_Impl.Ta_relation a -> [a];
states_of_ta_relation_dup (Tree_Automata_Impl.Some_Relation rel) =
  map fst rel ++ map snd rel;
states_of_ta_relation_dup Tree_Automata_Impl.Id_Relation = [];
states_of_ta_relation_dup Tree_Automata_Impl.Decision_Proc_Old = [];
states_of_ta_relation_dup Tree_Automata_Impl.Decision_Proc = [];

states_of_bounds_info_dup :: forall a b. Bounds_info a b -> [b];
states_of_bounds_info_dup (Bounds_Info bt b qs ta rel) =
  qs ++ states_of_tree_automata_dup ta ++ states_of_ta_relation_dup rel;

create_renaming_main ::
  forall a.
    (Arith.Ccompare a,
      Eq a) => [a] ->
                 Integer ->
                   (Mapping.Mapping a Integer, [(Integer, a)]) ->
                     (Mapping.Mapping a Integer, [(Integer, a)]);
create_renaming_main [] i (qi, iq) = (qi, reverse iq);
create_renaming_main (q : qs) i (qi, iq) =
  (case Mapping.lookup qi q of {
    Nothing ->
      create_renaming_main qs (i + (1 :: Integer))
        (Mapping.update q i qi, (i, q) : iq);
    Just _ -> create_renaming_main qs i (qi, iq);
  });

create_renaming_of_states ::
  forall a.
    (Arith.Ccompare a, Eq a,
      Mapping.Mapping_impl a) => [a] -> (a -> Integer, [(Integer, a)]);
create_renaming_of_states qs =
  (case create_renaming_main qs (0 :: Integer) (Mapping.empty, []) of {
    (qi, a) -> ((\ q -> Arith.the (Mapping.lookup qi q)), a);
  });

rename_ta_rule ::
  forall a b c.
    (a -> b) -> Term_Rewriting.Ta_rule a c -> Term_Rewriting.Ta_rule b c;
rename_ta_rule ren (Term_Rewriting.TA_rule f qs q) =
  Term_Rewriting.TA_rule f (map ren qs) (ren q);

rename_tree_automaton ::
  forall a b c.
    (a -> b) ->
      Tree_Automata_Impl.Tree_automaton a c ->
        Tree_Automata_Impl.Tree_automaton b c;
rename_tree_automaton ren (Tree_Automata_Impl.Tree_Automaton qfin rules eps) =
  Tree_Automata_Impl.Tree_Automaton (map ren qfin)
    (map (rename_ta_rule ren) rules) (map (Arith.map_prod ren ren) eps);

rename_ta_relation ::
  forall a b.
    (a -> b) ->
      Tree_Automata_Impl.Ta_relation a -> Tree_Automata_Impl.Ta_relation b;
rename_ta_relation ren (Tree_Automata_Impl.Some_Relation rel) =
  Tree_Automata_Impl.Some_Relation (map (Arith.map_prod ren ren) rel);
rename_ta_relation ren Tree_Automata_Impl.Decision_Proc_Old =
  Tree_Automata_Impl.Decision_Proc_Old;
rename_ta_relation ren Tree_Automata_Impl.Decision_Proc =
  Tree_Automata_Impl.Decision_Proc;
rename_ta_relation ren Tree_Automata_Impl.Id_Relation =
  Tree_Automata_Impl.Id_Relation;

rename_bounds_info ::
  forall a b c. (a -> b) -> Bounds_info c a -> Bounds_info c b;
rename_bounds_info ren (Bounds_Info bt b qs ta rel) =
  Bounds_Info bt b (map ren qs) (rename_tree_automaton ren ta)
    (rename_ta_relation ren rel);

get_integer_bounds_info ::
  forall a b.
    (Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => Bounds_info a b ->
                                   (Bounds_info a Integer, [(Integer, b)]);
get_integer_bounds_info bi =
  (case create_renaming_of_states (states_of_bounds_info_dup bi) of {
    (qi, a) -> (rename_bounds_info qi bi, a);
  });

flatten_term_enum_filter ::
  forall a b.
    (Term_Rewriting.Term a b -> Bool) ->
      Term_Rewriting.Term [a] b -> [Term_Rewriting.Term a b];
flatten_term_enum_filter f (Term_Rewriting.Var x) =
  let {
    tx = Term_Rewriting.Var x;
  } in (if f tx then [tx] else []);
flatten_term_enum_filter f (Term_Rewriting.Fun fs ts) =
  let {
    lts = map (flatten_term_enum_filter f) ts;
  } in (if any null lts then []
         else let {
                ss = Missing_List.concat_lists lts;
              } in filter f
                     (concatMap (\ fa -> map (Term_Rewriting.Fun fa) ss) fs));

inverse_base_term_filter ::
  forall a b.
    (Term_Rewriting.Term (a, Arith.Nat) b -> Bool) ->
      Term_Rewriting.Term a b ->
        Arith.Nat -> [Term_Rewriting.Term (a, Arith.Nat) b];
inverse_base_term_filter filt l c =
  let {
    hs = Arith.upt Arith.zero_nat (Arith.suc c);
  } in flatten_term_enum_filter filt
         (Term_Rewriting.map_term (\ f -> map (\ h -> Matchbounds.lift h f) hs)
           (\ x -> x) l);

cover_bound_list_filter ::
  forall a b.
    (Eq a,
      Eq b) => (Term_Rewriting.Term (a, Arith.Nat) b -> Bool) ->
                 ((Term_Rewriting.Term a b, Term_Rewriting.Term a b) ->
                   Term_Rewriting.Term a b -> Bool) ->
                   Matchbounds.Relation_kind ->
                     Arith.Nat ->
                       [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                         [(Term_Rewriting.Term (a, Arith.Nat) b,
                            Term_Rewriting.Term (a, Arith.Nat) b)];
cover_bound_list_filter filt ff gg c r =
  concatMap
    (\ (l, ra) ->
      let {
        ch = Matchbounds.compute_height gg l ra;
        ee = ff (l, ra);
      } in map (\ la ->
                 (la, Term_Rewriting.map_term
                        (Matchbounds.lift
                          (ch la
                            (Missing_List.min_list
                              (map Matchbounds.height
                                (Matchbounds.sym_collect
                                  (\ t ->
                                    ee (Term_Rewriting.map_term Matchbounds.base
 (\ x -> x) t))
                                  la)))))
                        (\ x -> x) ra))
             (inverse_base_term_filter filt l c))
    r;

get_renaming_info ::
  forall a. (Shows_Literal.Showl a) => [(Integer, a)] -> String -> String;
get_renaming_info ren =
  let {
    fun = (\ (i, q) ->
            (Shows_Literal.showsl_integer i . Shows_Literal.showsl_lit ": ") .
              Shows_Literal.showsl q);
  } in ((Shows_Literal.showsl_lit
           "renaming information: the states in the certificate have been numbered as follows:\n\n" .
          Shows_Literal.showsl_sep fun (Shows_Literal.showsl_literal "\n")
            ren) .
         Shows_Literal.showsl_literal "\n") .
         Shows_Literal.showsl_literal "\n";

relation_as_list ::
  forall a.
    Tree_Automata_Impl.Ta_relation a ->
      Sum_Type.Sum (String -> String) [(a, a)];
relation_as_list (Tree_Automata_Impl.Some_Relation rel) = Sum_Type.Inr rel;
relation_as_list Tree_Automata_Impl.Id_Relation = Sum_Type.Inr [];
relation_as_list Tree_Automata_Impl.Decision_Proc =
  Sum_Type.Inl
    (Shows_Literal.showsl_lit
      "decision procedure not available for non-left linear TRSs");
relation_as_list Tree_Automata_Impl.Decision_Proc_Old =
  Sum_Type.Inl
    (Shows_Literal.showsl_lit
      "decision procedure not available for non-left linear TRSs");

check_ta_bounded ::
  forall a b.
    (Quasi_Order.Linorder b,
      Shows_Literal.Showl b) => Tree_Automata_Impl.Ta_impl a (b, Arith.Nat) ->
                                  Arith.Nat ->
                                    Sum_Type.Sum (String -> String) ();
check_ta_bounded ta c =
  Error_Monad.catch_error
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ x ->
          (if (case x of {
                (f, _) -> Arith.less_eq_nat (Matchbounds.height f) c;
              })
            then Sum_Type.Inr () else Sum_Type.Inl x))
        (map fst
          (RBTMapImpl.g_to_list_rm_basic_ops
            (Tree_Automata_Impl.ta_rules_impl ta))))
      (\ x -> Sum_Type.Inl (snd x)))
    (\ x ->
      Sum_Type.Inl
        (case x of {
          (f, _) ->
            (Shows_Literal.showsl_prod f .
              Shows_Literal.showsl_lit
                " is symbol in TA with height larger than c = ") .
              Shows_Literal.showsl_nat c;
        }));

bounds_condition ::
  forall a b.
    (Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => Boundstype ->
                                  [(Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b)] ->
                                    Sum_Type.Sum (String -> String) ();
bounds_condition Roof uu = Sum_Type.Inr ();
bounds_condition Match r =
  Error_Monad.catch_error
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ x ->
          (if (case x of {
                (l, ra) ->
                  Multiset.subseteq_mset (Term_Rewriting.vars_term_ms ra)
                    (Term_Rewriting.vars_term_ms l);
              })
            then Sum_Type.Inr () else Sum_Type.Inl x))
        r)
      (\ x -> Sum_Type.Inl (snd x)))
    (\ x ->
      Sum_Type.Inl
        (case x of {
          (l, ra) ->
            (Shows_Literal.showsl_lit "rule " .
              Term_Rewriting.showsl_rule (l, ra)) .
              Shows_Literal.showsl_lit " is duplicating";
        }));

construct_c_opt ::
  forall a b.
    Arith.Nat ->
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] -> Maybe Arith.Nat;
construct_c_opt c r =
  (if Term_Rewriting.non_collapsing_impl r then Just c else Nothing);

boundstype_fun ::
  forall a b.
    (Arith.Ceq b, Arith.Ccompare b,
      Arith.Set_impl b) => Boundstype ->
                             (Term_Rewriting.Term a b,
                               Term_Rewriting.Term a b) ->
                               Term_Rewriting.Term a b -> Bool;
boundstype_fun Roof = Matchbounds.roof;
boundstype_fun Match = Matchbounds.match;

check_bounds_generic ::
  forall a b c.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a, Arith.Ccompare b,
      Eq b, Mapping.Mapping_impl b, Quasi_Order.Linorder b,
      Shows_Literal.Showl b, Arith.Ceq c, Arith.Ccompare c,
      Compare.Compare_order c, Eq c, Arith.Set_impl c,
      Shows_Literal.Showl c) => Bounds_info a b ->
                                  [(Term_Rewriting.Term a c,
                                     Term_Rewriting.Term a c)] ->
                                    [(Term_Rewriting.Term a c,
                                       Term_Rewriting.Term a c)] ->
                                      [(a, Arith.Nat)] ->
[(a, Arith.Nat)] -> Sum_Type.Sum (String -> String) ();
check_bounds_generic bi r s f g =
  (case get_integer_bounds_info bi of {
    (Bounds_Info typea c qfin preTA rel, ren) ->
      Error_Monad.catch_error
        (let {
           c_opt = construct_c_opt c r;
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
                               (Shows_Literal.showsl_lit
                                 "explicitly mentioned final states must be final"))
                             (\ _ ->
                               Error_Monad.bind
                                 (if Error_Monad.isOK
                                       (Term_Rewriting.check_left_linear_trs rs)
                                   then Sum_Type.Inr ()
                                   else Error_Monad.bind
  (Error_Monad.catch_error (Tree_Automata_Impl.check_det preTA)
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "for non left-linear TRS we require det. automaton\n" .
          x)))
  (\ _ ->
    Error_Monad.bind (relation_as_list rel)
      (check_state_raise_consistent preTA)))
                                 (\ _ ->
                                   Error_Monad.bind (bounds_condition typea rs)
                                     (\ _ ->
                                       Error_Monad.bind (check_ta_bounded ta c)
 (\ _ ->
   Error_Monad.bind
     (Check_Monad.check
       (any (\ q ->
              RBTSetImpl.memb_rm_basic_ops q
                (Tree_Automata_Impl.ta_rhs_states_set ta))
         qfin)
       (Shows_Literal.showsl_lit "did not find mentioned final state in TA"))
     (\ _ ->
       Error_Monad.bind
         (Error_Monad.catch_error
           (Tree_Automata_Impl.ta_contains_impl
             (map (\ (fa, a) -> (Matchbounds.lift Arith.zero_nat fa, a)) f)
             (map (\ (fa, a) -> (Matchbounds.lift Arith.zero_nat fa, a)) g) ta
             qfin)
           (\ x ->
             Sum_Type.Inl
               (Shows_Literal.showsl_lit
                  "it could not be guaranteed that lift0(T(Sigma)) is accepted by TA\n" .
                 (Shows_Literal.showsl_lit "there is no transition from " .
                   Term_Rewriting.showsl_terma x) .
                   Shows_Literal.showsl_lit " to a final state")))
         (\ _ ->
           Error_Monad.bind
             (Error_Monad.catch_error
               (Tree_Automata_Impl.state_compatible_eff_list ta rell
                 (cover_bound_list_filter
                   (\ l ->
                     not (Tree_Automata_Impl.rule_state_compatible_heuristic ta
                           l))
                   (boundstype_fun typea) Matchbounds.Strict_TRS c r))
               (\ x ->
                 Sum_Type.Inl
                   (case x of {
                     (lr, (lr_rhs, q)) ->
                       ((((((Shows_Literal.showsl_lit
                               "TA is not compatible with TRS\n" .
                              Shows_Literal.showsl_lit "for rule ") .
                             Term_Rewriting.showsl_rule lr) .
                            Shows_Literal.showsl_lit
                              "\nwhich is instantiated by states to ") .
                           Term_Rewriting.showsl_rule lr_rhs) .
                          Shows_Literal.showsl_lit "\nthe state ") .
                         Shows_Literal.showsl_integer q) .
                         Shows_Literal.showsl_lit
                           " is only reachable from the lhs\n";
                   })))
             (\ _ ->
               Error_Monad.catch_error
                 (Tree_Automata_Impl.state_compatible_eff_list ta rell
                   (cover_bound_list_filter
                     (\ l ->
                       not (Tree_Automata_Impl.rule_state_compatible_heuristic
                             ta l))
                     Matchbounds.match (Matchbounds.Weak_TRS c_opt) c s))
                 (\ x ->
                   Sum_Type.Inl
                     (case x of {
                       (lr, (lr_rhs, q)) ->
                         ((((((Shows_Literal.showsl_lit
                                 "TA is not compatible with relative TRS\n" .
                                Shows_Literal.showsl_lit "for rule ") .
                               Term_Rewriting.showsl_rule lr) .
                              Shows_Literal.showsl_lit
                                "\nwhich is instantiated by states to ") .
                             Term_Rewriting.showsl_rule lr_rhs) .
                            Shows_Literal.showsl_lit "\nthe state ") .
                           Shows_Literal.showsl_integer q) .
                           Shows_Literal.showsl_lit
                             " is only reachable from the lhs\n";
                     }))))))))))))
        (\ x ->
          Sum_Type.Inl
            (((Shows_Literal.showsl_lit
                 "problem during checking bounds of automaton\n" .
                get_renaming_info ren) .
               Shows_Literal.showsl_lit "\nerror:\n") .
              x));
  });

bounds_tt ::
  forall a b c d.
    (Compare.Compare_order b, Eq b, Shows_Literal.Showl b, Arith.Ceq c,
      Arith.Ccompare c, Compare.Compare_order c, Eq c, Arith.Set_impl c,
      Shows_Literal.Showl c, Arith.Ccompare d, Eq d, Mapping.Mapping_impl d,
      Quasi_Order.Linorder d,
      Shows_Literal.Showl d) => Termination_Problem_Spec.Tp_ops_ext a b c () ->
                                  Bounds_info b d ->
                                    a -> Sum_Type.Sum (String -> String) ();
bounds_tt i info tp = let {
                        r = Termination_Problem_Spec.rules i tp;
                        f = Term_Rewriting.funas_trs_list r;
                      } in check_bounds_generic info r [] f f;

equal_boundstype :: Boundstype -> Boundstype -> Bool;
equal_boundstype Roof Match = False;
equal_boundstype Match Roof = False;
equal_boundstype Match Match = True;
equal_boundstype Roof Roof = True;

boundstype :: forall a b. Bounds_info a b -> Boundstype;
boundstype (Bounds_Info x1 x2 x3 x4 x5) = x1;

bounds_complexity ::
  forall a b c d.
    (Compare.Compare_order b, Eq b, Shows_Literal.Showl b, Arith.Ceq c,
      Arith.Ccompare c, Compare.Compare_order c, Eq c, Arith.Set_impl c,
      Shows_Literal.Showl c, Arith.Ccompare d, Eq d, Mapping.Mapping_impl d,
      Quasi_Order.Linorder d,
      Shows_Literal.Showl d) => Termination_Problem_Spec.Tp_ops_ext a b c () ->
                                  Bounds_info b d ->
                                    Complexity.Complexity_measure b c ->
                                      Complexity.Complexity_class ->
a -> Sum_Type.Sum (String -> String) ();
bounds_complexity i info cm cc tp =
  Error_Monad.catch_error
    (Error_Monad.bind
      (Check_Monad.check
        (Complexity.less_eq_complexity_class
          (Complexity.Comp_Poly Arith.one_nat) cc)
        (Shows_Literal.showsl_lit "can only ensure linear complexity"))
      (\ _ ->
        Error_Monad.bind
          (Check_Monad.check (equal_boundstype (boundstype info) Match)
            (Shows_Literal.showsl_lit
              "complexity analysis requires boundstype match"))
          (\ _ ->
            check_bounds_generic info (Termination_Problem_Spec.rules i tp) []
              (Matchbounds.stackable_of_cm cm) (Matchbounds.roots_of_cm cm))))
    (\ x ->
      Sum_Type.Inl
        (((Shows_Literal.showsl_lit
             "problem in ensuring match boundedness of\n" .
            QDP_Framework_Impl.showsl_tp i tp) .
           Shows_Literal.showsl_literal "\n") .
          x));

bounds_complexity_rel ::
  forall a b c d.
    (Compare.Compare_order b, Eq b, Shows_Literal.Showl b, Arith.Ceq c,
      Arith.Ccompare c, Compare.Compare_order c, Eq c, Arith.Set_impl c,
      Shows_Literal.Showl c, Arith.Ccompare d, Eq d, Mapping.Mapping_impl d,
      Quasi_Order.Linorder d,
      Shows_Literal.Showl d) => Termination_Problem_Spec.Tp_ops_ext a b c () ->
                                  Bounds_info b d ->
                                    [(Term_Rewriting.Term b c,
                                       Term_Rewriting.Term b c)] ->
                                      Complexity.Complexity_measure b c ->
Complexity.Complexity_class -> a -> Sum_Type.Sum (String -> String) a;
bounds_complexity_rel i info rdelete cm cc tp =
  Error_Monad.catch_error
    (let {
       r = Termination_Problem_Spec.r i tp;
       rw = Termination_Problem_Spec.rw i tp;
       r2 = Map_Choice.ceta_list_diff r rdelete;
     } in Error_Monad.bind
            (Error_Monad.catch_error
              (Check_Monad.check_subseteq rdelete
                (Termination_Problem_Spec.rules i tp))
              (\ x ->
                Sum_Type.Inl
                  ((Shows_Literal.showsl_lit "could not find rule " .
                     Term_Rewriting.showsl_rule x) .
                    Shows_Literal.showsl_lit " in current complexity problem")))
            (\ _ ->
              Error_Monad.bind
                (Check_Monad.check
                  (Complexity.less_eq_complexity_class
                    (Complexity.Comp_Poly Arith.one_nat) cc)
                  (Shows_Literal.showsl_lit
                    "can only ensure linear complexity"))
                (\ _ ->
                  Error_Monad.bind
                    (Check_Monad.check
                      (equal_boundstype (boundstype info) Match)
                      (Shows_Literal.showsl_lit
                        "complexity analysis requires boundstype match"))
                    (\ _ ->
                      let {
                        _ = Termination_Problem_Spec.rules i tp;
                      } in Error_Monad.bind
                             (check_bounds_generic info rdelete (rw ++ r2)
                               (Matchbounds.stackable_of_cm cm)
                               (Matchbounds.roots_of_cm cm))
                             (\ _ ->
                               Sum_Type.Inr
                                 (Termination_Problem_Spec.mk i
                                   (Termination_Problem_Spec.nfs i tp)
                                   (Termination_Problem_Spec.q i tp) r2
                                   (Missing_List.list_union rw rdelete)))))))
    (\ x ->
      Sum_Type.Inl
        ((((Shows_Literal.showsl_lit
              "problem in ensuring match-RT boundedness of\n" .
             QDP_Framework_Impl.showsl_tp i tp) .
            Shows_Literal.showsl_lit "\nwith deletion of rules\n") .
           Term_Rewriting.showsl_trs rdelete) .
          x));

}
