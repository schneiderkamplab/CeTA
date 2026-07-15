{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Ordered_Completion_Impl(Oc_irule(..), Reduction_order_input(..),
                           Ordered_completion_proof(..), Redord_closure_ext,
                           check_ordered_completion_proof_ext,
                           check_equational_disproof_oc,
                           check_equational_disproof_by_ground_complete_system)
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
import qualified Map;
import qualified Partitions;
import qualified Fresh;
import qualified Abstract_Rewriting_Impl;
import qualified Quasi_Order;
import qualified KBO_More;
import qualified KBO_Impl;
import qualified FOR_Preliminaries;
import qualified Equational_Reasoning_Impl;
import qualified Trs_Impl_More;
import qualified HOL;
import qualified Check_Monad;
import qualified Reduction_Order_Impl;
import qualified Compare;
import qualified List_Lexorder;
import qualified Lists_are_Infinite;
import qualified Error_Monad;
import qualified Mapping;
import qualified Strict_Sum;
import qualified Sum_Type;
import qualified WPO;
import qualified Arith;
import qualified Term_Rewriting;

data Oc_irule a b =
  OC_Deduce (Term_Rewriting.Term a b) (Term_Rewriting.Term a b)
    (Term_Rewriting.Term a b)
  | OC_Orientl (Term_Rewriting.Term a b) (Term_Rewriting.Term a b)
  | OC_Orientr (Term_Rewriting.Term a b) (Term_Rewriting.Term a b)
  | OC_Delete (Term_Rewriting.Term a b)
  | OC_Compose (Term_Rewriting.Term a b) (Term_Rewriting.Term a b)
      (Term_Rewriting.Term a b)
  | OC_Simplifyl (Term_Rewriting.Term a b) (Term_Rewriting.Term a b)
      (Term_Rewriting.Term a b)
  | OC_Simplifyr (Term_Rewriting.Term a b) (Term_Rewriting.Term a b)
      (Term_Rewriting.Term a b)
  | OC_Collapse (Term_Rewriting.Term a b) (Term_Rewriting.Term a b)
      (Term_Rewriting.Term a b);

data Reduction_order_input a =
  RPO_Input [((a, Arith.Nat), (Arith.Nat, WPO.Order_tag))]
  | KBO_Input
      ([((a, Arith.Nat), (Arith.Nat, (Arith.Nat, Maybe [Arith.Nat])))],
        Arith.Nat);

newtype Ordered_completion_proof a b = OKB [Oc_irule a b];

data Redord_closure_ext a b c =
  Redord_closure_ext
    ([b] -> Term_Rewriting.Term a b -> Term_Rewriting.Term a b -> Bool)
    (Sum_Type.Sum (String -> String) ()) c;

lift :: forall a. Sum_Type.Sum a () -> Strict_Sum.Sum_bot a ();
lift c = (case c of {
           Sum_Type.Inl a -> Strict_Sum.errora a;
           Sum_Type.Inr a -> Strict_Sum.returna a;
         });

sym_list :: forall a. (Eq a) => [(a, a)] -> [(a, a)];
sym_list xs = Arith.union xs (map (\ (x, y) -> (y, x)) xs);

rules :: forall a. (Eq a) => [(a, a)] -> [(a, a)] -> [(a, a)];
rules e r = Arith.union r (sym_list e);

inserts :: forall a. a -> [a] -> [[a]];
inserts x [] = [[x]];
inserts x (y : ys) = (x : y : ys) : map (\ a -> y : a) (inserts x ys);

perms :: forall a. [a] -> [[a]];
perms [] = [[]];
perms (x : xs) = concatMap (inserts x) (perms xs);

check_rstep_p ::
  forall a b c.
    (Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => (Term_Rewriting.Term a b ->
                                   Term_Rewriting.Term a b ->
                                     Sum_Type.Sum (String -> String) c) ->
                                   (Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b) ->
                                     [Arith.Nat] ->
                                       Term_Rewriting.Term a b ->
 Term_Rewriting.Term a b -> Sum_Type.Sum (String -> String) c;
check_rstep_p c rho p s t =
  (if not (Arith.membera (Term_Rewriting.poss_list t) p)
    then Sum_Type.Inl
           (Term_Rewriting.showsl_literal "no step possible at this position")
    else (case rho of {
           (l, r) ->
             (case Term_Rewriting.match_list Term_Rewriting.Var
                     [(l, Term_Rewriting.subt_at s p),
                       (r, Term_Rewriting.subt_at t p)]
               of {
               Nothing ->
                 Sum_Type.Inl
                   (Term_Rewriting.showsl_literal "rule does not match");
               Just sigma ->
                 (if Term_Rewriting.equal_term t
                       (Term_Rewriting.intp_actxt Term_Rewriting.Fun
                         (Term_Rewriting.ctxt_of_pos_term p s)
                         (Term_Rewriting.eval_term Term_Rewriting.Fun r sigma))
                   then c (Term_Rewriting.eval_term Term_Rewriting.Fun l sigma)
                          (Term_Rewriting.eval_term Term_Rewriting.Fun r sigma)
                   else Sum_Type.Inl
                          (Term_Rewriting.showsl_literal
                            "result does not match"));
             });
         }));

check_step_rule ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Term_Rewriting.Showl b) => (Term_Rewriting.Term a b ->
                                   Term_Rewriting.Term a b ->
                                     Sum_Type.Sum (String -> String) ()) ->
                                   (Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b) ->
                                     Term_Rewriting.Term a b ->
                                       Term_Rewriting.Term a b ->
 Sum_Type.Sum (String -> String) ();
check_step_rule c rho s t =
  Error_Monad.catch_error
    (Error_Monad.existsM (\ p -> check_rstep_p c rho p s t)
      (Term_Rewriting.poss_list s))
    (\ _ ->
      Sum_Type.Inl
        (((Term_Rewriting.showsl_lit " is not a reduct with respect to " .
            Term_Rewriting.showsl_terma (fst rho)) .
           Term_Rewriting.showsl_lit " -> ") .
          Term_Rewriting.showsl_terma (snd rho)));

check_step ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Term_Rewriting.Showl b) => (Term_Rewriting.Term a b ->
                                   Term_Rewriting.Term a b ->
                                     Sum_Type.Sum (String -> String) ()) ->
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)] ->
                                     Term_Rewriting.Term a b ->
                                       Term_Rewriting.Term a b ->
 Sum_Type.Sum (String -> String) ();
check_step c [] s t =
  Sum_Type.Inl
    ((((Term_Rewriting.showsl_lit "no step from " .
         Term_Rewriting.showsl_terma s) .
        Term_Rewriting.showsl_lit " to ") .
       Term_Rewriting.showsl_terma t) .
      Term_Rewriting.showsl_lit " found\n");
check_step c (ea : e) s t =
  Error_Monad.catch_error
    (Error_Monad.choice [check_step_rule c ea s t, check_step c e s t])
    (\ x ->
      Sum_Type.Inl
        (Term_Rewriting.showsl_sep id (Term_Rewriting.showsl_literal "\n") x));

choice_bot :: forall a b. [Strict_Sum.Sum_bot a b] -> Strict_Sum.Sum_bot [a] b;
choice_bot [] = Strict_Sum.errora [];
choice_bot (x : xs) =
  Strict_Sum.catch_error x
    (\ e ->
      Strict_Sum.catch_error (choice_bot xs)
        (\ ea -> Strict_Sum.errora (e : ea)));

existsM_bot ::
  forall a b.
    (a -> Strict_Sum.Sum_bot b ()) -> [a] -> Strict_Sum.Sum_bot [b] ();
existsM_bot f [] = Strict_Sum.errora [];
existsM_bot f (x : xs) =
  Strict_Sum.catch_error (f x)
    (\ e ->
      Strict_Sum.catch_error (existsM_bot f xs)
        (\ ea -> Strict_Sum.errora (e : ea)));

forallM_bot ::
  forall a b.
    (a -> Strict_Sum.Sum_bot b ()) -> [a] -> Strict_Sum.Sum_bot (a, b) ();
forallM_bot f [] = Strict_Sum.returna ();
forallM_bot f (x : xs) =
  Strict_Sum.bind
    (Strict_Sum.catch_error (f x) (\ e -> Strict_Sum.errora (x, e)))
    (\ _ -> forallM_bot f xs);

precw_w0_sig :: forall a b c. ([(a, b)], c) -> [a];
precw_w0_sig precw_w0 = map fst (fst precw_w0);

ext_subst ::
  forall a b c d.
    (Term_Rewriting.Showl a,
      Eq b) => a -> (b -> Term_Rewriting.Term a c) ->
                      Term_Rewriting.Term d b -> b -> Term_Rewriting.Term a c;
ext_subst least sigma l =
  (\ x ->
    (if Arith.membera (Term_Rewriting.insert_vars_term l []) x then sigma x
      else Term_Rewriting.Fun least []));

mord_rewrite ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Term_Rewriting.Showl b) => (Term_Rewriting.Term a b ->
                                   Term_Rewriting.Term a b -> Bool) ->
                                   a -> [(Term_Rewriting.Term a b,
   Term_Rewriting.Term a b)] ->
  Term_Rewriting.Term a b -> [Term_Rewriting.Term a b];
mord_rewrite check_ord least r s =
  concatMap
    (\ (l, ra) ->
      concatMap
        (\ p ->
          (case Term_Rewriting.match (Term_Rewriting.subt_at s p) l of {
            Nothing -> [];
            Just sigma ->
              let {
                sigmaa = ext_subst least sigma l;
              } in (if check_ord
                         (Term_Rewriting.eval_term Term_Rewriting.Fun l sigmaa)
                         (Term_Rewriting.eval_term Term_Rewriting.Fun ra sigmaa)
                     then [Term_Rewriting.intp_actxt Term_Rewriting.Fun
                             (Term_Rewriting.ctxt_of_pos_term p s)
                             (Term_Rewriting.eval_term Term_Rewriting.Fun ra
                               sigmaa)]
                     else []);
          }))
        (Term_Rewriting.poss_list s))
    r;

first_mord_rewrite ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Term_Rewriting.Showl b) => (Term_Rewriting.Term a b ->
                                   Term_Rewriting.Term a b -> Bool) ->
                                   a -> [(Term_Rewriting.Term a b,
   Term_Rewriting.Term a b)] ->
  Term_Rewriting.Term a b -> Maybe (Term_Rewriting.Term a b);
first_mord_rewrite check_ord least r s =
  (case mord_rewrite check_ord least r s of {
    [] -> Nothing;
    t : _ -> Just t;
  });

compute_mordstep_NF ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Term_Rewriting.Showl b) => (Term_Rewriting.Term a b ->
                                   Term_Rewriting.Term a b -> Bool) ->
                                   a -> [(Term_Rewriting.Term a b,
   Term_Rewriting.Term a b)] ->
  Term_Rewriting.Term a b -> Maybe (Term_Rewriting.Term a b);
compute_mordstep_NF check_ord least r s =
  Abstract_Rewriting_Impl.compute_NF (first_mord_rewrite check_ord least r) s;

check_instance_joinable ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Term_Rewriting.Showl b) => (Term_Rewriting.Term a b ->
                                   Term_Rewriting.Term a b -> Bool) ->
                                   a -> [(Term_Rewriting.Term a b,
   Term_Rewriting.Term a b)] ->
  [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
    Term_Rewriting.Term a b ->
      Term_Rewriting.Term a b -> Sum_Type.Sum (String -> String) ();
check_instance_joinable check_ord least e r s t =
  (case (compute_mordstep_NF check_ord least (e ++ r) s,
          compute_mordstep_NF check_ord least (e ++ r) t)
    of {
    (Nothing, _) ->
      Sum_Type.Inl
        (Term_Rewriting.showsl_literal "error: check_instance_joinable");
    (Just _, Nothing) ->
      Sum_Type.Inl
        (Term_Rewriting.showsl_literal "error: check_instance_joinable");
    (Just u, Just v) ->
      Error_Monad.catch_error
        (Error_Monad.choice
          [Check_Monad.check (Term_Rewriting.equal_term u v)
             (Term_Rewriting.showsl_lit "normal forms differ"),
            check_step (\ _ _ -> Sum_Type.Inr ()) e u v])
        (\ x ->
          Sum_Type.Inl
            (Term_Rewriting.showsl_sep id (Term_Rewriting.showsl_literal "\n")
              x));
  });

check_var_order_joinable ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Arith.Ccompare b, Fresh.Infinite b, Eq b,
      Mapping.Mapping_impl b, Quasi_Order.Linorder b,
      Term_Rewriting.Showl b) => a -> ([b] ->
Term_Rewriting.Term a b -> Term_Rewriting.Term a b -> Bool) ->
[(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
  [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
    Term_Rewriting.Term a b ->
      Term_Rewriting.Term a b -> [b] -> Sum_Type.Sum (String -> String) ();
check_var_order_joinable least ext_check_ord e r s t vperm =
  check_instance_joinable (ext_check_ord vperm) least e r s t;

var_tuples_of_partitioning ::
  forall a.
    (Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a, Eq a,
      Quasi_Order.Linorder a) => [Arith.Set a] -> [(a, a)];
var_tuples_of_partitioning ps =
  concatMap (\ p -> (case Arith.sorted_list_of_set p of {
                      [] -> [];
                      x : xs -> map (\ y -> (y, x)) (x : xs);
                    }))
    (Arith.remdups ps);

var_subst_of_partitioning ::
  forall a.
    (Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a, Eq a,
      Quasi_Order.Linorder a) => [Arith.Set a] -> a -> a;
var_subst_of_partitioning p =
  (\ x -> (case Map.map_of (var_tuples_of_partitioning p) x of {
            Nothing -> x;
            Just y -> y;
          }));

subst_of_partitioning ::
  forall a b.
    (Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a, Eq a,
      Quasi_Order.Linorder a) => [Arith.Set a] -> a -> Term_Rewriting.Term b a;
subst_of_partitioning p =
  (\ x -> Term_Rewriting.Var (var_subst_of_partitioning p x));

check_var_orders_joinable ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Arith.Cenum b, Arith.Ceq b, Arith.Ccompare b,
      Fresh.Infinite b, Eq b, Mapping.Mapping_impl b, Quasi_Order.Linorder b,
      Arith.Set_impl b,
      Term_Rewriting.Showl b) => a -> ([b] ->
Term_Rewriting.Term a b -> Term_Rewriting.Term a b -> Bool) ->
[(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
  [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
    Term_Rewriting.Term a b ->
      Term_Rewriting.Term a b -> Sum_Type.Sum (String -> String) ();
check_var_orders_joinable least ext_check_ord e r s t =
  let {
    xs = Arith.remdups (Term_Rewriting.insert_vars_rule (s, t) []);
  } in Error_Monad.catch_error
         (Error_Monad.forallM
           (\ ps ->
             let {
               sigma = subst_of_partitioning ps;
             } in (case (Term_Rewriting.eval_term Term_Rewriting.Fun s sigma,
                          Term_Rewriting.eval_term Term_Rewriting.Fun t sigma)
                    of {
                    (sa, ta) ->
                      let {
                        orders =
                          perms (Arith.remdups
                                  (Term_Rewriting.insert_vars_rule (sa, ta)
                                    []));
                      } in Error_Monad.catch_error
                             (Error_Monad.forallM
                               (check_var_order_joinable least ext_check_ord e r
                                 sa ta)
                               orders)
                             (\ x -> Sum_Type.Inl (snd x));
                  }))
           (Partitions.all_partitions_list xs))
         (\ x -> Sum_Type.Inl (snd x));

check_rule_instance ::
  forall a b.
    (Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => (Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b) ->
                                   (Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b) ->
                                     Sum_Type.Sum (String -> String) ();
check_rule_instance ra r =
  (case Term_Rewriting.match_list Term_Rewriting.Var
          [(fst r, fst ra), (snd r, snd ra)]
    of {
    Nothing -> Sum_Type.Inl (Term_Rewriting.showsl_lit "rules do not match");
    Just _ -> Sum_Type.Inr ();
  });

check_instance ::
  forall a b.
    (Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => [(Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b)] ->
                                   Term_Rewriting.Term a b ->
                                     Term_Rewriting.Term a b ->
                                       Sum_Type.Sum (String -> String) ();
check_instance e s t =
  Error_Monad.catch_error (Error_Monad.existsM (check_rule_instance (s, t)) e)
    (\ x ->
      Sum_Type.Inl
        (Term_Rewriting.showsl_sep id (Term_Rewriting.showsl_literal "\n") x));

check_ground_join_rel_bot ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Arith.Cenum b, Arith.Ceq b, Arith.Ccompare b,
      Fresh.Infinite b, Eq b, Mapping.Mapping_impl b, Quasi_Order.Linorder b,
      Arith.Set_impl b,
      Term_Rewriting.Showl b) => (Term_Rewriting.Term a b ->
                                   Term_Rewriting.Term a b -> Bool) ->
                                   a -> ([b] ->
  Term_Rewriting.Term a b -> Term_Rewriting.Term a b -> Bool) ->
  [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
    [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
      Term_Rewriting.Term a b ->
        Term_Rewriting.Term a b -> Strict_Sum.Sum_bot (String -> String) ();
check_ground_join_rel_bot check_ord least ext_check_ord e r s t =
  (case (s, t) of {
    (Term_Rewriting.Var x, _) ->
      Strict_Sum.catch_error
        (choice_bot
          [lift (Check_Monad.check
                  (Term_Rewriting.equal_term (Term_Rewriting.Var x) t)
                  (Term_Rewriting.showsl_lit "The terms are different.")),
            Strict_Sum.catch_error
              (existsM_bot
                (check_ground_join_rel_bot check_ord least ext_check_ord e r
                  (Term_Rewriting.Var x))
                (mord_rewrite check_ord least (e ++ r) t))
              (\ _ ->
                Strict_Sum.errora
                  (Term_Rewriting.showsl_lit "No right-rewrite is possible."))])
        (\ ea ->
          Strict_Sum.errora
            (Term_Rewriting.showsl_sep id (Term_Rewriting.showsl_literal "\n")
              ea));
    (Term_Rewriting.Fun _ _, Term_Rewriting.Var x) ->
      Strict_Sum.catch_error
        (choice_bot
          [lift (Check_Monad.check
                  (Term_Rewriting.equal_term (Term_Rewriting.Var x) s)
                  (Term_Rewriting.showsl_lit "The terms are different.")),
            Strict_Sum.catch_error
              (existsM_bot
                (\ u ->
                  check_ground_join_rel_bot check_ord least ext_check_ord e r u
                    (Term_Rewriting.Var x))
                (mord_rewrite check_ord least (e ++ r) s))
              (\ _ ->
                Strict_Sum.errora
                  (Term_Rewriting.showsl_lit "No left-rewrite is possible."))])
        (\ ea ->
          Strict_Sum.errora
            (Term_Rewriting.showsl_sep id (Term_Rewriting.showsl_literal "\n")
              ea));
    (Term_Rewriting.Fun f ss, Term_Rewriting.Fun g ts) ->
      Strict_Sum.catch_error
        (choice_bot
          [lift (Check_Monad.check
                  (Term_Rewriting.equal_term (Term_Rewriting.Fun f ss)
                    (Term_Rewriting.Fun g ts))
                  (Term_Rewriting.showsl_lit "terms differ")),
            lift (check_instance (e ++ r) (Term_Rewriting.Fun f ss)
                   (Term_Rewriting.Fun g ts)),
            Strict_Sum.catch_error
              (existsM_bot
                (\ u ->
                  check_ground_join_rel_bot check_ord least ext_check_ord e r u
                    (Term_Rewriting.Fun g ts))
                (mord_rewrite check_ord least (e ++ r)
                  (Term_Rewriting.Fun f ss)))
              (\ _ ->
                Strict_Sum.errora
                  (Term_Rewriting.showsl_literal
                    "No left-rewrite is possible.")),
            Strict_Sum.catch_error
              (existsM_bot
                (check_ground_join_rel_bot check_ord least ext_check_ord e r
                  (Term_Rewriting.Fun f ss))
                (mord_rewrite check_ord least (e ++ r)
                  (Term_Rewriting.Fun g ts)))
              (\ _ ->
                Strict_Sum.errora
                  (Term_Rewriting.showsl_literal
                    "No right-rewrite is possible.")),
            (if f == g &&
                  Arith.equal_nat (Arith.size_list ss) (Arith.size_list ts)
              then Strict_Sum.catch_error
                     (forallM_bot
                       (\ (a, b) ->
                         check_ground_join_rel_bot check_ord least ext_check_ord
                           e r a b)
                       (zip ss ts))
                     (\ _ ->
                       Strict_Sum.errora
                         (Term_Rewriting.showsl_literal
                           "Arguments are not ground-joinable."))
              else Strict_Sum.errora
                     (Term_Rewriting.showsl_literal
                       "The congruence rule does not apply.")),
            lift (check_var_orders_joinable least ext_check_ord e r
                   (Term_Rewriting.Fun f ss) (Term_Rewriting.Fun g ts))])
        (\ ea ->
          Strict_Sum.errora
            (Term_Rewriting.showsl_sep id (Term_Rewriting.showsl_literal "\n")
              ea));
  });

check_ground_join_rel ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Arith.Cenum b, Arith.Ceq b, Arith.Ccompare b,
      Fresh.Infinite b, Eq b, Mapping.Mapping_impl b, Quasi_Order.Linorder b,
      Arith.Set_impl b,
      Term_Rewriting.Showl b) => (Term_Rewriting.Term a b ->
                                   Term_Rewriting.Term a b -> Bool) ->
                                   a -> ([b] ->
  Term_Rewriting.Term a b -> Term_Rewriting.Term a b -> Bool) ->
  [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
    [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
      Term_Rewriting.Term a b ->
        Term_Rewriting.Term a b -> Sum_Type.Sum (String -> String) ();
check_ground_join_rel check_ord least ext_check_ord e r s t =
  Strict_Sum.case_sum_bot
    (Sum_Type.Inl
      (Term_Rewriting.showsl_literal
        "Ground joinability could not be established."))
    (\ _ ->
      Sum_Type.Inl
        ((((Term_Rewriting.showsl_lit "The equation " .
             Term_Rewriting.showsl_terma s) .
            Term_Rewriting.showsl_lit " = ") .
           Term_Rewriting.showsl_terma t) .
          Term_Rewriting.showsl_lit " is not ground joinable\n"))
    Sum_Type.Inr
    (check_ground_join_rel_bot check_ord least ext_check_ord e r s t);

check_ooverlap_gj ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Arith.Cenum b, Arith.Ceq b, Arith.Ccompare b,
      Fresh.Infinite b, Eq b, Mapping.Mapping_impl b, Quasi_Order.Linorder b,
      Arith.Set_impl b,
      Term_Rewriting.Showl b) => (Term_Rewriting.Term a b ->
                                   Term_Rewriting.Term a b -> Bool) ->
                                   a -> (b -> b) ->
  (b -> b) ->
    ([b] -> Term_Rewriting.Term a b -> Term_Rewriting.Term a b -> Bool) ->
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
        [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
          (Term_Rewriting.Term a b, Term_Rewriting.Term a b) ->
            (Term_Rewriting.Term a b, Term_Rewriting.Term a b) ->
              [Arith.Nat] -> Sum_Type.Sum (String -> String) ();
check_ooverlap_gj check_ord least xvar yvar ext_check_ord e r rho_1 rho_2 p =
  (case Term_Rewriting.mgu_var_disjoint_generic xvar yvar (fst rho_1)
          (Term_Rewriting.subt_at (fst rho_2) p)
    of {
    Nothing -> Sum_Type.Inr ();
    Just (sigma_1, sigma_2) ->
      let {
        s = Term_Rewriting.intp_actxt Term_Rewriting.Fun
              (Term_Rewriting.ctxt_of_pos_term p
                (Term_Rewriting.eval_term Term_Rewriting.Fun (fst rho_2)
                  sigma_2))
              (Term_Rewriting.eval_term Term_Rewriting.Fun (snd rho_1) sigma_1);
        a = Term_Rewriting.eval_term Term_Rewriting.Fun (snd rho_2) sigma_2;
      } in check_ground_join_rel check_ord least ext_check_ord e r s a;
  });

check_ECPs_gj ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Arith.Cenum b, Arith.Ceq b, Arith.Ccompare b,
      Fresh.Infinite b, Eq b, Mapping.Mapping_impl b, Quasi_Order.Linorder b,
      Arith.Set_impl b,
      Term_Rewriting.Showl b) => (Term_Rewriting.Term a b ->
                                   Term_Rewriting.Term a b -> Bool) ->
                                   a -> (b -> b) ->
  (b -> b) ->
    ([b] -> Term_Rewriting.Term a b -> Term_Rewriting.Term a b -> Bool) ->
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
        [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
          Sum_Type.Sum (String -> String) ();
check_ECPs_gj check_ord least xvar yvar ext_check_ord e r =
  Error_Monad.catch_error
    (let {
       ea = sym_list e;
       s = Arith.union r ea;
     } in Error_Monad.catch_error
            (Error_Monad.forallM
              (\ rho_2 ->
                let {
                  l_2 = fst rho_2;
                } in Error_Monad.catch_error
                       (Error_Monad.forallM
                         (\ rho_1 ->
                           Error_Monad.catch_error
                             (Error_Monad.forallM
                               (check_ooverlap_gj check_ord least xvar yvar
                                 ext_check_ord ea r rho_1 rho_2)
                               (Term_Rewriting.fun_poss_list l_2))
                             (\ x -> Sum_Type.Inl (snd x)))
                         s)
                       (\ x -> Sum_Type.Inl (snd x)))
              s)
            (\ x -> Sum_Type.Inl (snd x)))
    (\ x ->
      Sum_Type.Inl
        (Term_Rewriting.showsl_lit "Not all extended CPs are ground joinable." .
          x));

ext_less ::
  forall a b c.
    Redord_closure_ext a b c ->
      [b] -> Term_Rewriting.Term a b -> Term_Rewriting.Term a b -> Bool;
ext_less (Redord_closure_ext ext_less valid more) = ext_less;

valid ::
  forall a b c. Redord_closure_ext a b c -> Sum_Type.Sum (String -> String) ();
valid (Redord_closure_ext ext_less valid more) = valid;

check_FGCR_gj ::
  forall a.
    (Compare.Compare_order a, Eq a,
      Term_Rewriting.Showl a) => Reduction_Order_Impl.Redord_ext a [Arith.Char]
                                   () ->
                                   Redord_closure_ext a [Arith.Char] () ->
                                     [(a, Arith.Nat)] ->
                                       [(Term_Rewriting.Term a [Arith.Char],
  Term_Rewriting.Term a [Arith.Char])] ->
 [(Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char])] ->
   Sum_Type.Sum (String -> String) ();
check_FGCR_gj ro rc f e r =
  Error_Monad.bind (Reduction_Order_Impl.valid ro)
    (\ _ ->
      Error_Monad.bind (valid rc)
        (\ _ ->
          Error_Monad.bind
            (Error_Monad.catch_error
              (Check_Monad.check_subseteq
                (Term_Rewriting.funas_trs_list (Arith.union e r)) f)
              (\ x ->
                Sum_Type.Inl
                  ((Term_Rewriting.showsl_lit "the function symbol " .
                     Term_Rewriting.showsl_prod x) .
                    Term_Rewriting.showsl_lit " does not occur in the TRS\n")))
            (\ _ ->
              check_ECPs_gj (Reduction_Order_Impl.less ro)
                (Reduction_Order_Impl.min_const ro) (\ a -> Arith.char_0x78 : a)
                (\ a -> Arith.char_0x79 : a) (ext_less rc) e r)));

find_variant_in_trs ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Term_Rewriting.Showl b) => (Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b) ->
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)] ->
                                     Sum_Type.Sum (String -> String)
                                       (Term_Rewriting.Term a b,
 Term_Rewriting.Term a b);
find_variant_in_trs ra r =
  Error_Monad.catch_error
    (Error_Monad.firstM (Trs_Impl_More.check_variants_rule ra) r)
    (\ x ->
      Sum_Type.Inl
        (Term_Rewriting.showsl_sep id (Term_Rewriting.showsl_literal "\n") x));

check_stepa ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Term_Rewriting.Showl b) => (Term_Rewriting.Term a b ->
                                   Term_Rewriting.Term a b ->
                                     Sum_Type.Sum (String -> String) ()) ->
                                   ([(Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b)],
                                     [(Term_Rewriting.Term a b,
Term_Rewriting.Term a b)]) ->
                                     Oc_irule a b ->
                                       Sum_Type.Sum (String -> String)
 ([(Term_Rewriting.Term a b, Term_Rewriting.Term a b)],
   [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]);
check_stepa check_ord (e, r) (OC_Deduce s t u) =
  Error_Monad.catch_error
    (let {
       sa = r ++ sym_list e;
     } in Error_Monad.bind
            (Error_Monad.catch_error
              (check_step (\ _ _ -> Sum_Type.Inr ()) sa s t)
              (\ x ->
                Sum_Type.Inl
                  (((((Term_Rewriting.showsl_lit " no step from " .
                        Term_Rewriting.showsl_terma s) .
                       Term_Rewriting.showsl_lit " to ") .
                      Term_Rewriting.showsl_terma t) .
                     Term_Rewriting.showsl_literal "\n") .
                    x)))
            (\ _ ->
              Error_Monad.bind
                (Error_Monad.catch_error
                  (check_step (\ _ _ -> Sum_Type.Inr ()) sa s u)
                  (\ x ->
                    Sum_Type.Inl
                      (((((Term_Rewriting.showsl_lit " no step from " .
                            Term_Rewriting.showsl_terma s) .
                           Term_Rewriting.showsl_lit " to ") .
                          Term_Rewriting.showsl_terma u) .
                         Term_Rewriting.showsl_literal "\n") .
                        x)))
                (\ _ -> Sum_Type.Inr ((t, u) : e, r))))
    (\ x ->
      Sum_Type.Inl
        (((((((Term_Rewriting.showsl_lit "error in deduce step " .
                Term_Rewriting.showsl_terma t) .
               Term_Rewriting.showsl_lit " <- ") .
              Term_Rewriting.showsl_terma s) .
             Term_Rewriting.showsl_lit " -> ") .
            Term_Rewriting.showsl_terma u) .
           Term_Rewriting.showsl_literal "\n") .
          x));
check_stepa check_ord (e, r) (OC_Orientl s t) =
  Error_Monad.catch_error
    (Error_Monad.bind (check_ord s t)
      (\ _ ->
        Error_Monad.bind (find_variant_in_trs (s, t) e)
          (\ st -> Sum_Type.Inr (Arith.removeAll st e, (s, t) : r))))
    (\ x ->
      Sum_Type.Inl
        (((((Term_Rewriting.showsl_lit "error in orientl step for " .
              Term_Rewriting.showsl_terma s) .
             Term_Rewriting.showsl_lit " -> ") .
            Term_Rewriting.showsl_terma t) .
           Term_Rewriting.showsl_literal "\n") .
          x));
check_stepa check_ord (e, r) (OC_Orientr s t) =
  Error_Monad.catch_error
    (Error_Monad.bind (check_ord t s)
      (\ _ ->
        Error_Monad.bind (find_variant_in_trs (s, t) e)
          (\ st -> Sum_Type.Inr (Arith.removeAll st e, (t, s) : r))))
    (\ x ->
      Sum_Type.Inl
        (((((Term_Rewriting.showsl_lit "error in orientr step for " .
              Term_Rewriting.showsl_terma s) .
             Term_Rewriting.showsl_lit " -> ") .
            Term_Rewriting.showsl_terma t) .
           Term_Rewriting.showsl_literal "\n") .
          x));
check_stepa check_ord (e, r) (OC_Delete s) =
  Error_Monad.catch_error
    (Error_Monad.bind (find_variant_in_trs (s, s) e)
      (\ ss -> Sum_Type.Inr (Arith.removeAll ss e, r)))
    (\ x ->
      Sum_Type.Inl
        (((((Term_Rewriting.showsl_lit "error in delete step for " .
              Term_Rewriting.showsl_terma s) .
             Term_Rewriting.showsl_lit " = ") .
            Term_Rewriting.showsl_terma s) .
           Term_Rewriting.showsl_literal "\n") .
          x));
check_stepa check_ord (e, r) (OC_Compose s t u) =
  Error_Monad.catch_error
    (Error_Monad.bind (find_variant_in_trs (s, t) r)
      (\ st ->
        let {
          ra = Arith.removeAll st r;
        } in Error_Monad.bind
               (Error_Monad.catch_error
                 (check_step check_ord (ra ++ sym_list e) t u)
                 (\ x ->
                   Sum_Type.Inl
                     (((((Term_Rewriting.showsl_lit " no ordstep from " .
                           Term_Rewriting.showsl_terma t) .
                          Term_Rewriting.showsl_lit " to ") .
                         Term_Rewriting.showsl_terma u) .
                        Term_Rewriting.showsl_literal "\n") .
                       x)))
               (\ _ -> Sum_Type.Inr (e, (s, u) : ra))))
    (\ x ->
      Sum_Type.Inl
        (((((((((Term_Rewriting.showsl_lit "error in compose step from " .
                  Term_Rewriting.showsl_terma s) .
                 Term_Rewriting.showsl_lit " -> ") .
                Term_Rewriting.showsl_terma t) .
               Term_Rewriting.showsl_lit " to ") .
              Term_Rewriting.showsl_terma s) .
             Term_Rewriting.showsl_lit " -> ") .
            Term_Rewriting.showsl_terma u) .
           Term_Rewriting.showsl_literal "\n") .
          x));
check_stepa check_ord (e, r) (OC_Simplifyl s t u) =
  Error_Monad.catch_error
    (Error_Monad.bind (find_variant_in_trs (s, t) e)
      (\ st ->
        let {
          ea = Arith.removeAll st e;
        } in Error_Monad.bind
               (Error_Monad.catch_error
                 (check_step check_ord (r ++ sym_list ea) s u)
                 (\ x ->
                   Sum_Type.Inl
                     (((((Term_Rewriting.showsl_lit " no ordstep from " .
                           Term_Rewriting.showsl_terma s) .
                          Term_Rewriting.showsl_lit " to ") .
                         Term_Rewriting.showsl_terma u) .
                        Term_Rewriting.showsl_literal "\n") .
                       x)))
               (\ _ -> Sum_Type.Inr ((u, t) : ea, r))))
    (\ x ->
      Sum_Type.Inl
        (((((((((Term_Rewriting.showsl_lit "error in simplifyl step from " .
                  Term_Rewriting.showsl_terma s) .
                 Term_Rewriting.showsl_lit " = ") .
                Term_Rewriting.showsl_terma t) .
               Term_Rewriting.showsl_lit " to ") .
              Term_Rewriting.showsl_terma u) .
             Term_Rewriting.showsl_lit " = ") .
            Term_Rewriting.showsl_terma t) .
           Term_Rewriting.showsl_literal "\n") .
          x));
check_stepa check_ord (e, r) (OC_Simplifyr s t u) =
  Error_Monad.catch_error
    (Error_Monad.bind (find_variant_in_trs (s, t) e)
      (\ st ->
        let {
          ea = Arith.removeAll st e;
        } in Error_Monad.bind
               (Error_Monad.catch_error
                 (check_step check_ord (r ++ sym_list ea) t u)
                 (\ x ->
                   Sum_Type.Inl
                     (((((Term_Rewriting.showsl_lit " no ordstep from " .
                           Term_Rewriting.showsl_terma t) .
                          Term_Rewriting.showsl_lit " to ") .
                         Term_Rewriting.showsl_terma u) .
                        Term_Rewriting.showsl_literal "\n") .
                       x)))
               (\ _ -> Sum_Type.Inr ((s, u) : ea, r))))
    (\ x ->
      Sum_Type.Inl
        (((((((((Term_Rewriting.showsl_lit "error in simplifyr step from " .
                  Term_Rewriting.showsl_terma s) .
                 Term_Rewriting.showsl_lit " = ") .
                Term_Rewriting.showsl_terma t) .
               Term_Rewriting.showsl_lit " to ") .
              Term_Rewriting.showsl_terma s) .
             Term_Rewriting.showsl_lit " = ") .
            Term_Rewriting.showsl_terma u) .
           Term_Rewriting.showsl_literal "\n") .
          x));
check_stepa check_ord (e, r) (OC_Collapse s t u) =
  Error_Monad.catch_error
    (Error_Monad.bind (find_variant_in_trs (t, s) r)
      (\ ts ->
        let {
          ra = Arith.removeAll ts r;
        } in Error_Monad.bind
               (Error_Monad.catch_error
                 (check_step check_ord (ra ++ sym_list e) t u)
                 (\ x ->
                   Sum_Type.Inl
                     (((((Term_Rewriting.showsl_lit " no ordstep from " .
                           Term_Rewriting.showsl_terma t) .
                          Term_Rewriting.showsl_lit " to ") .
                         Term_Rewriting.showsl_terma u) .
                        Term_Rewriting.showsl_literal "\n") .
                       x)))
               (\ _ -> Sum_Type.Inr ((u, s) : e, ra))))
    (\ x ->
      Sum_Type.Inl
        (((((((((Term_Rewriting.showsl_lit "error in collapse step from " .
                  Term_Rewriting.showsl_terma s) .
                 Term_Rewriting.showsl_lit " -> ") .
                Term_Rewriting.showsl_terma t) .
               Term_Rewriting.showsl_lit " to ") .
              Term_Rewriting.showsl_terma u) .
             Term_Rewriting.showsl_lit " = ") .
            Term_Rewriting.showsl_terma t) .
           Term_Rewriting.showsl_literal "\n") .
          x));

check_oc ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Term_Rewriting.Showl b) => (Term_Rewriting.Term a b ->
                                   Term_Rewriting.Term a b ->
                                     Sum_Type.Sum (String -> String) ()) ->
                                   ([(Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b)],
                                     [(Term_Rewriting.Term a b,
Term_Rewriting.Term a b)]) ->
                                     ([(Term_Rewriting.Term a b,
 Term_Rewriting.Term a b)],
                                       [(Term_Rewriting.Term a b,
  Term_Rewriting.Term a b)]) ->
                                       [Oc_irule a b] ->
 Sum_Type.Sum (String -> String) ();
check_oc check_ord (ea, ra) (e, r) [] =
  let {
    err = (\ f x y ->
            (f x . Term_Rewriting.showsl_lit "\nis not a variant of\n") . f y);
  } in Error_Monad.bind
         (Error_Monad.catch_error (Trs_Impl_More.check_variants_trs ea e)
           (\ _ ->
             Sum_Type.Inl (err Equational_Reasoning_Impl.showsl_eqs ea e)))
         (\ _ ->
           Error_Monad.bind
             (Error_Monad.catch_error (Trs_Impl_More.check_variants_trs e ea)
               (\ _ ->
                 Sum_Type.Inl (err Equational_Reasoning_Impl.showsl_eqs ea e)))
             (\ _ ->
               Error_Monad.bind
                 (Error_Monad.catch_error
                   (Trs_Impl_More.check_variants_trs ra r)
                   (\ _ -> Sum_Type.Inl (err Term_Rewriting.showsl_trs ra r)))
                 (\ _ ->
                   Error_Monad.catch_error
                     (Trs_Impl_More.check_variants_trs r ra)
                     (\ _ ->
                       Sum_Type.Inl (err Term_Rewriting.showsl_trs ra r)))));
check_oc check_ord (ea, ra) (e, r) (x : xs) =
  Error_Monad.bind (check_stepa check_ord (ea, ra) x)
    (\ (eaa, raa) -> check_oc check_ord (eaa, raa) (e, r) xs);

order_set_of_permx ::
  forall a.
    (Arith.Ceq a, Arith.Ccompare a,
      Arith.Set_impl a) => [a] -> Arith.Set (a, a);
order_set_of_permx [] = Arith.bot_set;
order_set_of_permx (x : xs) =
  Arith.sup_set (Arith.set (map (\ a -> (x, a)) xs)) (order_set_of_permx xs);

term_order_of_permx ::
  forall a b c.
    (Arith.Ceq a, Arith.Ccompare a, Compare.Compare a, Eq a, Arith.Set_impl a,
      Compare.Compare b, Eq b, Compare.Compare c,
      Eq c) => [a] ->
                 Arith.Set (Term_Rewriting.Term b a, Term_Rewriting.Term c a);
term_order_of_permx p =
  Arith.image (\ (x, y) -> (Term_Rewriting.Var x, Term_Rewriting.Var y))
    (order_set_of_permx p);

create_KBO_redord_closure ::
  forall a.
    (Compare.Compare_order a, Eq a,
      Term_Rewriting.Showl a) => ([((a, Arith.Nat),
                                     (Arith.Nat,
                                       (Arith.Nat, Maybe [Arith.Nat])))],
                                   Arith.Nat) ->
                                   [(a, Arith.Nat)] ->
                                     Redord_closure_ext a [Arith.Char] ();
create_KBO_redord_closure pr fs =
  (case KBO_Impl.prec_weight_repr_to_prec_weight pr of {
    (_, (p, (w, (w0, (lcs, scf))))) ->
      let {
        ro = (KBO_Impl.create_KBO_redord ::
               ([((a, Arith.Nat), (Arith.Nat, (Arith.Nat, Maybe [Arith.Nat])))],
                 Arith.Nat) ->
                 [(a, Arith.Nat)] ->
                   Reduction_Order_Impl.Redord_ext a [Arith.Char] ())
               pr fs;
      } in Redord_closure_ext
             (\ vp s t ->
               fst (KBO_More.kbo_closure w w0 scf (Arith.membera lcs)
                     (\ f g -> fst (p f g)) (\ f g -> snd (p f g))
                     (term_order_of_permx vp) s t))
             (Reduction_Order_Impl.valid ro) ();
  });

check_ground_completeness ::
  forall a.
    (Compare.Compare_order a, Eq a,
      Term_Rewriting.Showl a) => (String -> String) ->
                                   [(Term_Rewriting.Term a [Arith.Char],
                                      Term_Rewriting.Term a [Arith.Char])] ->
                                     [(Term_Rewriting.Term a [Arith.Char],
Term_Rewriting.Term a [Arith.Char])] ->
                                       [(a, Arith.Nat)] ->
 Reduction_order_input a -> Sum_Type.Sum (String -> String) ();
check_ground_completeness i e r f ro =
  FOR_Preliminaries.debug i "check ground completeness"
    (case ro of {
      RPO_Input _ ->
        Sum_Type.Inl (Term_Rewriting.showsl_lit "unsupported reduction order ");
      KBO_Input precw ->
        let {
          kbo = KBO_Impl.create_KBO_redord precw f;
        } in Error_Monad.bind
               (Check_Monad.check
                 (all (\ (a, b) -> Reduction_Order_Impl.less kbo a b) r)
                 (Term_Rewriting.showsl_lit "found unorientable rule in R"))
               (\ _ ->
                 Error_Monad.catch_error
                   (check_FGCR_gj kbo (create_KBO_redord_closure precw f) f e r)
                   (\ x ->
                     Sum_Type.Inl
                       ((i . Term_Rewriting.showsl_lit
                               ": error in ground confluence proof \n") .
                         x)));
    });

check_FGCR_run_with_closure ::
  forall a.
    (Compare.Compare_order a, Eq a,
      Term_Rewriting.Showl a) => Reduction_Order_Impl.Redord_ext a [Arith.Char]
                                   () ->
                                   Redord_closure_ext a [Arith.Char] () ->
                                     [(a, Arith.Nat)] ->
                                       [(Term_Rewriting.Term a [Arith.Char],
  Term_Rewriting.Term a [Arith.Char])] ->
 [(Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char])] ->
   [(Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char])] ->
     [(Term_Rewriting.Term a [Arith.Char],
        Term_Rewriting.Term a [Arith.Char])] ->
       [Oc_irule a [Arith.Char]] -> Sum_Type.Sum (String -> String) ();
check_FGCR_run_with_closure ro rc f e_0 r_0 e r steps =
  let {
    check_ord =
      (\ s t ->
        Check_Monad.check (Reduction_Order_Impl.less ro s t)
          (Term_Rewriting.showsl_lit "Term pair cannot be oriented."));
  } in Error_Monad.bind
         (Error_Monad.catch_error
           (Error_Monad.forallM (\ (a, b) -> check_ord a b) r_0)
           (\ x -> Sum_Type.Inl (snd x)))
         (\ _ ->
           Error_Monad.bind
             (Error_Monad.catch_error
               (check_oc check_ord (e_0, r_0) (e, r) steps)
               (\ x ->
                 Sum_Type.Inl
                   (Term_Rewriting.showsl_lit
                      "The oKB run could not be reconstructed.\n\n" .
                     x)))
             (\ _ ->
               Error_Monad.catch_error (check_FGCR_gj ro rc f e r)
                 (\ x ->
                   Sum_Type.Inl
                     (Term_Rewriting.showsl_lit
                        "Ground confluence could not be verified.\n\n" .
                       x))));

check_ordered_completion_proof_ext ::
  forall a.
    (Compare.Compare_order a, Eq a,
      Term_Rewriting.Showl a) => (String -> String) ->
                                   [(Term_Rewriting.Term a [Arith.Char],
                                      Term_Rewriting.Term a [Arith.Char])] ->
                                     [(Term_Rewriting.Term a [Arith.Char],
Term_Rewriting.Term a [Arith.Char])] ->
                                       [(Term_Rewriting.Term a [Arith.Char],
  Term_Rewriting.Term a [Arith.Char])] ->
 Reduction_order_input a ->
   Ordered_completion_proof a [Arith.Char] ->
     Sum_Type.Sum (String -> String) ();
check_ordered_completion_proof_ext i e_0 e r ro (OKB steps) =
  FOR_Preliminaries.debug i "OKB"
    (case ro of {
      RPO_Input _ ->
        Sum_Type.Inl
          (Term_Rewriting.showsl_lit "unsupported reduction order\n");
      KBO_Input precw ->
        let {
          f = map fst (fst precw);
        } in Error_Monad.catch_error
               (check_FGCR_run_with_closure (KBO_Impl.create_KBO_redord precw f)
                 (create_KBO_redord_closure precw f) f e_0 [] e r steps)
               (\ x ->
                 Sum_Type.Inl
                   ((i . Term_Rewriting.showsl_lit
                           ": error in ground completeness proof with closure\n") .
                     x));
    });

check_equational_disproof_oc ::
  forall a.
    (Compare.Compare_order a, Eq a,
      Term_Rewriting.Showl a) => (String -> String) ->
                                   (Term_Rewriting.Term a [Arith.Char],
                                     Term_Rewriting.Term a [Arith.Char]) ->
                                     [(Term_Rewriting.Term a [Arith.Char],
Term_Rewriting.Term a [Arith.Char])] ->
                                       [(Term_Rewriting.Term a [Arith.Char],
  Term_Rewriting.Term a [Arith.Char])] ->
 [(Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char])] ->
   Reduction_order_input a ->
     Ordered_completion_proof a [Arith.Char] ->
       Sum_Type.Sum (String -> String) ();
check_equational_disproof_oc i eq e_0 e r ro p =
  (case ro of {
    RPO_Input _ ->
      Sum_Type.Inl (Term_Rewriting.showsl_lit "unsupported reduction order");
    KBO_Input precw ->
      Error_Monad.bind (check_ordered_completion_proof_ext i e_0 e r ro p)
        (\ _ ->
          let {
            roa = KBO_Impl.create_KBO_redord precw (precw_w0_sig precw);
          } in (case eq of {
                 (s, t) ->
                   Error_Monad.bind
                     (Error_Monad.catch_error
                       (Term_Rewriting.check_ground_term s)
                       (\ _ ->
                         Sum_Type.Inl
                           (Term_Rewriting.showsl_terma s .
                             Term_Rewriting.showsl_lit
                               " is not a ground term\n")))
                     (\ _ ->
                       Error_Monad.bind
                         (Error_Monad.catch_error
                           (Term_Rewriting.check_ground_term t)
                           (\ _ ->
                             Sum_Type.Inl
                               (Term_Rewriting.showsl_terma t .
                                 Term_Rewriting.showsl_lit
                                   " is not a ground term\n")))
                         (\ _ ->
                           Error_Monad.bind
                             (Error_Monad.catch_error
                               (Check_Monad.check_subseteq
                                 (Term_Rewriting.funas_rule_list (s, t))
                                 (precw_w0_sig precw))
                               (\ _ ->
                                 Sum_Type.Inl
                                   (Term_Rewriting.showsl_lit
                                     " goal is not over expected signature\n")))
                             (\ _ ->
                               Error_Monad.bind
                                 (Error_Monad.catch_error
                                   (Check_Monad.check_subseteq
                                     (Term_Rewriting.funas_trs_list
                                       (e_0 ++ e ++ r))
                                     (precw_w0_sig precw))
                                   (\ _ ->
                                     Sum_Type.Inl
                                       (Term_Rewriting.showsl_lit
 " system is not over expected signature\n")))
                                 (\ _ ->
                                   let {
                                     nf = compute_mordstep_NF
    (Reduction_Order_Impl.less roa) (Reduction_Order_Impl.min_const roa)
    (rules e r);
                                   } in (case (nf s, nf t) of {
  (Nothing, _) ->
    Sum_Type.Inl
      (((Term_Rewriting.showsl_lit "error when computing normal forms of " .
          Term_Rewriting.showsl_terma s) .
         Term_Rewriting.showsl_lit " and ") .
        Term_Rewriting.showsl_terma t);
  (Just _, Nothing) ->
    Sum_Type.Inl
      (((Term_Rewriting.showsl_lit "error when computing normal forms of " .
          Term_Rewriting.showsl_terma s) .
         Term_Rewriting.showsl_lit " and ") .
        Term_Rewriting.showsl_terma t);
  (Just sa, Just ta) ->
    (if not (Term_Rewriting.equal_term sa ta) then Sum_Type.Inr ()
      else Sum_Type.Inl
             ((((Term_Rewriting.showsl_terma s .
                  Term_Rewriting.showsl_lit " and ") .
                 Term_Rewriting.showsl_terma t) .
                Term_Rewriting.showsl_lit " have same normal form ") .
               Term_Rewriting.showsl_terma sa));
})))));
               }));
  });

check_equational_disproof_by_ground_complete_system ::
  forall a.
    (Compare.Compare_order a, Eq a,
      Term_Rewriting.Showl a) => (String -> String) ->
                                   (Term_Rewriting.Term a [Arith.Char],
                                     Term_Rewriting.Term a [Arith.Char]) ->
                                     [(Term_Rewriting.Term a [Arith.Char],
Term_Rewriting.Term a [Arith.Char])] ->
                                       [(Term_Rewriting.Term a [Arith.Char],
  Term_Rewriting.Term a [Arith.Char])] ->
 [(Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char])] ->
   Reduction_order_input a -> Sum_Type.Sum (String -> String) ();
check_equational_disproof_by_ground_complete_system i eq e_0 e r ro =
  (case ro of {
    RPO_Input _ ->
      Sum_Type.Inl (Term_Rewriting.showsl_lit "unsupported reduction order");
    KBO_Input precw ->
      let {
        f = precw_w0_sig precw;
        kbo = KBO_Impl.create_KBO_redord precw f;
        _ = ext_less (create_KBO_redord_closure precw f);
      } in (case eq of {
             (s, t) ->
               Error_Monad.bind
                 (Error_Monad.catch_error (Term_Rewriting.check_ground_term s)
                   (\ _ ->
                     Sum_Type.Inl
                       (Term_Rewriting.showsl_terma s .
                         Term_Rewriting.showsl_lit " is not a ground term\n")))
                 (\ _ ->
                   Error_Monad.bind
                     (Error_Monad.catch_error
                       (Term_Rewriting.check_ground_term t)
                       (\ _ ->
                         Sum_Type.Inl
                           (Term_Rewriting.showsl_terma t .
                             Term_Rewriting.showsl_lit
                               " is not a ground term\n")))
                     (\ _ ->
                       Error_Monad.bind
                         (Error_Monad.catch_error
                           (Check_Monad.check_subseteq
                             (Term_Rewriting.funas_rule_list (s, t)) f)
                           (\ _ ->
                             Sum_Type.Inl
                               (Term_Rewriting.showsl_lit
                                 " goal is not over expected signature\n")))
                         (\ _ ->
                           Error_Monad.bind
                             (Error_Monad.catch_error
                               (Check_Monad.check_subseteq
                                 (Term_Rewriting.funas_trs_list (e_0 ++ e ++ r))
                                 f)
                               (\ _ ->
                                 Sum_Type.Inl
                                   (Term_Rewriting.showsl_lit
                                     " system is not over expected signature\n")))
                             (\ _ ->
                               Error_Monad.bind
                                 (check_ground_completeness i e r f ro)
                                 (\ _ ->
                                   Error_Monad.bind
                                     (Error_Monad.catch_error
                                       (Error_Monad.catch_error
 (Error_Monad.forallM
   (\ (a, b) ->
     check_instance_joinable (Reduction_Order_Impl.less kbo)
       (Reduction_Order_Impl.min_const kbo) e r a b)
   e_0)
 (\ x -> Sum_Type.Inl (snd x)))
                                       (\ _ ->
 Sum_Type.Inl (Term_Rewriting.showsl_lit " E_0 is not subsumed by E and R\n")))
                                     (\ _ ->
                                       let {
 nf = compute_mordstep_NF (Reduction_Order_Impl.less kbo)
        (Reduction_Order_Impl.min_const kbo) (rules e r);
                                       } in
 (case (nf s, nf t) of {
   (Nothing, _) ->
     Sum_Type.Inl
       (((Term_Rewriting.showsl_lit "error when computing normal forms of " .
           Term_Rewriting.showsl_terma s) .
          Term_Rewriting.showsl_lit " and ") .
         Term_Rewriting.showsl_terma t);
   (Just _, Nothing) ->
     Sum_Type.Inl
       (((Term_Rewriting.showsl_lit "error when computing normal forms of " .
           Term_Rewriting.showsl_terma s) .
          Term_Rewriting.showsl_lit " and ") .
         Term_Rewriting.showsl_terma t);
   (Just sa, Just ta) ->
     (if not (Term_Rewriting.equal_term sa ta) then Sum_Type.Inr ()
       else Sum_Type.Inl
              ((((Term_Rewriting.showsl_terma s .
                   Term_Rewriting.showsl_lit " and ") .
                  Term_Rewriting.showsl_terma t) .
                 Term_Rewriting.showsl_lit " have same normal form ") .
                Term_Rewriting.showsl_terma sa));
 })))))));
           });
  });

}
