{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Non_Confluence_Impl(Non_join_info(..), check_non_join, check_non_cr,
                       check_rule_removal, check_modularity_ncr)
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
import qualified RTrancl_Impl;
import qualified Semantic_Labeling_Impl;
import qualified Product_Type;
import qualified Missing_List;
import qualified Trs;
import qualified List;
import qualified Map;
import qualified Util;
import qualified Usable_Rules_NJ_Unif_Impl;
import qualified Usable_Rules_NJ_Impl;
import qualified Ground_Context_Impl;
import qualified Position;
import qualified Check_Monad;
import qualified Trs_Impl;
import qualified Tcap_Impl;
import qualified Option;
import qualified Ground_Context;
import qualified Set;
import qualified Check_Termination_Common;
import qualified Term_More;
import qualified Container_Setup;
import qualified Compare_Order_Instances;
import qualified Compare_Instances;
import qualified Q_Restricted_Rewriting_Impl;
import qualified Error_Monad;
import qualified Compare;
import qualified Collection_Enum;
import qualified Cardinality;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified HOL;
import qualified Labelings_Impl;
import qualified Labelings;
import qualified Str;
import qualified Mapping_Impl;
import qualified Collection_Order;
import qualified Shows_Literal;
import qualified Semantic_Labeling_Carrier;
import qualified Tree_Automata_Impl;
import qualified Term_Order_Impl;
import qualified Argument_Filter;
import qualified Sum_Type;
import qualified Term;
import qualified Arith;

data Non_join_info a b c d = Diff_NFs
  | Tcap_Non_Unif (Term.Term a b -> Term.Term a b -> b -> Term.Term a b)
  | Tree_Aut_Intersect_Empty (Tree_Automata_Impl.Tree_automaton c a)
      (Tree_Automata_Impl.Ta_relation c) (Tree_Automata_Impl.Tree_automaton c a)
      (Tree_Automata_Impl.Ta_relation c)
  | Finite_Model_Gt (Semantic_Labeling_Carrier.Sl_variant a b)
  | Discr_Pair_Gt (Term_Order_Impl.Rel_impl_type a b d) d
  | Usable_Rules_Reach_NJ (Non_join_info a b c d)
  | Usable_Rules_Reach_Unif_NJ
      (Sum_Type.Sum [(Term.Term a b, Term.Term a b)]
        [(Term.Term a b, Term.Term a b)])
      (Non_join_info a b c d)
  | Finitely_Reachable
  | Argument_Filter_NJ [((a, Arith.Nat), Argument_Filter.Af_entry)]
      (Non_join_info a b c d)
  | Grounding [(b, Term.Term a b)] (Non_join_info a b c d)
  | Subterm_NJ [Arith.Nat] (Non_join_info a b c d);

is_non_joinable_finite_reachable_rtrancl ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Eq a,
      Set_Impl.Set_impl a,
      Shows_Literal.Showl a) => (a -> [a]) ->
                                  (a -> [a]) ->
                                    a -> a ->
   Sum_Type.Sum (String -> String) ();
is_non_joinable_finite_reachable_rtrancl succsR succsS s t =
  (case (RTrancl_Impl.rtrancl_option succsR [s],
          RTrancl_Impl.rtrancl_option succsS [t])
    of {
    (Nothing, _) ->
      Check_Monad.check False
        (Shows_Literal.showsl_lit
          "cannot happen: is_non_join is non-terminating");
    (Just _, Nothing) ->
      Check_Monad.check False
        (Shows_Literal.showsl_lit
          "cannot happen: is_non_join is non-terminating");
    (Just reach1, Just reach2) ->
      Error_Monad.catch_error
        (Error_Monad.forallM
          (\ u ->
            Check_Monad.check (not (List.member reach2 u))
              (Shows_Literal.showsl_lit "the following term is a join: " .
                Shows_Literal.showsl u))
          reach1)
        (\ x -> Sum_Type.Inl (snd x));
  });

check_qmodel_rule_ass ::
  forall a b c.
    (Shows_Literal.Showl a, Shows_Literal.Showl b,
      Shows_Literal.Showl c) => (a -> [b] -> b) ->
                                  (b -> b -> Bool) ->
                                    (c -> b) ->
                                      (Term.Term a c, Term.Term a c) ->
Sum_Type.Sum (String -> String) ();
check_qmodel_rule_ass i cge alpha (l, r) =
  let {
    cl = Term.eval_term i l alpha;
    cr = Term.eval_term i r alpha;
  } in Check_Monad.check (cge cl cr)
         (((((Shows_Literal.showsl_lit "rule " . Trs_Impl.showsl_rule (l, r)) .
              Shows_Literal.showsl_lit
                " violates the model condition, [lhs] = ") .
             Shows_Literal.showsl cl) .
            Shows_Literal.showsl_lit ", [rhs] = ") .
           Shows_Literal.showsl cr);

check_qmodel_rule ::
  forall a b c.
    (Shows_Literal.Showl a, Shows_Literal.Showl b, Eq c,
      Shows_Literal.Showl c) => (a -> [b] -> b) ->
                                  [b] ->
                                    (b -> b -> Bool) ->
                                      (Term.Term a c, Term.Term a c) ->
Sum_Type.Sum (String -> String) ();
check_qmodel_rule i c cge lr =
  Error_Monad.catch_error
    (Error_Monad.forallM (\ alpha -> check_qmodel_rule_ass i cge alpha lr)
      (map Util.fun_of (Util.enum_vectors c (Trs_Impl.insert_vars_rule lr []))))
    (\ x -> Sum_Type.Inl (snd x));

check_qmodel ::
  forall a b c.
    (Shows_Literal.Showl a, Shows_Literal.Showl b, Eq c,
      Shows_Literal.Showl c) => (a -> [b] -> b) ->
                                  [b] ->
                                    (b -> b -> Bool) ->
                                      [(Term.Term a c, Term.Term a c)] ->
Sum_Type.Sum (String -> String) ();
check_qmodel i c cge r =
  Error_Monad.catch_error (Error_Monad.forallM (check_qmodel_rule i c cge) r)
    (\ x -> Sum_Type.Inl (snd x));

check_non_join_model ::
  forall a b c d.
    (Shows_Literal.Showl a, Shows_Literal.Showl b, Eq d,
      Shows_Literal.Showl d) => (a -> a -> Bool) ->
                                  ([(b, Arith.Nat)] ->
                                    [(b, Arith.Nat)] ->
                                      Sum_Type.Sum (String -> String)
(Semantic_Labeling_Impl.Sl_ops_ext b a c d ())) ->
                                    [(Term.Term b d, Term.Term b d)] ->
                                      [(Term.Term b d, Term.Term b d)] ->
Term.Term b d -> Term.Term b d -> Sum_Type.Sum (String -> String) ();
check_non_join_model cge gen rs rt s t =
  Error_Monad.catch_error
    (Error_Monad.bind (gen (Trs.funas_trs_list (rs ++ rt)) [])
      (\ ops ->
        let {
          i = Semantic_Labeling_Impl.sl_I ops;
          e = (\ ta ->
                Term.eval_term i ta (\ _ -> Semantic_Labeling_Impl.sl_c ops));
          es = e s;
          et = e t;
        } in Error_Monad.bind
               (Check_Monad.check (not (cge et es))
                 ((((((((Shows_Literal.showsl_lit
                           "the inequality must not hold: [" .
                          Term_More.showsl_terma t) .
                         Shows_Literal.showsl_lit "] = ") .
                        Shows_Literal.showsl et) .
                       Shows_Literal.showsl_lit " >= ") .
                      Shows_Literal.showsl es) .
                     Shows_Literal.showsl_lit " = [") .
                    Term_More.showsl_terma s) .
                   Shows_Literal.showsl_lit "]"))
               (\ _ ->
                 check_qmodel i (Semantic_Labeling_Impl.sl_C ops) cge
                   (Trs_Impl.reverse_rules rs ++ rt))))
    (\ x ->
      Sum_Type.Inl
        ((Shows_Literal.showsl_lit
            "problem in disproving non-joinability via interpretations" .
           Shows_Literal.showsl_literal "\n") .
          x));

check_non_join_finite_model ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b,
      Shows_Literal.Showl b) => Semantic_Labeling_Carrier.Sl_variant
                                  (Labelings.Lab a [Arith.Nat]) b ->
                                  [(Term.Term (Labelings.Lab a [Arith.Nat]) b,
                                     Term.Term (Labelings.Lab a [Arith.Nat])
                                       b)] ->
                                    [(Term.Term (Labelings.Lab a [Arith.Nat]) b,
                                       Term.Term (Labelings.Lab a [Arith.Nat])
 b)] ->
                                      Term.Term (Labelings.Lab a [Arith.Nat])
b ->
Term.Term (Labelings.Lab a [Arith.Nat]) b -> Sum_Type.Sum (String -> String) ();
check_non_join_finite_model (Semantic_Labeling_Carrier.Rootlab x) rs rt s t =
  check_non_join_model Labelings.equal_lab
    (Semantic_Labeling_Impl.slm_gen_to_sl_gen
      (Semantic_Labeling_Carrier.rl_slm x))
    rs rt s t;
check_non_join_finite_model (Semantic_Labeling_Carrier.Finitelab sli) rs rt s t
  = check_non_join_model Arith.equal_nat
      (Semantic_Labeling_Impl.slm_gen_to_sl_gen
        (\ _ _ -> Sum_Type.Inr (Semantic_Labeling_Carrier.sli_to_slm sli)))
      rs rt s t;
check_non_join_finite_model (Semantic_Labeling_Carrier.QuasiFinitelab sli v) rs
  rt s t =
  Check_Monad.or_ok
    (check_non_join_model Semantic_Labeling_Carrier.qmodel_cge
      (\ f g -> Semantic_Labeling_Carrier.qsli_to_sl v f g sli) rs rt s t)
    (check_non_join_model Semantic_Labeling_Carrier.qmodel_cge
      (\ f g -> Semantic_Labeling_Carrier.qsli_to_sl v f g sli) rt rs t s);

check_non_join_discr_pair ::
  forall a b.
    (Compare.Compare_order a, Shows_Literal.Showl a,
      Shows_Literal.Showl b) => Term_Order_Impl.Rel_impl_ext a b () ->
                                  [(Term.Term a b, Term.Term a b)] ->
                                    [(Term.Term a b, Term.Term a b)] ->
                                      Term.Term a b ->
Term.Term a b -> Sum_Type.Sum (String -> String) ();
check_non_join_discr_pair rp rs rt s t =
  Error_Monad.catch_error
    (Error_Monad.bind (Term_Order_Impl.rel_impl_co_discrimination_pair rp)
      (\ _ ->
        Error_Monad.bind
          (Term_Order_Impl.rel_impl_ns rp (Trs_Impl.reverse_rules rs ++ rt))
          (\ _ -> Term_Order_Impl.s rp (s, t))))
    (\ x ->
      Sum_Type.Inl
        ((Shows_Literal.showsl_lit
            "problem in disproving non-joinability via co-discrimination pairs" .
           Shows_Literal.showsl_literal "\n") .
          x));

check_non_join ::
  forall a b c.
    (Compare.Compare_order a, HOL.Default a, Eq a, Shows_Literal.Showl a,
      Cardinality.Card_UNIV b, Collection_Enum.Cenum b, Collection_Eq.Ceq b,
      Collection_Order.Cproper_interval b, Compare.Compare_order b, Eq b,
      Set_Impl.Set_impl b,
      Shows_Literal.Showl b) => [(Term.Term (Labelings.Lab a [Arith.Nat])
                                    [Str.Char],
                                   Term.Term (Labelings.Lab a [Arith.Nat])
                                     [Str.Char])] ->
                                  [(Term.Term (Labelings.Lab a [Arith.Nat])
                                      [Str.Char],
                                     Term.Term (Labelings.Lab a [Arith.Nat])
                                       [Str.Char])] ->
                                    Term.Term (Labelings.Lab a [Arith.Nat])
                                      [Str.Char] ->
                                      Term.Term (Labelings.Lab a [Arith.Nat])
[Str.Char] ->
Non_join_info (Labelings.Lab a [Arith.Nat]) [Str.Char] b c ->
  Sum_Type.Sum (String -> String) ();
check_non_join rs rt s t Diff_NFs =
  Error_Monad.bind
    (Check_Monad.check (not (Term.equal_term s t))
      ((((Shows_Literal.showsl_lit "the terms " . Term_More.showsl_terma s) .
          Shows_Literal.showsl_lit " and ") .
         Term_More.showsl_terma t) .
        Shows_Literal.showsl_lit " are identical"))
    (\ _ ->
      let {
        chknf =
          (\ sa r ->
            Check_Monad.check (Trs_Impl.is_NF_trs r sa)
              ((Shows_Literal.showsl_lit "the term " .
                 Term_More.showsl_terma sa) .
                Shows_Literal.showsl_lit " is not in normal form"));
      } in Error_Monad.bind (chknf s rs) (\ _ -> chknf t rt));
check_non_join rs rt s t (Grounding sigma prf) =
  let {
    sigmaa = Term_More.mk_subst Term.Var sigma;
  } in check_non_join rs rt (Term.eval_term Term.Fun s sigmaa)
         (Term.eval_term Term.Fun t sigmaa) prf;
check_non_join rs rt s t (Subterm_NJ p prf) =
  Error_Monad.bind
    (Check_Monad.check
      (Set.member p (Ground_Context.pos_gctxt (Tcap_Impl.tcapI rs s)))
      (((Shows_Literal.showsl_lit "position " . Position.showsl_pos p) .
         Shows_Literal.showsl_lit " not in capped term  of ") .
        Term_More.showsl_terma s))
    (\ _ ->
      Error_Monad.bind
        (Check_Monad.check
          (Set.member p (Ground_Context.pos_gctxt (Tcap_Impl.tcapI rt t)))
          (((Shows_Literal.showsl_lit "position " . Position.showsl_pos p) .
             Shows_Literal.showsl_lit " not in capped term  of ") .
            Term_More.showsl_terma t))
        (\ _ ->
          check_non_join rs rt (Term_More.subt_at s p) (Term_More.subt_at t p)
            prf));
check_non_join rs rt s t (Tcap_Non_Unif grd_subst) =
  let {
    sigma = grd_subst s t;
    cs = Tcap_Impl.tcapI rs (Term.eval_term Term.Fun s sigma);
    ct = Tcap_Impl.tcapI rt (Term.eval_term Term.Fun t sigma);
  } in Check_Monad.check (Option.is_none (Ground_Context_Impl.merge cs ct))
         ((((Shows_Literal.showsl_lit "could not infer that " .
              Term_More.showsl_terma s) .
             Shows_Literal.showsl_lit " and ") .
            Term_More.showsl_terma t) .
           Shows_Literal.showsl_lit " are not joinable");
check_non_join rs rt s t (Tree_Aut_Intersect_Empty ta1 rel1 ta2 rel2) =
  Error_Monad.catch_error
    (Tree_Automata_Impl.non_join_with_ta ta1 rel1 rs s ta2 rel2 rt t)
    (\ x ->
      Sum_Type.Inl
        ((((((Shows_Literal.showsl_lit "could not infer that " .
               Term_More.showsl_terma s) .
              Shows_Literal.showsl_lit " and ") .
             Term_More.showsl_terma t) .
            Shows_Literal.showsl_lit " are not joinable") .
           Shows_Literal.showsl_literal "\n") .
          x));
check_non_join rs rt s t (Finite_Model_Gt i) =
  Error_Monad.catch_error (check_non_join_finite_model i rs rt s t)
    (\ x ->
      Sum_Type.Inl
        ((((((Shows_Literal.showsl_lit "could not infer that " .
               Term_More.showsl_terma s) .
              Shows_Literal.showsl_lit " and ") .
             Term_More.showsl_terma t) .
            Shows_Literal.showsl_lit " are not joinable") .
           Shows_Literal.showsl_literal "\n") .
          x));
check_non_join rs rt s t (Discr_Pair_Gt grt rp) =
  Error_Monad.catch_error
    (Check_Monad.or_ok
      (check_non_join_discr_pair (Term_Order_Impl.rel_impl_of grt rp) rs rt s t)
      (check_non_join_discr_pair (Term_Order_Impl.rel_impl_of grt rp) rt rs t
        s))
    (\ _ ->
      Sum_Type.Inl
        ((((Shows_Literal.showsl_lit "could not infer that " .
             Term_More.showsl_terma s) .
            Shows_Literal.showsl_lit " and ") .
           Term_More.showsl_terma t) .
          Shows_Literal.showsl_lit " are not joinable by discrimination pair"));
check_non_join rs rt s t (Usable_Rules_Reach_NJ prf) =
  check_non_join (Usable_Rules_NJ_Impl.usable_rules_reach_impl rs s)
    (Usable_Rules_NJ_Impl.usable_rules_reach_impl rt t) s t prf;
check_non_join rs rt s t (Usable_Rules_Reach_Unif_NJ u_sum prf) =
  (case u_sum of {
    Sum_Type.Inl u ->
      Error_Monad.bind
        (Usable_Rules_NJ_Unif_Impl.check_usable_rules_unif rs u s)
        (\ _ -> check_non_join u rt s t prf);
    Sum_Type.Inr u ->
      Error_Monad.bind
        (Usable_Rules_NJ_Unif_Impl.check_usable_rules_unif rt u t)
        (\ _ -> check_non_join rs u s t prf);
  });
check_non_join rs rt s t Finitely_Reachable =
  Error_Monad.bind (Trs_Impl.check_wf_trs rs)
    (\ _ ->
      Error_Monad.bind (Trs_Impl.check_wf_trs rt)
        (\ _ ->
          Error_Monad.catch_error
            (is_non_joinable_finite_reachable_rtrancl (Trs_Impl.rewrite rs)
              (Trs_Impl.rewrite rt) s t)
            (\ _ ->
              Sum_Type.Inl
                ((((Shows_Literal.showsl_lit "could not infer that " .
                     Term_More.showsl_terma s) .
                    Shows_Literal.showsl_lit " and ") .
                   Term_More.showsl_terma t) .
                  Shows_Literal.showsl_lit
                    " are not joinable by finitely reachable terms"))));
check_non_join rs rt s t (Argument_Filter_NJ pi prf) =
  (case Argument_Filter.afs_of pi of {
    Nothing ->
      Sum_Type.Inl (Shows_Literal.showsl_lit "invalid argument filter");
    Just pia -> let {
                  af = Argument_Filter.af_term pia;
                  afs = Argument_Filter.af_rules pia;
                } in check_non_join (afs rs) (afs rt) (af s) (af t) prf;
  });

check_non_cr ::
  forall a b c.
    (Compare.Compare_order a, HOL.Default a, Eq a, Shows_Literal.Showl a,
      Cardinality.Card_UNIV b, Collection_Enum.Cenum b, Collection_Eq.Ceq b,
      Collection_Order.Cproper_interval b, Compare.Compare_order b, Eq b,
      Set_Impl.Set_impl b,
      Shows_Literal.Showl b) => [(Term.Term (Labelings.Lab a [Arith.Nat])
                                    [Str.Char],
                                   Term.Term (Labelings.Lab a [Arith.Nat])
                                     [Str.Char])] ->
                                  Term.Term (Labelings.Lab a [Arith.Nat])
                                    [Str.Char] ->
                                    [([Arith.Nat],
                                       ((Term.Term (Labelings.Lab a [Arith.Nat])
   [Str.Char],
  Term.Term (Labelings.Lab a [Arith.Nat]) [Str.Char]),
 Term.Term (Labelings.Lab a [Arith.Nat]) [Str.Char]))] ->
                                      [([Arith.Nat],
 ((Term.Term (Labelings.Lab a [Arith.Nat]) [Str.Char],
    Term.Term (Labelings.Lab a [Arith.Nat]) [Str.Char]),
   Term.Term (Labelings.Lab a [Arith.Nat]) [Str.Char]))] ->
Non_join_info (Labelings.Lab a [Arith.Nat]) [Str.Char] b c ->
  Sum_Type.Sum (String -> String) ();
check_non_cr r s seq1 seq2 reason =
  let {
    chk = Q_Restricted_Rewriting_Impl.check_rsteps_last r s;
  } in Error_Monad.bind (chk seq1)
         (\ _ ->
           Error_Monad.bind (chk seq2)
             (\ _ ->
               check_non_join r r (Q_Restricted_Rewriting_Impl.rseq_last s seq1)
                 (Q_Restricted_Rewriting_Impl.rseq_last s seq2) reason));

check_rule_removal ::
  forall a b c.
    (Eq a, Shows_Literal.Showl a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b,
      Shows_Literal.Showl b) => [((Term.Term a b, Term.Term a b),
                                   [([Arith.Nat],
                                      ((Term.Term a b, Term.Term a b),
Term.Term a b))])] ->
                                  c -> [(Term.Term a b, Term.Term a b)] ->
 [(Term.Term a b, Term.Term a b)] -> Sum_Type.Sum (String -> String) ();
check_rule_removal infos r rdel s =
  Error_Monad.catch_error
    (let {
       f = Trs.funas_trs_list s;
       rs = filter
              (\ lr -> all (List.member f) (Term_More.funas_term_list (fst lr)))
              rdel;
     } in Error_Monad.bind (Trs_Impl.check_wf_trs s)
            (\ _ ->
              Error_Monad.catch_error
                (Error_Monad.forallM
                  (\ lr ->
                    (case Map.map_of infos lr of {
                      Nothing ->
                        Sum_Type.Inl
                          (Shows_Literal.showsl_lit
                             "did not find info for rule: " .
                            Trs_Impl.showsl_rule lr);
                      Just info ->
                        Q_Restricted_Rewriting_Impl.check_rsteps s info (fst lr)
                          (snd lr);
                    }))
                  rs)
                (\ x -> Sum_Type.Inl (snd x))))
    (\ x ->
      Sum_Type.Inl
        ((x . Shows_Literal.showsl_literal "\n") .
          Shows_Literal.showsl_lit "problem in rule removal"));

check_modularity_ncr ::
  forall a b.
    (Collection_Enum.Cenum a, Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Eq a, Set_Impl.Set_impl a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => [(Term.Term a b, Term.Term a b)] ->
                                  [(Term.Term a b, Term.Term a b)] ->
                                    Sum_Type.Sum (String -> String) ();
check_modularity_ncr ra r =
  Error_Monad.bind
    (Error_Monad.catch_error (Check_Monad.check_subseteq r ra)
      (\ _ ->
        Sum_Type.Inl
          (Shows_Literal.showsl_lit "new TRS is not a subsystem of given TRS")))
    (\ _ ->
      let {
        s = Missing_List.list_diff ra r;
        f = Trs.funas_trs_list r;
        g = Trs.funas_trs_list s;
      } in Error_Monad.bind
             (Check_Monad.check
               (Set.less_eq_set (Set.inf_set (List.set f) (List.set g))
                 Set.bot_set)
               (Shows_Literal.showsl_lit "signatures are not disjoint"))
             (\ _ ->
               Error_Monad.bind (Trs_Impl.check_varcond_subset r)
                 (\ _ ->
                   Error_Monad.catch_error
                     (Error_Monad.catch_error
                       (Error_Monad.forallM
                         (\ x ->
                           (if (case x of {
                                 (l, _) -> not (Term.is_Var l);
                               })
                             then Sum_Type.Inr () else Sum_Type.Inl x))
                         s)
                       (\ x -> Sum_Type.Inl (snd x)))
                     (\ _ ->
                       Sum_Type.Inl
                         (Shows_Literal.showsl_lit
                           "lhss must not be variables")))));

}
