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
import qualified Missing_List;
import qualified Map;
import qualified Util;
import qualified Usable_Rules_NJ_Unif_Impl;
import qualified Usable_Rules_NJ_Impl;
import qualified Position;
import qualified Check_Monad;
import qualified Tcap_Impl;
import qualified Check_Termination_Common;
import qualified Compare_Order_Instances;
import qualified Q_Restricted_Rewriting_Impl;
import qualified Error_Monad;
import qualified Compare;
import qualified HOL;
import qualified Labelings_Impl;
import qualified Labelings;
import qualified Mapping;
import qualified Shows_Literal;
import qualified Semantic_Labeling_Carrier;
import qualified Tree_Automata_Impl;
import qualified Sum_Type;
import qualified Term_Rewriting;
import qualified Arith;

data Non_join_info a b c d = Diff_NFs
  | Tcap_Non_Unif
      (Term_Rewriting.Term a b ->
        Term_Rewriting.Term a b -> b -> Term_Rewriting.Term a b)
  | Tree_Aut_Intersect_Empty (Tree_Automata_Impl.Tree_automaton c a)
      (Tree_Automata_Impl.Ta_relation c) (Tree_Automata_Impl.Tree_automaton c a)
      (Tree_Automata_Impl.Ta_relation c)
  | Finite_Model_Gt (Semantic_Labeling_Carrier.Sl_variant a b)
  | Discr_Pair_Gt (Term_Rewriting.Rel_impl_type a b d) d
  | Usable_Rules_Reach_NJ (Non_join_info a b c d)
  | Usable_Rules_Reach_Unif_NJ
      (Sum_Type.Sum [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]
        [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)])
      (Non_join_info a b c d)
  | Finitely_Reachable
  | Argument_Filter_NJ [((a, Arith.Nat), Term_Rewriting.Af_entry)]
      (Non_join_info a b c d)
  | Grounding [(b, Term_Rewriting.Term a b)] (Non_join_info a b c d)
  | Subterm_NJ [Arith.Nat] (Non_join_info a b c d);

is_non_joinable_finite_reachable_rtrancl ::
  forall a.
    (Arith.Ceq a, Arith.Ccompare a, Eq a, Arith.Set_impl a,
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
            Check_Monad.check (not (Arith.membera reach2 u))
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
                                      (Term_Rewriting.Term a c,
Term_Rewriting.Term a c) ->
Sum_Type.Sum (String -> String) ();
check_qmodel_rule_ass i cge alpha (l, r) =
  let {
    cl = Term_Rewriting.eval_term i l alpha;
    cr = Term_Rewriting.eval_term i r alpha;
  } in Check_Monad.check (cge cl cr)
         (((((Shows_Literal.showsl_lit "rule " .
               Term_Rewriting.showsl_rule (l, r)) .
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
                                      (Term_Rewriting.Term a c,
Term_Rewriting.Term a c) ->
Sum_Type.Sum (String -> String) ();
check_qmodel_rule i c cge lr =
  Error_Monad.catch_error
    (Error_Monad.forallM (\ alpha -> check_qmodel_rule_ass i cge alpha lr)
      (map Util.fun_of
        (Util.enum_vectors c (Term_Rewriting.insert_vars_rule lr []))))
    (\ x -> Sum_Type.Inl (snd x));

check_qmodel ::
  forall a b c.
    (Shows_Literal.Showl a, Shows_Literal.Showl b, Eq c,
      Shows_Literal.Showl c) => (a -> [b] -> b) ->
                                  [b] ->
                                    (b -> b -> Bool) ->
                                      [(Term_Rewriting.Term a c,
 Term_Rewriting.Term a c)] ->
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
                                    [(Term_Rewriting.Term b d,
                                       Term_Rewriting.Term b d)] ->
                                      [(Term_Rewriting.Term b d,
 Term_Rewriting.Term b d)] ->
Term_Rewriting.Term b d ->
  Term_Rewriting.Term b d -> Sum_Type.Sum (String -> String) ();
check_non_join_model cge gen rs rt s t =
  Error_Monad.catch_error
    (Error_Monad.bind (gen (Term_Rewriting.funas_trs_list (rs ++ rt)) [])
      (\ ops ->
        let {
          i = Semantic_Labeling_Impl.sl_I ops;
          e = (\ ta ->
                Term_Rewriting.eval_term i ta
                  (\ _ -> Semantic_Labeling_Impl.sl_c ops));
          es = e s;
          et = e t;
        } in Error_Monad.bind
               (Check_Monad.check (not (cge et es))
                 ((((((((Shows_Literal.showsl_lit
                           "the inequality must not hold: [" .
                          Term_Rewriting.showsl_terma t) .
                         Shows_Literal.showsl_lit "] = ") .
                        Shows_Literal.showsl et) .
                       Shows_Literal.showsl_lit " >= ") .
                      Shows_Literal.showsl es) .
                     Shows_Literal.showsl_lit " = [") .
                    Term_Rewriting.showsl_terma s) .
                   Shows_Literal.showsl_lit "]"))
               (\ _ ->
                 check_qmodel i (Semantic_Labeling_Impl.sl_C ops) cge
                   (Term_Rewriting.reverse_rules rs ++ rt))))
    (\ x ->
      Sum_Type.Inl
        ((Shows_Literal.showsl_lit
            "problem in disproving non-joinability via interpretations" .
           Shows_Literal.showsl_literal "\n") .
          x));

check_non_join_finite_model ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => Semantic_Labeling_Carrier.Sl_variant
                                  (Labelings.Lab a [Arith.Nat]) b ->
                                  [(Term_Rewriting.Term
                                      (Labelings.Lab a [Arith.Nat]) b,
                                     Term_Rewriting.Term
                                       (Labelings.Lab a [Arith.Nat]) b)] ->
                                    [(Term_Rewriting.Term
(Labelings.Lab a [Arith.Nat]) b,
                                       Term_Rewriting.Term
 (Labelings.Lab a [Arith.Nat]) b)] ->
                                      Term_Rewriting.Term
(Labelings.Lab a [Arith.Nat]) b ->
Term_Rewriting.Term (Labelings.Lab a [Arith.Nat]) b ->
  Sum_Type.Sum (String -> String) ();
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
      Shows_Literal.Showl b) => Term_Rewriting.Rel_impl_ext a b () ->
                                  [(Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b)] ->
                                    [(Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b)] ->
                                      Term_Rewriting.Term a b ->
Term_Rewriting.Term a b -> Sum_Type.Sum (String -> String) ();
check_non_join_discr_pair rp rs rt s t =
  Error_Monad.catch_error
    (Error_Monad.bind (Term_Rewriting.rel_impl_co_discrimination_pair rp)
      (\ _ ->
        Error_Monad.bind
          (Term_Rewriting.rel_impl_ns rp
            (Term_Rewriting.reverse_rules rs ++ rt))
          (\ _ -> Term_Rewriting.s rp (s, t))))
    (\ x ->
      Sum_Type.Inl
        ((Shows_Literal.showsl_lit
            "problem in disproving non-joinability via co-discrimination pairs" .
           Shows_Literal.showsl_literal "\n") .
          x));

check_non_join ::
  forall a b c.
    (Compare.Compare_order a, HOL.Default a, Eq a, Shows_Literal.Showl a,
      Arith.Card_UNIV b, Arith.Cenum b, Arith.Ceq b, Arith.Cproper_interval b,
      Compare.Compare_order b, Eq b, Arith.Set_impl b,
      Shows_Literal.Showl b) => [(Term_Rewriting.Term
                                    (Labelings.Lab a [Arith.Nat]) [Arith.Char],
                                   Term_Rewriting.Term
                                     (Labelings.Lab a [Arith.Nat])
                                     [Arith.Char])] ->
                                  [(Term_Rewriting.Term
                                      (Labelings.Lab a [Arith.Nat])
                                      [Arith.Char],
                                     Term_Rewriting.Term
                                       (Labelings.Lab a [Arith.Nat])
                                       [Arith.Char])] ->
                                    Term_Rewriting.Term
                                      (Labelings.Lab a [Arith.Nat])
                                      [Arith.Char] ->
                                      Term_Rewriting.Term
(Labelings.Lab a [Arith.Nat]) [Arith.Char] ->
Non_join_info (Labelings.Lab a [Arith.Nat]) [Arith.Char] b c ->
  Sum_Type.Sum (String -> String) ();
check_non_join rs rt s t Diff_NFs =
  Error_Monad.bind
    (Check_Monad.check (not (Term_Rewriting.equal_term s t))
      ((((Shows_Literal.showsl_lit "the terms " .
           Term_Rewriting.showsl_terma s) .
          Shows_Literal.showsl_lit " and ") .
         Term_Rewriting.showsl_terma t) .
        Shows_Literal.showsl_lit " are identical"))
    (\ _ ->
      let {
        chknf =
          (\ sa r ->
            Check_Monad.check (Term_Rewriting.is_NF_trs r sa)
              ((Shows_Literal.showsl_lit "the term " .
                 Term_Rewriting.showsl_terma sa) .
                Shows_Literal.showsl_lit " is not in normal form"));
      } in Error_Monad.bind (chknf s rs) (\ _ -> chknf t rt));
check_non_join rs rt s t (Grounding sigma prf) =
  let {
    sigmaa = Term_Rewriting.mk_subst Term_Rewriting.Var sigma;
  } in check_non_join rs rt
         (Term_Rewriting.eval_term Term_Rewriting.Fun s sigmaa)
         (Term_Rewriting.eval_term Term_Rewriting.Fun t sigmaa) prf;
check_non_join rs rt s t (Subterm_NJ p prf) =
  Error_Monad.bind
    (Check_Monad.check
      (Arith.member p (Term_Rewriting.pos_gctxt (Tcap_Impl.tcapI rs s)))
      (((Shows_Literal.showsl_lit "position " . Position.showsl_pos p) .
         Shows_Literal.showsl_lit " not in capped term  of ") .
        Term_Rewriting.showsl_terma s))
    (\ _ ->
      Error_Monad.bind
        (Check_Monad.check
          (Arith.member p (Term_Rewriting.pos_gctxt (Tcap_Impl.tcapI rt t)))
          (((Shows_Literal.showsl_lit "position " . Position.showsl_pos p) .
             Shows_Literal.showsl_lit " not in capped term  of ") .
            Term_Rewriting.showsl_terma t))
        (\ _ ->
          check_non_join rs rt (Term_Rewriting.subt_at s p)
            (Term_Rewriting.subt_at t p) prf));
check_non_join rs rt s t (Tcap_Non_Unif grd_subst) =
  let {
    sigma = grd_subst s t;
    cs = Tcap_Impl.tcapI rs
           (Term_Rewriting.eval_term Term_Rewriting.Fun s sigma);
    ct = Tcap_Impl.tcapI rt
           (Term_Rewriting.eval_term Term_Rewriting.Fun t sigma);
  } in Check_Monad.check (Arith.is_none (Term_Rewriting.merge cs ct))
         ((((Shows_Literal.showsl_lit "could not infer that " .
              Term_Rewriting.showsl_terma s) .
             Shows_Literal.showsl_lit " and ") .
            Term_Rewriting.showsl_terma t) .
           Shows_Literal.showsl_lit " are not joinable");
check_non_join rs rt s t (Tree_Aut_Intersect_Empty ta1 rel1 ta2 rel2) =
  Error_Monad.catch_error
    (Tree_Automata_Impl.non_join_with_ta ta1 rel1 rs s ta2 rel2 rt t)
    (\ x ->
      Sum_Type.Inl
        ((((((Shows_Literal.showsl_lit "could not infer that " .
               Term_Rewriting.showsl_terma s) .
              Shows_Literal.showsl_lit " and ") .
             Term_Rewriting.showsl_terma t) .
            Shows_Literal.showsl_lit " are not joinable") .
           Shows_Literal.showsl_literal "\n") .
          x));
check_non_join rs rt s t (Finite_Model_Gt i) =
  Error_Monad.catch_error (check_non_join_finite_model i rs rt s t)
    (\ x ->
      Sum_Type.Inl
        ((((((Shows_Literal.showsl_lit "could not infer that " .
               Term_Rewriting.showsl_terma s) .
              Shows_Literal.showsl_lit " and ") .
             Term_Rewriting.showsl_terma t) .
            Shows_Literal.showsl_lit " are not joinable") .
           Shows_Literal.showsl_literal "\n") .
          x));
check_non_join rs rt s t (Discr_Pair_Gt grt rp) =
  Error_Monad.catch_error
    (Check_Monad.or_ok
      (check_non_join_discr_pair (Term_Rewriting.rel_impl_of grt rp) rs rt s t)
      (check_non_join_discr_pair (Term_Rewriting.rel_impl_of grt rp) rt rs t s))
    (\ _ ->
      Sum_Type.Inl
        ((((Shows_Literal.showsl_lit "could not infer that " .
             Term_Rewriting.showsl_terma s) .
            Shows_Literal.showsl_lit " and ") .
           Term_Rewriting.showsl_terma t) .
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
  Error_Monad.bind (Term_Rewriting.check_wf_trs rs)
    (\ _ ->
      Error_Monad.bind (Term_Rewriting.check_wf_trs rt)
        (\ _ ->
          Error_Monad.catch_error
            (is_non_joinable_finite_reachable_rtrancl
              (Term_Rewriting.rewrite rs) (Term_Rewriting.rewrite rt) s t)
            (\ _ ->
              Sum_Type.Inl
                ((((Shows_Literal.showsl_lit "could not infer that " .
                     Term_Rewriting.showsl_terma s) .
                    Shows_Literal.showsl_lit " and ") .
                   Term_Rewriting.showsl_terma t) .
                  Shows_Literal.showsl_lit
                    " are not joinable by finitely reachable terms"))));
check_non_join rs rt s t (Argument_Filter_NJ pi prf) =
  (case Term_Rewriting.afs_of pi of {
    Nothing ->
      Sum_Type.Inl (Shows_Literal.showsl_lit "invalid argument filter");
    Just pia -> let {
                  af = Term_Rewriting.af_term pia;
                  afs = Term_Rewriting.af_rules pia;
                } in check_non_join (afs rs) (afs rt) (af s) (af t) prf;
  });

check_non_cr ::
  forall a b c.
    (Compare.Compare_order a, HOL.Default a, Eq a, Shows_Literal.Showl a,
      Arith.Card_UNIV b, Arith.Cenum b, Arith.Ceq b, Arith.Cproper_interval b,
      Compare.Compare_order b, Eq b, Arith.Set_impl b,
      Shows_Literal.Showl b) => [(Term_Rewriting.Term
                                    (Labelings.Lab a [Arith.Nat]) [Arith.Char],
                                   Term_Rewriting.Term
                                     (Labelings.Lab a [Arith.Nat])
                                     [Arith.Char])] ->
                                  Term_Rewriting.Term
                                    (Labelings.Lab a [Arith.Nat])
                                    [Arith.Char] ->
                                    [([Arith.Nat],
                                       ((Term_Rewriting.Term
   (Labelings.Lab a [Arith.Nat]) [Arith.Char],
  Term_Rewriting.Term (Labelings.Lab a [Arith.Nat]) [Arith.Char]),
 Term_Rewriting.Term (Labelings.Lab a [Arith.Nat]) [Arith.Char]))] ->
                                      [([Arith.Nat],
 ((Term_Rewriting.Term (Labelings.Lab a [Arith.Nat]) [Arith.Char],
    Term_Rewriting.Term (Labelings.Lab a [Arith.Nat]) [Arith.Char]),
   Term_Rewriting.Term (Labelings.Lab a [Arith.Nat]) [Arith.Char]))] ->
Non_join_info (Labelings.Lab a [Arith.Nat]) [Arith.Char] b c ->
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
    (Eq a, Shows_Literal.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => [((Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b),
                                   [([Arith.Nat],
                                      ((Term_Rewriting.Term a b,
 Term_Rewriting.Term a b),
Term_Rewriting.Term a b))])] ->
                                  c -> [(Term_Rewriting.Term a b,
  Term_Rewriting.Term a b)] ->
 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
   Sum_Type.Sum (String -> String) ();
check_rule_removal infos r rdel s =
  Error_Monad.catch_error
    (let {
       f = Term_Rewriting.funas_trs_list s;
       rs = filter
              (\ lr ->
                all (Arith.membera f) (Term_Rewriting.funas_term_list (fst lr)))
              rdel;
     } in Error_Monad.bind (Term_Rewriting.check_wf_trs s)
            (\ _ ->
              Error_Monad.catch_error
                (Error_Monad.forallM
                  (\ lr ->
                    (case Map.map_of infos lr of {
                      Nothing ->
                        Sum_Type.Inl
                          (Shows_Literal.showsl_lit
                             "did not find info for rule: " .
                            Term_Rewriting.showsl_rule lr);
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
    (Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a, Eq a, Arith.Set_impl a,
      Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => [(Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b)] ->
                                  [(Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b)] ->
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
        f = Term_Rewriting.funas_trs_list r;
        g = Term_Rewriting.funas_trs_list s;
      } in Error_Monad.bind
             (Check_Monad.check
               (Arith.less_eq_set (Arith.inf_set (Arith.set f) (Arith.set g))
                 Arith.bot_set)
               (Shows_Literal.showsl_lit "signatures are not disjoint"))
             (\ _ ->
               Error_Monad.bind (Term_Rewriting.check_varcond_subset r)
                 (\ _ ->
                   Error_Monad.catch_error
                     (Error_Monad.catch_error
                       (Error_Monad.forallM
                         (\ x ->
                           (if (case x of {
                                 (l, _) -> not (Term_Rewriting.is_Var l);
                               })
                             then Sum_Type.Inr () else Sum_Type.Inl x))
                         s)
                       (\ x -> Sum_Type.Inl (snd x)))
                     (\ _ ->
                       Sum_Type.Inl
                         (Shows_Literal.showsl_lit
                           "lhss must not be variables")))));

}
