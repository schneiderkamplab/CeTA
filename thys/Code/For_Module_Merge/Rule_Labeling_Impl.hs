{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Rule_Labeling_Impl(rule_lab_repr_to_lab, check_rule_labeling_eld,
                      check_rule_labeling_eldc)
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
import qualified Option_Util;
import qualified Map_Choice;
import qualified Compare_Order_Instances;
import qualified Term_Impl;
import qualified Unification;
import qualified Term_More;
import qualified Subterm_and_Context;
import qualified Renaming2;
import qualified Fresh;
import qualified Matching;
import qualified Trs_Impl;
import qualified Option;
import qualified Set;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Container_Setup;
import qualified Product_Type;
import qualified Orderings;
import qualified Trs;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified List;
import qualified HOL;
import qualified Check_Joins;
import qualified Sum_Type;
import qualified Term;
import qualified Mapping_Impl;
import qualified Collection_Order;
import qualified Shows_Literal;
import qualified Compare;
import qualified Arith;

check_cpeak_eld ::
  forall a b.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a,
      Collection_Order.Ccompare b, Compare.Compare b, Eq b,
      Mapping_Impl.Mapping_impl b,
      Shows_Literal.Showl b) => [((Term.Term a b, Term.Term a b), Arith.Nat)] ->
                                  ((Term.Term a b, Term.Term a b) ->
                                    Arith.Nat) ->
                                    ((Term.Term a b,
                                       ((Term.Term a b, Term.Term a b),
 ([Arith.Nat], (b -> Term.Term a b, (Bool, Term.Term a b))))),
                                      (Term.Term a b,
((Term.Term a b, Term.Term a b),
  ([Arith.Nat], (b -> Term.Term a b, (Bool, Term.Term a b)))))) ->
                                      Check_Joins.Crit_pair_info a b ->
Sum_Type.Sum (String -> String) ();
check_cpeak_eld lR lab p cp_info =
  (case p of {
    ((_, (r1, (_, (_, (True, t1))))), (_, (r2, (_, (_, (True, t2)))))) ->
      let {
        cp = (Check_Joins.cp_left cp_info, Check_Joins.cp_right cp_info);
      } in Error_Monad.bind
             (Check_Monad.check (Trs.instance_rule (t1, t2) cp) id)
             (\ _ ->
               let {
                 alpha = lab r1;
                 beta = lab r2;
                 r1a = List.map_filter
                         (\ x ->
                           (if Arith.less_nat (snd x) alpha then Just (fst x)
                             else Nothing))
                         lR;
                 r2a = List.map_filter
                         (\ x ->
                           (if Arith.less_eq_nat (snd x) beta then Just (fst x)
                             else Nothing))
                         lR;
                 r3 = List.map_filter
                        (\ x ->
                          (if Arith.less_nat (snd x) (Orderings.max alpha beta)
                            then Just (fst x) else Nothing))
                        lR;
                 r4 = List.map_filter
                        (\ x ->
                          (if Arith.less_eq_nat (snd x) alpha then Just (fst x)
                            else Nothing))
                        lR;
                 r5 = List.map_filter
                        (\ x ->
                          (if Arith.less_nat (snd x) beta then Just (fst x)
                            else Nothing))
                        lR;
               } in Check_Joins.check_rl_decreasing_sequence r1a r2a r3 r4 r5
                      (Check_Joins.cp_left cp_info)
                      (Check_Joins.cp_right cp_info)
                      (Check_Joins.cp_join cp_info));
  });

check_cpeak_eldc ::
  forall a b.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a,
      Collection_Order.Ccompare b, Compare.Compare b, Eq b,
      Mapping_Impl.Mapping_impl b,
      Shows_Literal.Showl b) => [(Term.Term a b, Term.Term a b)] ->
                                  [((Term.Term a b, Term.Term a b),
                                     Arith.Nat)] ->
                                    ((Term.Term a b, Term.Term a b) ->
                                      Arith.Nat) ->
                                      Maybe Arith.Nat ->
((Term.Term a b,
   ((Term.Term a b, Term.Term a b),
     ([Arith.Nat], (b -> Term.Term a b, (Bool, Term.Term a b))))),
  (Term.Term a b,
    ((Term.Term a b, Term.Term a b),
      ([Arith.Nat], (b -> Term.Term a b, (Bool, Term.Term a b)))))) ->
  Check_Joins.Crit_pair_info a b -> Sum_Type.Sum (String -> String) ();
check_cpeak_eldc r lR lab n p cp_info =
  (case p of {
    ((s1, (r1, (_, (_, (True, t1))))), (_, (r2, (_, (_, (True, t2)))))) ->
      let {
        cl = Check_Joins.cp_left cp_info;
        cr = Check_Joins.cp_right cp_info;
        cpo = Check_Joins.cp_peak cp_info;
      } in Error_Monad.bind
             (Check_Monad.check (case cpo of {
                                  Nothing -> False;
                                  Just _ -> True;
                                })
               (Shows_Literal.showsl_lit
                 "critical pair info does not specify peak"))
             (\ _ ->
               let {
                 cp = Option.the cpo;
               } in Error_Monad.bind
                      (Check_Monad.check
                        (case Matching.match_list Term.Var
                                [(cl, t1), (cr, t2), (cp, s1)]
                          of {
                          Nothing -> False;
                          Just _ -> True;
                        })
                        (Shows_Literal.showsl_lit
                          "crit-pair info does not fit to this critical pair"))
                      (\ _ ->
                        let {
                          reach =
                            (case n of {
                              Nothing -> (\ _ -> True);
                              Just m ->
                                List.member (Trs_Impl.reachable_terms r cp m);
                            });
                          alpha = lab r1;
                          beta = lab r2;
                          r1a = List.map_filter
                                  (\ x ->
                                    (if Arith.less_nat (snd x) alpha
                                      then Just (fst x) else Nothing))
                                  lR;
                          r2a = List.map_filter
                                  (\ x ->
                                    (if Arith.less_eq_nat (snd x) beta
                                      then Just (fst x) else Nothing))
                                  lR;
                          r3 = List.map_filter
                                 (\ x ->
                                   (if Arith.less_nat (snd x)
 (Orderings.max alpha beta)
                                     then Just (fst x) else Nothing))
                                 lR;
                          r4 = List.map_filter
                                 (\ x ->
                                   (if Arith.less_eq_nat (snd x) alpha
                                     then Just (fst x) else Nothing))
                                 lR;
                          r5 = List.map_filter
                                 (\ x ->
                                   (if Arith.less_nat (snd x) beta
                                     then Just (fst x) else Nothing))
                                 lR;
                        } in Check_Joins.check_generic_decreasing_sequence
                               (\ (s, t) ->
                                 (case (s, t) of {
                                   (a, b) ->
                                     Trs_Impl.is_rstep (List.set r1a) a b;
                                 }) ||
                                   (case (t, s) of {
                                     (a, b) ->
                                       Trs_Impl.is_rstep (List.set r1a) a b;
                                   }) &&
                                     reach t)
                               (\ (s, t) ->
                                 (case (s, t) of {
                                   (a, b) ->
                                     Trs_Impl.is_rstep (List.set r2a) a b;
                                 }))
                               (\ (s, t) ->
                                 (case (s, t) of {
                                   (a, b) ->
                                     Trs_Impl.is_rstep (List.set r3) a b;
                                 }) ||
                                   (case (t, s) of {
                                     (a, b) ->
                                       Trs_Impl.is_rstep (List.set r3) a b;
                                   }) &&
                                     reach t)
                               (\ _ -> False)
                               (\ (s, t) ->
                                 (case (t, s) of {
                                   (a, b) ->
                                     Trs_Impl.is_rstep (List.set r4) a b;
                                 }) &&
                                   reach t)
                               (\ (t, s) ->
                                 (case (s, t) of {
                                   (a, b) ->
                                     Trs_Impl.is_rstep (List.set r5) a b;
                                 }) ||
                                   (case (t, s) of {
                                     (a, b) ->
                                       Trs_Impl.is_rstep (List.set r5) a b;
                                   }) &&
                                     reach t)
                               " <->* . ->? . <->* . ?<- . <->* " cl cr
                               (Check_Joins.cp_join cp_info)));
  });

critical_peaks_impl ::
  forall a b.
    (Fresh.Infinite a, Eq a,
      Eq b) => Renaming2.Renaming2 a ->
                 [(Term.Term b a, Term.Term b a)] ->
                   [(Term.Term b a, Term.Term b a)] ->
                     [(Bool,
                        ((Term.Term b a,
                           ((Term.Term b a, Term.Term b a),
                             ([Arith.Nat],
                               (a -> Term.Term b a, (Bool, Term.Term b a))))),
                          (Term.Term b a,
                            ((Term.Term b a, Term.Term b a),
                              ([Arith.Nat],
                                (a -> Term.Term b a,
                                  (Bool, Term.Term b a)))))))];
critical_peaks_impl ren p r =
  concatMap
    (\ (l, ra) ->
      concatMap
        (\ pa ->
          let {
            c = Term_More.ctxt_of_pos_term pa l;
            la = Term_More.subt_at l pa;
            b = Subterm_and_Context.equal_actxt c Subterm_and_Context.Hole;
          } in (if Term.is_Var la then []
                 else concatMap
                        (\ (lb, rb) ->
                          (case Unification.mgu_vd ren la lb of {
                            Nothing -> [];
                            Just (sigma, tau) ->
                              [(b, ((Term.eval_term Term.Fun l sigma,
                                      ((l, ra),
([], (sigma, (True, Term.eval_term Term.Fun ra sigma))))),
                                     (Term.eval_term Term.Fun l sigma,
                                       ((lb, rb),
 (pa, (tau, (True,
              Subterm_and_Context.intp_actxt Term.Fun
                (Subterm_and_Context.map_actxt (\ x -> x)
                  (\ t -> Term.eval_term Term.Fun t sigma) c)
                (Term.eval_term Term.Fun rb tau))))))))];
                          }))
                        r))
        (Term_Impl.poss_list l))
    p;

rule_lab_repr_to_lab ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare_order b) => [((Term.Term a b, Term.Term a b),
                                     Arith.Nat)] ->
                                    (Term.Term a b, Term.Term a b) -> Arith.Nat;
rule_lab_repr_to_lab ps =
  Option_Util.fun_of_map (Map_Choice.ceta_map_of ps) Arith.zero_nat;

check_rule_labeling_eld ::
  forall a b.
    (Collection_Order.Ccompare a, Compare.Compare_order a, Fresh.Infinite a,
      Eq a, Mapping_Impl.Mapping_impl a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => Renaming2.Renaming2 a ->
                                  [(Term.Term b a, Term.Term b a)] ->
                                    [((Term.Term b a, Term.Term b a),
                                       Arith.Nat)] ->
                                      [Check_Joins.Crit_pair_info b a] ->
Sum_Type.Sum (String -> String) ();
check_rule_labeling_eld ren r lab cp_infos =
  let {
    cps = critical_peaks_impl ren r r;
    l = rule_lab_repr_to_lab lab;
    lR = map (\ ra -> (ra, l ra)) r;
  } in Error_Monad.catch_error
         (Error_Monad.forallM
           (\ (_, (a, b)) ->
             (case a of {
               (s1, (r1, (p1, (sigma_1, (_, t1))))) ->
                 (\ (s2, (r2, (p2, (sigma_2, (true, t2))))) ->
                   Error_Monad.catch_error
                     (Check_Monad.check (Term.equal_term t1 t2)
                       (Shows_Literal.showsl_lit " pair non-trivial "))
                     (\ _ ->
                       Error_Monad.catch_error
                         (Error_Monad.existsM
                           (check_cpeak_eld lR l
                             ((s1, (r1, (p1, (sigma_1, (true, t1))))),
                               (s2, (r2, (p2, (sigma_2, (true, t2)))))))
                           cp_infos)
                         (\ x ->
                           Sum_Type.Inl
                             (((Shows_Literal.showsl_lit
                                  "\nthe critical peak " .
                                 Trs_Impl.showsl_rulea Shows_Literal.showsl
                                   Shows_Literal.showsl " <- . -> " (t1, t2)) .
                                Shows_Literal.showsl_lit
                                  " could not be joined decreasingly:\n") .
                               Shows_Literal.showsl_sep id id x))));
             })
               b)
           cps)
         (\ x -> Sum_Type.Inl (snd x));

check_rule_labeling_eldc ::
  forall a b.
    (Collection_Order.Ccompare a, Compare.Compare_order a, Fresh.Infinite a,
      Eq a, Mapping_Impl.Mapping_impl a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => Renaming2.Renaming2 a ->
                                  [(Term.Term b a, Term.Term b a)] ->
                                    [((Term.Term b a, Term.Term b a),
                                       Arith.Nat)] ->
                                      [Check_Joins.Crit_pair_info b a] ->
Maybe Arith.Nat -> Sum_Type.Sum (String -> String) ();
check_rule_labeling_eldc ren r lab cp_infos n =
  let {
    cps = critical_peaks_impl ren r r;
    l = rule_lab_repr_to_lab lab;
    lR = map (\ ra -> (ra, l ra)) r;
  } in Error_Monad.catch_error
         (Error_Monad.forallM
           (\ (_, (a, b)) ->
             (case a of {
               (s1, (r1, (p1, (sigma_1, (_, t1))))) ->
                 (\ (s2, (r2, (p2, (sigma_2, (true, t2))))) ->
                   Error_Monad.catch_error
                     (Check_Monad.check (Term.equal_term t1 t2)
                       (Shows_Literal.showsl_lit " pair non-trivial "))
                     (\ _ ->
                       Error_Monad.catch_error
                         (Error_Monad.existsM
                           (check_cpeak_eldc r lR l n
                             ((s1, (r1, (p1, (sigma_1, (true, t1))))),
                               (s2, (r2, (p2, (sigma_2, (true, t2)))))))
                           cp_infos)
                         (\ x ->
                           Sum_Type.Inl
                             (((((((((Shows_Literal.showsl_literal "\n" .
                                       Shows_Literal.showsl_lit
 "the critical peak ") .
                                      Term_More.showsl_terma t1) .
                                     Shows_Literal.showsl_lit " <- ") .
                                    Term_More.showsl_terma s1) .
                                   Shows_Literal.showsl_lit " -> ") .
                                  Term_More.showsl_terma t2) .
                                 Shows_Literal.showsl_lit
                                   " could not be joined decreasingly:") .
                                Shows_Literal.showsl_literal "\n") .
                               Shows_Literal.showsl_sep id id x))));
             })
               b)
           cps)
         (\ x -> Sum_Type.Inl (snd x));

}
