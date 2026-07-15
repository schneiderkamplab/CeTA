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
import qualified Renaming2;
import qualified Fresh;
import qualified Quasi_Order;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified HOL;
import qualified Check_Joins;
import qualified Sum_Type;
import qualified Term_Rewriting;
import qualified Mapping;
import qualified Shows_Literal;
import qualified Compare;
import qualified Arith;

check_cpeak_eld ::
  forall a b.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a, Arith.Ccompare b,
      Compare.Compare b, Eq b, Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => [((Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b),
                                   Arith.Nat)] ->
                                  ((Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b) ->
                                    Arith.Nat) ->
                                    ((Term_Rewriting.Term a b,
                                       ((Term_Rewriting.Term a b,
  Term_Rewriting.Term a b),
 ([Arith.Nat],
   (b -> Term_Rewriting.Term a b, (Bool, Term_Rewriting.Term a b))))),
                                      (Term_Rewriting.Term a b,
((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
  ([Arith.Nat],
    (b -> Term_Rewriting.Term a b, (Bool, Term_Rewriting.Term a b)))))) ->
                                      Check_Joins.Crit_pair_info a b ->
Sum_Type.Sum (String -> String) ();
check_cpeak_eld lR lab p cp_info =
  (case p of {
    ((_, (r1, (_, (_, (True, t1))))), (_, (r2, (_, (_, (True, t2)))))) ->
      let {
        cp = (Check_Joins.cp_left cp_info, Check_Joins.cp_right cp_info);
      } in Error_Monad.bind
             (Check_Monad.check (Term_Rewriting.instance_rule (t1, t2) cp) id)
             (\ _ ->
               let {
                 alpha = lab r1;
                 beta = lab r2;
                 r1a = Arith.map_filter
                         (\ x ->
                           (if Arith.less_nat (snd x) alpha then Just (fst x)
                             else Nothing))
                         lR;
                 r2a = Arith.map_filter
                         (\ x ->
                           (if Arith.less_eq_nat (snd x) beta then Just (fst x)
                             else Nothing))
                         lR;
                 r3 = Arith.map_filter
                        (\ x ->
                          (if Arith.less_nat (snd x)
                                (Quasi_Order.max alpha beta)
                            then Just (fst x) else Nothing))
                        lR;
                 r4 = Arith.map_filter
                        (\ x ->
                          (if Arith.less_eq_nat (snd x) alpha then Just (fst x)
                            else Nothing))
                        lR;
                 r5 = Arith.map_filter
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
    (Compare.Compare a, Eq a, Shows_Literal.Showl a, Arith.Ccompare b,
      Compare.Compare b, Eq b, Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => [(Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b)] ->
                                  [((Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b),
                                     Arith.Nat)] ->
                                    ((Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b) ->
                                      Arith.Nat) ->
                                      Maybe Arith.Nat ->
((Term_Rewriting.Term a b,
   ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
     ([Arith.Nat],
       (b -> Term_Rewriting.Term a b, (Bool, Term_Rewriting.Term a b))))),
  (Term_Rewriting.Term a b,
    ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
      ([Arith.Nat],
        (b -> Term_Rewriting.Term a b, (Bool, Term_Rewriting.Term a b)))))) ->
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
                 cp = Arith.the cpo;
               } in Error_Monad.bind
                      (Check_Monad.check
                        (case Term_Rewriting.match_list Term_Rewriting.Var
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
                                Arith.membera
                                  (Term_Rewriting.reachable_terms r cp m);
                            });
                          alpha = lab r1;
                          beta = lab r2;
                          r1a = Arith.map_filter
                                  (\ x ->
                                    (if Arith.less_nat (snd x) alpha
                                      then Just (fst x) else Nothing))
                                  lR;
                          r2a = Arith.map_filter
                                  (\ x ->
                                    (if Arith.less_eq_nat (snd x) beta
                                      then Just (fst x) else Nothing))
                                  lR;
                          r3 = Arith.map_filter
                                 (\ x ->
                                   (if Arith.less_nat (snd x)
 (Quasi_Order.max alpha beta)
                                     then Just (fst x) else Nothing))
                                 lR;
                          r4 = Arith.map_filter
                                 (\ x ->
                                   (if Arith.less_eq_nat (snd x) alpha
                                     then Just (fst x) else Nothing))
                                 lR;
                          r5 = Arith.map_filter
                                 (\ x ->
                                   (if Arith.less_nat (snd x) beta
                                     then Just (fst x) else Nothing))
                                 lR;
                        } in Check_Joins.check_generic_decreasing_sequence
                               (\ (s, t) ->
                                 (case (s, t) of {
                                   (a, b) ->
                                     Term_Rewriting.is_rstep (Arith.set r1a) a
                                       b;
                                 }) ||
                                   (case (t, s) of {
                                     (a, b) ->
                                       Term_Rewriting.is_rstep (Arith.set r1a) a
 b;
                                   }) &&
                                     reach t)
                               (\ (s, t) ->
                                 (case (s, t) of {
                                   (a, b) ->
                                     Term_Rewriting.is_rstep (Arith.set r2a) a
                                       b;
                                 }))
                               (\ (s, t) ->
                                 (case (s, t) of {
                                   (a, b) ->
                                     Term_Rewriting.is_rstep (Arith.set r3) a b;
                                 }) ||
                                   (case (t, s) of {
                                     (a, b) ->
                                       Term_Rewriting.is_rstep (Arith.set r3) a
 b;
                                   }) &&
                                     reach t)
                               (\ _ -> False)
                               (\ (s, t) ->
                                 (case (t, s) of {
                                   (a, b) ->
                                     Term_Rewriting.is_rstep (Arith.set r4) a b;
                                 }) &&
                                   reach t)
                               (\ (t, s) ->
                                 (case (s, t) of {
                                   (a, b) ->
                                     Term_Rewriting.is_rstep (Arith.set r5) a b;
                                 }) ||
                                   (case (t, s) of {
                                     (a, b) ->
                                       Term_Rewriting.is_rstep (Arith.set r5) a
 b;
                                   }) &&
                                     reach t)
                               " <->* . ->? . <->* . ?<- . <->* " cl cr
                               (Check_Joins.cp_join cp_info)));
  });

critical_peaks_impl ::
  forall a b.
    (Fresh.Infinite a, Eq a,
      Eq b) => Renaming2.Renaming2 a ->
                 [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
                   [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
                     [(Bool,
                        ((Term_Rewriting.Term b a,
                           ((Term_Rewriting.Term b a, Term_Rewriting.Term b a),
                             ([Arith.Nat],
                               (a -> Term_Rewriting.Term b a,
                                 (Bool, Term_Rewriting.Term b a))))),
                          (Term_Rewriting.Term b a,
                            ((Term_Rewriting.Term b a, Term_Rewriting.Term b a),
                              ([Arith.Nat],
                                (a -> Term_Rewriting.Term b a,
                                  (Bool, Term_Rewriting.Term b a)))))))];
critical_peaks_impl ren p r =
  concatMap
    (\ (l, ra) ->
      concatMap
        (\ pa ->
          let {
            c = Term_Rewriting.ctxt_of_pos_term pa l;
            la = Term_Rewriting.subt_at l pa;
            b = Term_Rewriting.equal_actxt c Term_Rewriting.Hole;
          } in (if Term_Rewriting.is_Var la then []
                 else concatMap
                        (\ (lb, rb) ->
                          (case Term_Rewriting.mgu_vd ren la lb of {
                            Nothing -> [];
                            Just (sigma, tau) ->
                              [(b, ((Term_Rewriting.eval_term Term_Rewriting.Fun
                                       l sigma,
                                      ((l, ra),
([], (sigma, (True, Term_Rewriting.eval_term Term_Rewriting.Fun ra sigma))))),
                                     (Term_Rewriting.eval_term
Term_Rewriting.Fun l sigma,
                                       ((lb, rb),
 (pa, (tau, (True,
              Term_Rewriting.intp_actxt Term_Rewriting.Fun
                (Term_Rewriting.map_actxt (\ x -> x)
                  (\ t -> Term_Rewriting.eval_term Term_Rewriting.Fun t sigma)
                  c)
                (Term_Rewriting.eval_term Term_Rewriting.Fun rb tau))))))))];
                          }))
                        r))
        (Term_Rewriting.poss_list l))
    p;

rule_lab_repr_to_lab ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare_order b) => [((Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b),
                                     Arith.Nat)] ->
                                    (Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b) ->
                                      Arith.Nat;
rule_lab_repr_to_lab ps =
  Option_Util.fun_of_map (Map_Choice.ceta_map_of ps) Arith.zero_nat;

check_rule_labeling_eld ::
  forall a b.
    (Arith.Ccompare a, Compare.Compare_order a, Fresh.Infinite a, Eq a,
      Mapping.Mapping_impl a, Shows_Literal.Showl a, Compare.Compare_order b,
      Eq b,
      Shows_Literal.Showl b) => Renaming2.Renaming2 a ->
                                  [(Term_Rewriting.Term b a,
                                     Term_Rewriting.Term b a)] ->
                                    [((Term_Rewriting.Term b a,
Term_Rewriting.Term b a),
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
                     (Check_Monad.check (Term_Rewriting.equal_term t1 t2)
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
                                 Term_Rewriting.showsl_rulea
                                   Shows_Literal.showsl Shows_Literal.showsl
                                   " <- . -> " (t1, t2)) .
                                Shows_Literal.showsl_lit
                                  " could not be joined decreasingly:\n") .
                               Shows_Literal.showsl_sep id id x))));
             })
               b)
           cps)
         (\ x -> Sum_Type.Inl (snd x));

check_rule_labeling_eldc ::
  forall a b.
    (Arith.Ccompare a, Compare.Compare_order a, Fresh.Infinite a, Eq a,
      Mapping.Mapping_impl a, Shows_Literal.Showl a, Compare.Compare_order b,
      Eq b,
      Shows_Literal.Showl b) => Renaming2.Renaming2 a ->
                                  [(Term_Rewriting.Term b a,
                                     Term_Rewriting.Term b a)] ->
                                    [((Term_Rewriting.Term b a,
Term_Rewriting.Term b a),
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
                     (Check_Monad.check (Term_Rewriting.equal_term t1 t2)
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
                                      Term_Rewriting.showsl_terma t1) .
                                     Shows_Literal.showsl_lit " <- ") .
                                    Term_Rewriting.showsl_terma s1) .
                                   Shows_Literal.showsl_lit " -> ") .
                                  Term_Rewriting.showsl_terma t2) .
                                 Shows_Literal.showsl_lit
                                   " could not be joined decreasingly:") .
                                Shows_Literal.showsl_literal "\n") .
                               Shows_Literal.showsl_sep id id x))));
             })
               b)
           cps)
         (\ x -> Sum_Type.Inl (snd x));

}
