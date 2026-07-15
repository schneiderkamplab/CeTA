{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Parallel_Critical_Pairs_Impl(Pcp_rule_lab(..), Pcp_rule_lab_com(..),
                                check_pcp_rule_lab, check_pcp_rule_lab_com,
                                check_compositional_PCPS,
                                check_compositional_PCPS_com,
                                check_compositional_pcp_rule_lab,
                                check_compositional_parallel_pairs,
                                check_compositional_pcp_rule_lab_comm,
                                check_parallel_critical_pairs_closed_CR,
                                check_parallel_critical_pairs_closed_comm)
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
import qualified Mgu_generic;
import qualified Utility;
import qualified Critical_Pairs_Impl;
import qualified Rewrite_Relations_Impl;
import qualified Finite_Renaming;
import qualified Missing_List;
import qualified Quasi_Order;
import qualified Position;
import qualified Check_Monad;
import qualified List_Lexorder;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Shows_Literal;
import qualified Compare;
import qualified HOL;
import qualified Mapping;
import qualified Parallel_Critical_Pairs;
import qualified RenamingN;
import qualified Renaming2;
import qualified Fresh;
import qualified Check_Joins;
import qualified Term_Rewriting;
import qualified Arith;

data Pcp_rule_lab a b =
  PCP_Sequences
    ((Term_Rewriting.Term a b, Term_Rewriting.Term a b) -> Arith.Nat)
    (Check_Joins.Cp_join_hints a b);

data Pcp_rule_lab_com a b =
  PCP_Sequences_Com
    ((Term_Rewriting.Term a b, Term_Rewriting.Term a b) -> Arith.Nat)
    (Maybe ((Term_Rewriting.Term a b, Term_Rewriting.Term a b) -> Arith.Nat))
    (Check_Joins.Cp_join_hints a b) (Check_Joins.Cp_join_hints a b);

r_le_impl ::
  forall a b.
    [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
      ((Term_Rewriting.Term a b, Term_Rewriting.Term a b) -> Arith.Nat) ->
        Arith.Nat -> [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
r_le_impl r phi k =
  concatMap (\ lr -> (if Arith.less_eq_nat (phi lr) k then [lr] else [])) r;

split_num :: Arith.Nat -> [(Arith.Nat, (Arith.Nat, (Arith.Nat, Arith.Nat)))];
split_num n =
  concatMap
    (\ n1 ->
      concatMap
        (\ n2 ->
          concatMap
            (\ n3 ->
              map (\ n4 -> (n1, (n2, (n3, n4))))
                (Arith.upt Arith.zero_nat
                  (Arith.suc
                    (Arith.minus_nat (Arith.minus_nat (Arith.minus_nat n n1) n2)
                      n3))))
            (Arith.upt Arith.zero_nat
              (Arith.suc (Arith.minus_nat (Arith.minus_nat n n2) n1))))
        (Arith.upt Arith.zero_nat (Arith.suc (Arith.minus_nat n n1))))
    (Arith.upt Arith.zero_nat (Arith.suc n));

crit_rules ::
  forall a b.
    (Fresh.Infinite a, Eq a,
      Eq b) => RenamingN.RenamingN a ->
                 [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
                   Term_Rewriting.Term b a ->
                     [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)];
crit_rules ren r lp =
  filter
    (\ lr ->
      not (Arith.is_none
            (Term_Rewriting.mgu_vd (Parallel_Critical_Pairs.renaming2 ren)
              (fst lr) lp)))
    r;

matching_cp ::
  forall a b c d.
    (Eq c, Arith.Ccompare d, Eq d,
      Mapping.Mapping_impl d) => (Term_Rewriting.Mctxt a b,
                                   (Term_Rewriting.Term c d,
                                     (Term_Rewriting.Term c d,
                                       Term_Rewriting.Term c d))) ->
                                   Check_Joins.Crit_pair_info c d -> Bool;
matching_cp cp given =
  (case cp of {
    (c, (s, (t, u))) ->
      let {
        real_cp = [s, t, u];
        cert_cp =
          [Check_Joins.cp_left given, Check_Joins.cpPeak given,
            Check_Joins.cp_right given];
      } in not (Arith.is_none
                 (Term_Rewriting.match_list Term_Rewriting.Var
                   (zip real_cp cert_cp))) &&
             not (Arith.is_none
                   (Term_Rewriting.match_list Term_Rewriting.Var
                     (zip cert_cp real_cp))) &&
               (case Check_Joins.cp_poss given of {
                 Nothing -> False;
                 Just ps ->
                   Arith.set_eq (Arith.set ps) (Term_Rewriting.hole_poss c);
               });
  });

rS_conv_impl ::
  forall a b.
    [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
        ((Term_Rewriting.Term a b, Term_Rewriting.Term a b) -> Arith.Nat) ->
          ((Term_Rewriting.Term a b, Term_Rewriting.Term a b) -> Arith.Nat) ->
            Arith.Nat -> [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
rS_conv_impl r s phi psi k =
  concatMap
    (\ (l, ra) -> (if Arith.less_nat (phi (l, ra)) k then [(ra, l)] else []))
    r ++
    concatMap
      (\ (l, ra) -> (if Arith.less_nat (psi (l, ra)) k then [(l, ra)] else []))
      s;

matching_peak ::
  forall a b c d.
    (Eq c, Arith.Ccompare d, Eq d,
      Mapping.Mapping_impl d) => (Term_Rewriting.Mctxt a b,
                                   (Term_Rewriting.Term c d,
                                     (Term_Rewriting.Term c d,
                                       (Term_Rewriting.Term c d,
 (Arith.Nat, Arith.Nat))))) ->
                                   Check_Joins.Crit_pair_info c d -> Bool;
matching_peak cp given =
  (case cp of {
    (c, (s, (t, (u, (k, m))))) ->
      Check_Joins.cp_labels given == Just (k, m) &&
        let {
          real_cp = [s, t, u];
          cert_cp =
            [Check_Joins.cp_left given, Check_Joins.cpPeak given,
              Check_Joins.cp_right given];
        } in not (Arith.is_none
                   (Term_Rewriting.match_list Term_Rewriting.Var
                     (zip real_cp cert_cp))) &&
               not (Arith.is_none
                     (Term_Rewriting.match_list Term_Rewriting.Var
                       (zip cert_cp real_cp))) &&
                 (case Check_Joins.cp_poss given of {
                   Nothing -> False;
                   Just ps ->
                     Arith.set_eq (Arith.set ps) (Term_Rewriting.hole_poss c);
                 });
  });

potential_overlaps ::
  forall a b.
    (Fresh.Infinite a, Eq a,
      Eq b) => RenamingN.RenamingN a ->
                 [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
                   Term_Rewriting.Term b a ->
                     [(Term_Rewriting.Mctxt b a,
                        [((Term_Rewriting.Term b a, Term_Rewriting.Term b a),
                           Term_Rewriting.Term b a)])];
potential_overlaps ren r (Term_Rewriting.Var x) = [(Term_Rewriting.MVar x, [])];
potential_overlaps ren r (Term_Rewriting.Fun f ts) =
  let {
    lp = Term_Rewriting.Fun f ts;
    root_os = crit_rules ren r lp;
    merge = (\ oss -> (Term_Rewriting.MFun f (map fst oss), concatMap snd oss));
    rec_oss = Missing_List.concat_lists (map (potential_overlaps ren r) ts);
  } in map merge rec_oss ++
         map (\ lr -> (Term_Rewriting.MHole, [(lr, lp)])) root_os;

parallel_critical_peaks_of_rule_impl ::
  forall a b.
    (Fresh.Infinite a, Eq a,
      Eq b) => RenamingN.RenamingN a ->
                 [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
                   (Term_Rewriting.Term b a, Term_Rewriting.Term b a) ->
                     [(Term_Rewriting.Mctxt b a,
                        (Term_Rewriting.Term b a,
                          (Term_Rewriting.Term b a,
                            (Term_Rewriting.Term b a,
                              [(Term_Rewriting.Term b a,
                                 Term_Rewriting.Term b a)]))))];
parallel_critical_peaks_of_rule_impl ren r lr =
  (case lr of {
    (l, ra) ->
      let {
        a = filter (\ (_, rule_lp) -> not (null rule_lp))
              (potential_overlaps ren r l);
      } in concatMap
             (\ (c, rule_lp) ->
               (case Mgu_generic.mgu_vd_list ren
                       (map (\ (rl, aa) -> (fst rl, aa)) rule_lp)
                 of {
                 Nothing -> [];
                 Just (sigma, tau) ->
                   [(Term_Rewriting.subst_apply_mctxt c tau,
                      (Term_Rewriting.fill_holes
                         (Term_Rewriting.subst_apply_mctxt c tau)
                         (map (\ (aa, b) ->
                                (case aa of {
                                  (rl, _) ->
                                    Term_Rewriting.eval_term Term_Rewriting.Fun
                                      (snd rl);
                                })
                                  b)
                           (zip rule_lp sigma)),
                        (Term_Rewriting.eval_term Term_Rewriting.Fun l tau,
                          (Term_Rewriting.eval_term Term_Rewriting.Fun ra tau,
                            map fst rule_lp))))];
               }))
             a;
  });

check_PCPS_com ::
  forall a b.
    (Arith.Ccompare a, Compare.Compare a, Fresh.Infinite a, Eq a,
      Mapping.Mapping_impl a, Shows_Literal.Showl a, Compare.Compare b, Eq b,
      Shows_Literal.Showl b) => RenamingN.RenamingN a ->
                                  [(Term_Rewriting.Term b a,
                                     Term_Rewriting.Term b a)] ->
                                    [(Term_Rewriting.Term b a,
                                       Term_Rewriting.Term b a)] ->
                                      [(Term_Rewriting.Term b a,
 Term_Rewriting.Term b a)] ->
[(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
  [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
    Check_Joins.Cp_join_hints b a -> Sum_Type.Sum (String -> String) ();
check_PCPS_com ren p r s c d hints =
  Error_Monad.bind
    (Error_Monad.catch_error (Check_Joins.is_rsteps_conversiona d c hints)
      (\ x ->
        Sum_Type.Inl
          (Shows_Literal.showsl_lit
             "error in checking hints for proving that certains PCPS-elements are not in P\n" .
            x)))
    (\ checker ->
      Error_Monad.catch_error
        (Error_Monad.forallM
          (\ (t, (sa, u)) ->
            (if Term_Rewriting.equal_term t u ||
                  any (Term_Rewriting.instance_rule (sa, t)) p &&
                    any (Term_Rewriting.instance_rule (sa, u)) p
              then Sum_Type.Inr ()
              else Error_Monad.catch_error (checker t u)
                     (\ x ->
                       Sum_Type.Inl
                         (((((((Shows_Literal.showsl_lit
                                  "P does not contain PCPS for crit pair " .
                                 Term_Rewriting.showsl_terma t) .
                                Shows_Literal.showsl_lit " <-||- ") .
                               Term_Rewriting.showsl_terma sa) .
                              Shows_Literal.showsl_lit " -root-> ") .
                             Term_Rewriting.showsl_terma u) .
                            Shows_Literal.showsl_literal "\n") .
                           x))))
          (concatMap
            (\ lr ->
              map (\ (_, (t, (sa, (u, _)))) -> (t, (sa, u)))
                (parallel_critical_peaks_of_rule_impl ren r lr))
            s))
        (\ x -> Sum_Type.Inl (snd x)));

critical_parallel_rule_peaks_impl ::
  forall a b c.
    (Fresh.Infinite a, Eq a,
      Eq b) => RenamingN.RenamingN a ->
                 [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
                   [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
                     ((Term_Rewriting.Term b a, Term_Rewriting.Term b a) ->
                       Arith.Nat) ->
                       ((Term_Rewriting.Term b a, Term_Rewriting.Term b a) ->
                         c) ->
                         [(Term_Rewriting.Mctxt b a,
                            (Term_Rewriting.Term b a,
                              (Term_Rewriting.Term b a,
                                (Term_Rewriting.Term b a, (Arith.Nat, c)))))];
critical_parallel_rule_peaks_impl ren r s phi psi =
  concatMap
    (\ lr ->
      concatMap
        (\ (c, (t, (sa, (u, rls)))) ->
          (if not (Term_Rewriting.equal_term t u)
            then [(c, (t, (sa, (u, (Utility.max_list (map phi rls), psi lr)))))]
            else []))
        (parallel_critical_peaks_of_rule_impl ren r lr))
    s;

is_decreasing_steps ::
  forall a b c d.
    (Compare.Compare a, Eq a, Arith.Card_UNIV b, Arith.Cenum b, Arith.Ceq b,
      Arith.Cproper_interval b, Compare.Compare b, Eq b, Mapping.Mapping_impl b,
      Arith.Set_impl b, Compare.Compare c,
      Eq c) => Arith.Nat ->
                 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                   [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                     Term_Rewriting.Mctxt c b ->
                       Term_Rewriting.Term a b ->
                         d -> Term_Rewriting.Term a b ->
                                ((Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b) ->
                                  Arith.Nat) ->
                                  ((Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b) ->
                                    Arith.Nat) ->
                                    Arith.Nat -> Arith.Nat -> Bool;
is_decreasing_steps n r sa c s peak t phi psi k m =
  any (\ (n1, (n2, (n3, n4))) ->
        any (\ u1 ->
              any (\ u2 ->
                    any (\ u3 ->
                          any (\ u5 ->
                                any (\ u4 ->
                                      Arith.membera
(Term_Rewriting.reachable_terms
  (rS_conv_impl sa r psi phi (Quasi_Order.max k m)) u4 n4)
u3 &&
Rewrite_Relations_Impl.is_par_rstep_var_restr (r_le_impl r phi k)
  (Term_Rewriting.vars_mctxt c) u5 u4)
                                  (Rewrite_Relations_Impl.parallel_rewrite
                                    (r_le_impl r phi k) u5))
                            (Term_Rewriting.reachable_terms
                              (rS_conv_impl sa r psi phi m) t n3))
                      (Term_Rewriting.reachable_terms
                        (rS_conv_impl r sa phi psi (Quasi_Order.max k m)) u2
                        n2))
                (Rewrite_Relations_Impl.parallel_rewrite (r_le_impl sa psi m)
                  u1))
          (Term_Rewriting.reachable_terms (rS_conv_impl r sa phi psi k) s n1))
    (split_num n);

check_is_decreasing_auto ::
  forall a b.
    (Arith.Card_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Compare.Compare a, Fresh.Infinite a, Eq a, Mapping.Mapping_impl a,
      Arith.Set_impl a, Shows_Literal.Showl a, Compare.Compare b, Eq b,
      Shows_Literal.Showl b) => RenamingN.RenamingN a ->
                                  Arith.Nat ->
                                    [(Term_Rewriting.Term b a,
                                       Term_Rewriting.Term b a)] ->
                                      [(Term_Rewriting.Term b a,
 Term_Rewriting.Term b a)] ->
((Term_Rewriting.Term b a, Term_Rewriting.Term b a) -> Arith.Nat) ->
  ((Term_Rewriting.Term b a, Term_Rewriting.Term b a) -> Arith.Nat) ->
    Parallel_Critical_Pairs.Lab_filter -> Sum_Type.Sum (String -> String) ();
check_is_decreasing_auto ren n r s phi psi lf =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ (c, (sa, (peak, (t, (k, m))))) ->
        Check_Monad.check
          (if Parallel_Critical_Pairs.lab_filter lf k m
            then is_decreasing_steps n r s c sa peak t phi psi k m else True)
          ((((((Shows_Literal.showsl_lit "the parallel critical pair " .
                 Term_Rewriting.showsl_terma sa) .
                Shows_Literal.showsl_lit " R<-||- . ->S ") .
               Term_Rewriting.showsl_terma t) .
              Shows_Literal.showsl_lit
                " is not closed by the rule labeling criteria (auto mode) within the specified steps.") .
             Shows_Literal.showsl_nat n) .
            Shows_Literal.showsl_lit ""))
      (critical_parallel_rule_peaks_impl ren r s phi psi))
    (\ x -> Sum_Type.Inl (snd x));

get_renaming_substs ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Fresh.Infinite b, Eq b,
      Shows_Literal.Showl b) => [(Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b)] ->
                                  Sum_Type.Sum (String -> String)
                                    (b -> b, b -> b);
get_renaming_substs pairs =
  let {
    vfst = concatMap (Term_Rewriting.vars_term_list . fst) pairs;
    vsnd = concatMap (Term_Rewriting.vars_term_list . snd) pairs;
    xs = Arith.remdups (zip vfst vsnd);
  } in Error_Monad.bind
         (Check_Monad.check
           (Arith.distinct (map fst xs) && Arith.distinct (map snd xs))
           (Shows_Literal.showsl_lit
              "internal error in get_renamings (not distinct)\n" .
             Shows_Literal.showsl_lista pairs))
         (\ _ ->
           (case Finite_Renaming.extend_finite_map xs of {
             (sig, inv_sig) ->
               Error_Monad.bind
                 (Error_Monad.catch_error
                   (Error_Monad.forallM
                     (\ (l, r) ->
                       Check_Monad.check
                         (Term_Rewriting.equal_term
                           (Term_Rewriting.eval_term Term_Rewriting.Fun l
                             (Term_Rewriting.Var . sig))
                           r)
                         (Shows_Literal.showsl_lit
                            "internal error in get_renamings (wrong subst)\n" .
                           Shows_Literal.showsl_lista pairs))
                     pairs)
                   (\ x -> Sum_Type.Inl (snd x)))
                 (\ _ -> Sum_Type.Inr (sig, inv_sig));
           }));

check_decreasing ::
  forall a b.
    (Arith.Card_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Compare.Compare a, Fresh.Infinite a, Eq a, Mapping.Mapping_impl a,
      Arith.Set_impl a, Shows_Literal.Showl a, Compare.Compare b, Eq b,
      Shows_Literal.Showl b) => RenamingN.RenamingN a ->
                                  [(Term_Rewriting.Term b a,
                                     Term_Rewriting.Term b a)] ->
                                    [(Term_Rewriting.Term b a,
                                       Term_Rewriting.Term b a)] ->
                                      ((Term_Rewriting.Term b a,
 Term_Rewriting.Term b a) ->
Arith.Nat) ->
((Term_Rewriting.Term b a, Term_Rewriting.Term b a) -> Arith.Nat) ->
  Parallel_Critical_Pairs.Lab_filter ->
    Check_Joins.Cp_join_hints b a -> Sum_Type.Sum (String -> String) ();
check_decreasing ren r s phi psi lf (Check_Joins.CP_Auto n) =
  check_is_decreasing_auto ren n r s phi psi lf;
check_decreasing ren r s phi psi lf (Check_Joins.CP_Sequences cps) =
  let {
    rl = map (\ x -> (x, phi x)) r;
    sl = map (\ x -> (x, psi x)) s;
    sle = (\ k ->
            Arith.map_filter
              (\ x ->
                (if Arith.less_eq_nat (snd x) k then Just (fst x) else Nothing))
              sl);
    rle = (\ k ->
            Arith.map_filter
              (\ x ->
                (if Arith.less_eq_nat (snd x) k then Just (fst x) else Nothing))
              rl);
    rSconv =
      (\ k ->
        Arith.map_filter
          (\ x -> (if Arith.less_nat (snd x) k then Just (fst x) else Nothing))
          sl ++
          Arith.map_filter
            (\ x ->
              (if Arith.less_nat (snd x) k then Just ((Arith.swap . fst) x)
                else Nothing))
            rl);
  } in Error_Monad.bind
         (Error_Monad.catch_error
           (Error_Monad.forallM
             (\ cp ->
               Check_Monad.check (not (Arith.is_none (Check_Joins.cp_peak cp)))
                 (Shows_Literal.showsl_lit
                   "some peak has not been specified in PCP"))
             cps)
           (\ x -> Sum_Type.Inl (snd x)))
         (\ _ ->
           Error_Monad.catch_error
             (Error_Monad.forallM
               (\ (c, (sa, (t, (u, (k, m))))) ->
                 (if Parallel_Critical_Pairs.lab_filter lf k m
                   then (case Arith.find
                                (matching_peak (c, (sa, (t, (u, (k, m)))))) cps
                          of {
                          Nothing ->
                            Sum_Type.Inl
                              (((((((((Shows_Literal.showsl_lit
 "could not find the following critical peak in the certificate:\n" .
Term_Rewriting.showsl_terma sa) .
                                       Shows_Literal.showsl_lit "<-||-") .
                                      Term_Rewriting.showsl_terma t) .
                                     Shows_Literal.showsl_lit "->") .
                                    Term_Rewriting.showsl_terma u) .
                                   Shows_Literal.showsl_lit
                                     "\nwith labels (max-left,right) = ") .
                                  Shows_Literal.showsl_prod (k, m)) .
                                 Shows_Literal.showsl_lit
                                   "\n and with parallel positions\n") .
                                Shows_Literal.showsl_sep Position.showsl_pos
                                  (Shows_Literal.showsl_literal "; ")
                                  (Arith.sorted_list_of_set
                                    (Term_Rewriting.hole_poss c)));
                          Just cp ->
                            Error_Monad.bind
                              (get_renaming_substs
                                [(Check_Joins.cp_left cp, sa),
                                  (Check_Joins.cpPeak cp, t),
                                  (Check_Joins.cp_right cp, u)])
                              (\ (_, inv_sig) ->
                                let {
                                  rSk = rSconv k;
                                  sm = sle m;
                                  rSkm = rSconv (Quasi_Order.max k m);
                                  rk = rle k;
                                  rSm = rSconv m;
                                } in Check_Joins.check_rl_par_decreasing_sequence
                                       rSk sm rSkm rk rSm
                                       (Arith.image inv_sig
 (Term_Rewriting.vars_mctxt c))
                                       (Check_Joins.cp_left cp)
                                       (Check_Joins.cp_right cp)
                                       (Check_Joins.cp_join cp));
                        })
                   else Sum_Type.Inr ()))
               (critical_parallel_rule_peaks_impl ren r s phi psi))
             (\ x -> Sum_Type.Inl (snd x)));

check_pcp_rule_lab ::
  forall a b.
    (Arith.Card_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Compare.Compare a, Fresh.Infinite a, Eq a, Mapping.Mapping_impl a,
      Arith.Set_impl a, Shows_Literal.Showl a, Compare.Compare b, Eq b,
      Shows_Literal.Showl b) => RenamingN.RenamingN a ->
                                  [(Term_Rewriting.Term b a,
                                     Term_Rewriting.Term b a)] ->
                                    Pcp_rule_lab b a ->
                                      Sum_Type.Sum (String -> String) ();
check_pcp_rule_lab ren r (PCP_Sequences phi cps) =
  Error_Monad.bind (Term_Rewriting.check_left_linear_trs r)
    (\ _ ->
      check_decreasing ren r r phi phi Parallel_Critical_Pairs.No_Lab_Filter
        cps);

check_pcp_rule_lab_com ::
  forall a b.
    (Arith.Card_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Compare.Compare a, Fresh.Infinite a, Eq a, Mapping.Mapping_impl a,
      Arith.Set_impl a, Shows_Literal.Showl a, Compare.Compare b, Eq b,
      Shows_Literal.Showl b) => RenamingN.RenamingN a ->
                                  [(Term_Rewriting.Term b a,
                                     Term_Rewriting.Term b a)] ->
                                    [(Term_Rewriting.Term b a,
                                       Term_Rewriting.Term b a)] ->
                                      Pcp_rule_lab_com b a ->
Sum_Type.Sum (String -> String) ();
check_pcp_rule_lab_com ren r s (PCP_Sequences_Com phi psi cpsRS cpsSR) =
  let {
    chi = (case psi of {
            Nothing -> phi;
            Just chi -> chi;
          });
  } in Error_Monad.bind (Term_Rewriting.check_left_linear_trs r)
         (\ _ ->
           Error_Monad.bind (Term_Rewriting.check_left_linear_trs s)
             (\ _ ->
               Error_Monad.bind
                 (check_decreasing ren r s phi chi
                   Parallel_Critical_Pairs.No_Lab_Filter cpsRS)
                 (\ _ ->
                   check_decreasing ren s r chi phi
                     Parallel_Critical_Pairs.No_Lab_Filter cpsSR)));

parallel_critical_pairs_impl ::
  forall a b.
    (Fresh.Infinite a, Eq a,
      Eq b) => RenamingN.RenamingN a ->
                 [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
                   [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
                     [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)];
parallel_critical_pairs_impl ren r s =
  concatMap
    (\ lr ->
      concatMap
        (\ (_, (t, (_, (u, _)))) ->
          (if not (Term_Rewriting.equal_term t u) then [(t, u)] else []))
        (parallel_critical_peaks_of_rule_impl ren r lr))
    s;

check_compositional_pcps_joinable ::
  forall a b.
    (Arith.Ccompare a, Compare.Compare a, Fresh.Infinite a, Eq a,
      Mapping.Mapping_impl a, Shows_Literal.Showl a, Compare.Compare b, Eq b,
      Shows_Literal.Showl b) => RenamingN.RenamingN a ->
                                  [(Term_Rewriting.Term b a,
                                     Term_Rewriting.Term b a)] ->
                                    [(Term_Rewriting.Term b a,
                                       Term_Rewriting.Term b a)] ->
                                      Check_Joins.Cp_join_hints b a ->
Sum_Type.Sum (String -> String) ();
check_compositional_pcps_joinable ren r c hints =
  Error_Monad.bind (Check_Joins.is_rsteps_join_one c hints)
    (\ checker ->
      Error_Monad.catch_error
        (Error_Monad.forallM checker (parallel_critical_pairs_impl ren r r))
        (\ x -> Sum_Type.Inl (snd x)));

check_compositional_PCPS ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Compare.Compare a, Fresh.Infinite a, Eq a,
      Mapping.Mapping_impl a, Arith.Set_impl a, Shows_Literal.Showl a,
      Compare.Compare b, Eq b,
      Shows_Literal.Showl b) => RenamingN.RenamingN a ->
                                  [(Term_Rewriting.Term b a,
                                     Term_Rewriting.Term b a)] ->
                                    [(Term_Rewriting.Term b a,
                                       Term_Rewriting.Term b a)] ->
                                      [(Term_Rewriting.Term b a,
 Term_Rewriting.Term b a)] ->
Check_Joins.Cp_join_hints b a ->
  Check_Joins.Cp_join_hints b a -> Sum_Type.Sum (String -> String) ();
check_compositional_PCPS ren r c p hintsP hintsPCP =
  Error_Monad.catch_error
    (Error_Monad.bind (Term_Rewriting.check_left_linear_trs r)
      (\ _ ->
        Error_Monad.bind
          (Error_Monad.catch_error (Check_Monad.check_subseteq c r)
            (\ x ->
              Sum_Type.Inl
                ((Shows_Literal.showsl_lit "could not find rule " .
                   Term_Rewriting.showsl_rule x) .
                  Shows_Literal.showsl_lit " of C in R")))
          (\ _ ->
            Error_Monad.bind
              (check_compositional_pcps_joinable ren r r hintsPCP)
              (\ _ -> check_PCPS_com ren p r r c c hintsP))))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "problem in compositional parallel critical pair systems application\n" .
          x));

nontriv_ordinary_cps_impl ::
  forall a b.
    (Fresh.Infinite a, Eq a,
      Eq b) => RenamingN.RenamingN a ->
                 [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
                   [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
                     [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)];
nontriv_ordinary_cps_impl ren r s =
  filter (\ tu -> not (Term_Rewriting.equal_term (fst tu) (snd tu)))
    (map snd
      (Critical_Pairs_Impl.critical_pairs_impl
        (Parallel_Critical_Pairs.renaming2 ren) r s));

nonroot_parallel_peaks_impl ::
  forall a b.
    (Fresh.Infinite a, Eq a,
      Eq b) => RenamingN.RenamingN a ->
                 [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
                   [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
                     [(Term_Rewriting.Mctxt b a,
                        (Term_Rewriting.Term b a,
                          (Term_Rewriting.Term b a, Term_Rewriting.Term b a)))];
nonroot_parallel_peaks_impl ren r s =
  concatMap
    (\ lr ->
      concatMap
        (\ (c, (t, (sa, (u, _)))) ->
          (if not (Term_Rewriting.equal_mctxt c Term_Rewriting.MHole) &&
                not (Term_Rewriting.equal_term t u)
            then [(c, (t, (sa, u)))] else []))
        (parallel_critical_peaks_of_rule_impl ren r lr))
    s;

check_toyama_pcp_sequence_comm ::
  forall a b.
    (Arith.Card_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Compare.Compare a, Fresh.Infinite a, Eq a, Mapping.Mapping_impl a,
      Arith.Set_impl a, Shows_Literal.Showl a, Compare.Compare b, Eq b,
      Shows_Literal.Showl b) => RenamingN.RenamingN a ->
                                  [(Term_Rewriting.Term b a,
                                     Term_Rewriting.Term b a)] ->
                                    String ->
                                      [(Term_Rewriting.Term b a,
 Term_Rewriting.Term b a)] ->
String ->
  [Check_Joins.Crit_pair_info b a] -> Sum_Type.Sum (String -> String) ();
check_toyama_pcp_sequence_comm ren ra r sa s cps =
  Error_Monad.bind
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ cp ->
          Check_Monad.check (not (Arith.is_none (Check_Joins.cp_peak cp)))
            (Shows_Literal.showsl_lit
              "some peak has not been specified in PCP"))
        cps)
      (\ x -> Sum_Type.Inl (snd x)))
    (\ _ ->
      Error_Monad.catch_error
        (Error_Monad.forallM
          (\ (c, (sb, (t, u))) ->
            (case Arith.find (matching_cp (c, (sb, (t, u)))) cps of {
              Nothing ->
                Sum_Type.Inl
                  (((((((Shows_Literal.showsl_lit
                           "could not find the following critical peak in the certificate:\n" .
                          Term_Rewriting.showsl_terma sb) .
                         Shows_Literal.showsl_lit "<-||-") .
                        Term_Rewriting.showsl_terma t) .
                       Shows_Literal.showsl_lit "->") .
                      Term_Rewriting.showsl_terma u) .
                     Shows_Literal.showsl_lit "\nwith parallel positions\n") .
                    Shows_Literal.showsl_sep Position.showsl_pos
                      (Shows_Literal.showsl_literal "; ")
                      (Arith.sorted_list_of_set (Term_Rewriting.hole_poss c)));
              Just cp ->
                Error_Monad.bind
                  (get_renaming_substs
                    [(Check_Joins.cp_left cp, sb), (Check_Joins.cpPeak cp, t),
                      (Check_Joins.cp_right cp, u)])
                  (\ (_, inv_sig) ->
                    Check_Joins.check_toyama_pcp_join_sequence ra r sa s
                      (Arith.image inv_sig (Term_Rewriting.vars_mctxt c))
                      (Check_Joins.cp_left cp) (Check_Joins.cp_right cp)
                      (Check_Joins.cp_join cp));
            }))
          (nonroot_parallel_peaks_impl ren ra sa))
        (\ x -> Sum_Type.Inl (snd x)));

check_toyama_pcp_condition ::
  forall a b.
    (Arith.Card_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Compare.Compare a, Fresh.Infinite a, Eq a, Mapping.Mapping_impl a,
      Arith.Set_impl a, Shows_Literal.Showl a, Compare.Compare b, Eq b,
      Shows_Literal.Showl b) => RenamingN.RenamingN a ->
                                  [(Term_Rewriting.Term b a,
                                     Term_Rewriting.Term b a)] ->
                                    String ->
                                      [(Term_Rewriting.Term b a,
 Term_Rewriting.Term b a)] ->
String -> Check_Joins.Cp_join_hints b a -> Sum_Type.Sum (String -> String) ();
check_toyama_pcp_condition ren ra r sa s (Check_Joins.CP_Auto n) =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ (c, (sb, (peak, t))) ->
        Check_Monad.check
          (Check_Joins.is_toyama_par_rstep_join n ra sa c sb peak t)
          ((((((Shows_Literal.showsl_lit "the parallel critical pair " .
                 Term_Rewriting.showsl_terma sb) .
                Shows_Literal.showsl_lit
                  ((((" <-||," ++ r) ++ "- . -") ++ s) ++ "-> ")) .
               Term_Rewriting.showsl_terma t) .
              Shows_Literal.showsl_lit
                " is not closed by the  Toyama\'s pcp condition within") .
             Shows_Literal.showsl_nat n) .
            Shows_Literal.showsl_lit " steps."))
      (nonroot_parallel_peaks_impl ren ra sa))
    (\ x -> Sum_Type.Inl (snd x));
check_toyama_pcp_condition ren ra r sa s (Check_Joins.CP_Sequences seqs) =
  check_toyama_pcp_sequence_comm ren ra r sa s seqs;

check_compositional_pcps_joinable_generic ::
  forall a b.
    (Arith.Ccompare a, Compare.Compare a, Fresh.Infinite a, Eq a,
      Mapping.Mapping_impl a, Shows_Literal.Showl a, Compare.Compare b, Eq b,
      Shows_Literal.Showl b) => RenamingN.RenamingN a ->
                                  [(Term_Rewriting.Term b a,
                                     Term_Rewriting.Term b a)] ->
                                    [(Term_Rewriting.Term b a,
                                       Term_Rewriting.Term b a)] ->
                                      [(Term_Rewriting.Term b a,
 Term_Rewriting.Term b a)] ->
[(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
  Check_Joins.Cp_join_hints b a -> Sum_Type.Sum (String -> String) ();
check_compositional_pcps_joinable_generic ren r s c d hints =
  Error_Monad.bind (Check_Joins.is_rsteps_join_two c d hints)
    (\ checker ->
      Error_Monad.catch_error
        (Error_Monad.forallM checker (parallel_critical_pairs_impl ren r s))
        (\ x -> Sum_Type.Inl (snd x)));

check_compositional_PCPS_com ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Compare.Compare a, Fresh.Infinite a, Eq a,
      Mapping.Mapping_impl a, Arith.Set_impl a, Shows_Literal.Showl a,
      Compare.Compare b, Eq b,
      Shows_Literal.Showl b) => RenamingN.RenamingN a ->
                                  [(Term_Rewriting.Term b a,
                                     Term_Rewriting.Term b a)] ->
                                    [(Term_Rewriting.Term b a,
                                       Term_Rewriting.Term b a)] ->
                                      [(Term_Rewriting.Term b a,
 Term_Rewriting.Term b a)] ->
[(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
  [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
    Check_Joins.Cp_join_hints b a ->
      Check_Joins.Cp_join_hints b a ->
        Check_Joins.Cp_join_hints b a ->
          Check_Joins.Cp_join_hints b a -> Sum_Type.Sum (String -> String) ();
check_compositional_PCPS_com ren r s c d p hintsP_RS hintsP_SR hintsRS hintsSR =
  Error_Monad.catch_error
    (Error_Monad.bind (Term_Rewriting.check_left_linear_trs r)
      (\ _ ->
        Error_Monad.bind (Term_Rewriting.check_left_linear_trs s)
          (\ _ ->
            Error_Monad.bind
              (Error_Monad.catch_error (Check_Monad.check_subseteq c r)
                (\ x ->
                  Sum_Type.Inl
                    ((Shows_Literal.showsl_lit "could not find rule " .
                       Term_Rewriting.showsl_rule x) .
                      Shows_Literal.showsl_lit " of C in R")))
              (\ _ ->
                Error_Monad.bind
                  (Error_Monad.catch_error (Check_Monad.check_subseteq d s)
                    (\ x ->
                      Sum_Type.Inl
                        ((Shows_Literal.showsl_lit "could not find rule " .
                           Term_Rewriting.showsl_rule x) .
                          Shows_Literal.showsl_lit " of D in S")))
                  (\ _ ->
                    Error_Monad.bind
                      (check_compositional_pcps_joinable_generic ren r s s r
                        hintsRS)
                      (\ _ ->
                        Error_Monad.bind
                          (check_compositional_pcps_joinable_generic ren s r r s
                            hintsSR)
                          (\ _ ->
                            Error_Monad.bind
                              (check_PCPS_com ren p r s c d hintsP_RS)
                              (\ _ ->
                                check_PCPS_com ren p s r d c hintsP_SR))))))))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "problem in compositional parallel critical pair systems application\n" .
          x));

check_cp_parstep_steps_sequence_comm ::
  forall a b.
    (Arith.Ccompare a, Compare.Compare a, Fresh.Infinite a, Eq a,
      Mapping.Mapping_impl a, Shows_Literal.Showl a, Compare.Compare b, Eq b,
      Shows_Literal.Showl b) => RenamingN.RenamingN a ->
                                  [(Term_Rewriting.Term b a,
                                     Term_Rewriting.Term b a)] ->
                                    String ->
                                      [(Term_Rewriting.Term b a,
 Term_Rewriting.Term b a)] ->
String ->
  [Check_Joins.Crit_pair_info b a] -> Sum_Type.Sum (String -> String) ();
check_cp_parstep_steps_sequence_comm ren ra r sa s cps =
  Error_Monad.bind
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ cp ->
          Check_Joins.check_par_rsteps_join_sequence ra r sa s
            (Check_Joins.cp_left cp) (Check_Joins.cp_right cp)
            (Check_Joins.cp_join cp))
        cps)
      (\ x -> Sum_Type.Inl (snd x)))
    (\ _ ->
      Error_Monad.catch_error
        (Error_Monad.forallM
          (\ cp ->
            Check_Monad.check
              (any (\ cpa ->
                     Term_Rewriting.instance_rule cp
                       (Check_Joins.cp_left cpa, Check_Joins.cp_right cpa))
                cps)
              (Shows_Literal.showsl_lit "could not find critical pair " .
                Shows_Literal.showsl_prod cp))
          (nontriv_ordinary_cps_impl ren ra sa))
        (\ x -> Sum_Type.Inl (snd x)));

check_cp_parstep_steps_joinable ::
  forall a b.
    (Arith.Ccompare a, Compare.Compare a, Fresh.Infinite a, Eq a,
      Mapping.Mapping_impl a, Shows_Literal.Showl a, Compare.Compare b, Eq b,
      Shows_Literal.Showl b) => RenamingN.RenamingN a ->
                                  [(Term_Rewriting.Term b a,
                                     Term_Rewriting.Term b a)] ->
                                    String ->
                                      [(Term_Rewriting.Term b a,
 Term_Rewriting.Term b a)] ->
String -> Check_Joins.Cp_join_hints b a -> Sum_Type.Sum (String -> String) ();
check_cp_parstep_steps_joinable ren ra r sa s (Check_Joins.CP_Auto n) =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ (sb, t) ->
        Check_Monad.check (Check_Joins.is_par_rsteps_join ra sa (Just n) sb t)
          ((((((Shows_Literal.showsl_lit "the ordinary critical pair " .
                 Term_Rewriting.showsl_terma sb) .
                Shows_Literal.showsl_lit
                  ((((" <-" ++ s) ++ "- . -") ++ r) ++ "-> ")) .
               Term_Rewriting.showsl_terma t) .
              Shows_Literal.showsl_lit
                " is not closed by the Gramlich\'s cp condition within ") .
             Shows_Literal.showsl_nat n) .
            Shows_Literal.showsl_lit " steps."))
      (nontriv_ordinary_cps_impl ren ra sa))
    (\ x -> Sum_Type.Inl (snd x));
check_cp_parstep_steps_joinable ren ra r sa s (Check_Joins.CP_Sequences seqs) =
  check_cp_parstep_steps_sequence_comm ren ra r sa s seqs;

check_compositional_pcp_rule_lab ::
  forall a b.
    (Arith.Card_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Compare.Compare a, Fresh.Infinite a, Eq a, Mapping.Mapping_impl a,
      Arith.Set_impl a, Shows_Literal.Showl a, Compare.Compare b, Eq b,
      Shows_Literal.Showl b) => RenamingN.RenamingN a ->
                                  [(Term_Rewriting.Term b a,
                                     Term_Rewriting.Term b a)] ->
                                    [(Term_Rewriting.Term b a,
                                       Term_Rewriting.Term b a)] ->
                                      Pcp_rule_lab_com b a ->
Sum_Type.Sum (String -> String) ();
check_compositional_pcp_rule_lab ren r c
  (PCP_Sequences_Com phi psi cpsPhiPsi cpsPsiPhi) =
  let {
    chi = (case psi of {
            Nothing -> phi;
            Just chi -> chi;
          });
    r_0 = r_le_impl r phi Arith.zero_nat;
    r_0a = r_le_impl r chi Arith.zero_nat;
  } in Error_Monad.bind (Term_Rewriting.check_left_linear_trs r)
         (\ _ ->
           Error_Monad.bind
             (Error_Monad.catch_error (Check_Monad.check_same_set r_0 c)
               (\ x ->
                 Sum_Type.Inl
                   (Shows_Literal.showsl_lit
                      "0-labelled TRSs is not identical to C because of rule " .
                     Term_Rewriting.showsl_rule x)))
             (\ _ ->
               Error_Monad.bind
                 (Error_Monad.catch_error (Check_Monad.check_same_set r_0a c)
                   (\ x ->
                     Sum_Type.Inl
                       (Shows_Literal.showsl_lit
                          "0-labelled TRSs is not identical to C because of rule " .
                         Term_Rewriting.showsl_rule x)))
                 (\ _ ->
                   Error_Monad.bind
                     (check_decreasing ren r r phi chi
                       Parallel_Critical_Pairs.Zero_Zero_Filter cpsPhiPsi)
                     (\ _ ->
                       (case psi of {
                         Nothing -> Sum_Type.Inr ();
                         Just _ ->
                           check_decreasing ren r r chi phi
                             Parallel_Critical_Pairs.Zero_Zero_Filter cpsPsiPhi;
                       })))));

check_compositional_pcps_convertable ::
  forall a b.
    (Arith.Ccompare a, Compare.Compare a, Fresh.Infinite a, Eq a,
      Mapping.Mapping_impl a, Shows_Literal.Showl a, Compare.Compare b, Eq b,
      Shows_Literal.Showl b) => RenamingN.RenamingN a ->
                                  [(Term_Rewriting.Term b a,
                                     Term_Rewriting.Term b a)] ->
                                    [(Term_Rewriting.Term b a,
                                       Term_Rewriting.Term b a)] ->
                                      Check_Joins.Cp_join_hints b a ->
Sum_Type.Sum (String -> String) ();
check_compositional_pcps_convertable ren r c (Check_Joins.CP_Auto n) =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ (t, u) ->
        Check_Monad.check (Check_Joins.is_rsteps_conversion c c n t u)
          (((Shows_Literal.showsl_lit
               "\ncould not find conversion of parallel critical pair " .
              Term_Rewriting.showsl_terma t) .
             Shows_Literal.showsl_lit "<-||- . -root->") .
            Term_Rewriting.showsl_terma u))
      (parallel_critical_pairs_impl ren r r))
    (\ x -> Sum_Type.Inl (snd x));
check_compositional_pcps_convertable ren r c (Check_Joins.CP_Sequences cps) =
  Error_Monad.bind
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ cp ->
          Check_Joins.check_conversion_sequence c (Check_Joins.cp_left cp)
            (Check_Joins.cp_right cp) (Check_Joins.cp_join cp))
        cps)
      (\ x -> Sum_Type.Inl (snd x)))
    (\ _ ->
      Error_Monad.catch_error
        (Error_Monad.forallM
          (\ cp ->
            Check_Monad.check
              (any (\ cpa ->
                     Term_Rewriting.instance_rule cp
                       (Check_Joins.cp_left cpa, Check_Joins.cp_right cpa) ||
                       Term_Rewriting.instance_rule cp
                         (Check_Joins.cp_right cpa, Check_Joins.cp_left cpa))
                cps)
              (Shows_Literal.showsl_lit
                 "could not find parallel critical pair " .
                Shows_Literal.showsl_prod cp))
          (parallel_critical_pairs_impl ren r r))
        (\ x -> Sum_Type.Inl (snd x)));

check_compositional_parallel_pairs ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Compare.Compare a, Fresh.Infinite a, Eq a,
      Mapping.Mapping_impl a, Arith.Set_impl a, Shows_Literal.Showl a,
      Compare.Compare b, Eq b,
      Shows_Literal.Showl b) => RenamingN.RenamingN a ->
                                  [(Term_Rewriting.Term b a,
                                     Term_Rewriting.Term b a)] ->
                                    [(Term_Rewriting.Term b a,
                                       Term_Rewriting.Term b a)] ->
                                      Check_Joins.Cp_join_hints b a ->
Sum_Type.Sum (String -> String) ();
check_compositional_parallel_pairs ren r c hints =
  Error_Monad.catch_error
    (Error_Monad.bind (Term_Rewriting.check_left_linear_trs r)
      (\ _ ->
        Error_Monad.bind
          (Error_Monad.catch_error (Check_Monad.check_subseteq c r)
            (\ x ->
              Sum_Type.Inl
                ((Shows_Literal.showsl_lit "could not find rule " .
                   Term_Rewriting.showsl_rule x) .
                  Shows_Literal.showsl_lit " of C in R")))
          (\ _ -> check_compositional_pcps_convertable ren r c hints)))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "problem in compositional parallel critical pair application\n" .
          x));

check_compositional_pcp_rule_lab_comm ::
  forall a b.
    (Arith.Card_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Compare.Compare a, Fresh.Infinite a, Eq a, Mapping.Mapping_impl a,
      Arith.Set_impl a, Shows_Literal.Showl a, Compare.Compare b, Eq b,
      Shows_Literal.Showl b) => RenamingN.RenamingN a ->
                                  [(Term_Rewriting.Term b a,
                                     Term_Rewriting.Term b a)] ->
                                    [(Term_Rewriting.Term b a,
                                       Term_Rewriting.Term b a)] ->
                                      [(Term_Rewriting.Term b a,
 Term_Rewriting.Term b a)] ->
[(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
  Pcp_rule_lab_com b a -> Sum_Type.Sum (String -> String) ();
check_compositional_pcp_rule_lab_comm ren r s c d
  (PCP_Sequences_Com phi psi cpsPhiPsi cpsPsiPhi) =
  let {
    chi = (case psi of {
            Nothing -> phi;
            Just chi -> chi;
          });
    r_0 = r_le_impl r phi Arith.zero_nat;
    s_0 = r_le_impl s chi Arith.zero_nat;
  } in Error_Monad.bind (Term_Rewriting.check_left_linear_trs r)
         (\ _ ->
           Error_Monad.bind (Term_Rewriting.check_left_linear_trs s)
             (\ _ ->
               Error_Monad.bind
                 (Error_Monad.catch_error (Check_Monad.check_same_set r_0 c)
                   (\ x ->
                     Sum_Type.Inl
                       (Shows_Literal.showsl_lit
                          "0-labelled TRSs R is not identical to C because of rule " .
                         Term_Rewriting.showsl_rule x)))
                 (\ _ ->
                   Error_Monad.bind
                     (Error_Monad.catch_error (Check_Monad.check_same_set s_0 d)
                       (\ x ->
                         Sum_Type.Inl
                           (Shows_Literal.showsl_lit
                              "0-labelled TRSs S is not identical to D because of rule " .
                             Term_Rewriting.showsl_rule x)))
                     (\ _ ->
                       Error_Monad.bind
                         (check_decreasing ren r s phi chi
                           Parallel_Critical_Pairs.Zero_Zero_Filter cpsPhiPsi)
                         (\ _ ->
                           check_decreasing ren s r chi phi
                             Parallel_Critical_Pairs.Zero_Zero_Filter
                             cpsPsiPhi)))));

check_parallel_critical_pairs_closed_CR ::
  forall a b.
    (Arith.Card_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Compare.Compare a, Fresh.Infinite a, Eq a, Mapping.Mapping_impl a,
      Arith.Set_impl a, Shows_Literal.Showl a, Compare.Compare b, Eq b,
      Shows_Literal.Showl b) => RenamingN.RenamingN a ->
                                  [(Term_Rewriting.Term b a,
                                     Term_Rewriting.Term b a)] ->
                                    Check_Joins.Cp_join_hints b a ->
                                      Check_Joins.Cp_join_hints b a ->
Sum_Type.Sum (String -> String) ();
check_parallel_critical_pairs_closed_CR ren r hints_cp hints_pcp =
  Error_Monad.catch_error
    (Error_Monad.bind (Term_Rewriting.check_left_linear_trs r)
      (\ _ ->
        Error_Monad.bind
          (check_cp_parstep_steps_joinable ren r "R" r "R" hints_cp)
          (\ _ -> check_toyama_pcp_condition ren r "R" r "R" hints_pcp)))
    (\ x ->
      Sum_Type.Inl
        (((Shows_Literal.showsl_lit
             "failed to apply PCP-closed criterion for proving CR of R\n\n" .
            x) .
           Shows_Literal.showsl_lit "\n\nR: ") .
          Term_Rewriting.showsl_trs r));

check_parallel_critical_pairs_closed_comm ::
  forall a b.
    (Arith.Card_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Compare.Compare a, Fresh.Infinite a, Eq a, Mapping.Mapping_impl a,
      Arith.Set_impl a, Shows_Literal.Showl a, Compare.Compare b, Eq b,
      Shows_Literal.Showl b) => RenamingN.RenamingN a ->
                                  [(Term_Rewriting.Term b a,
                                     Term_Rewriting.Term b a)] ->
                                    [(Term_Rewriting.Term b a,
                                       Term_Rewriting.Term b a)] ->
                                      Check_Joins.Cp_join_hints b a ->
Check_Joins.Cp_join_hints b a -> Sum_Type.Sum (String -> String) ();
check_parallel_critical_pairs_closed_comm ren r s hints_cp hints_pcp =
  Error_Monad.catch_error
    (Error_Monad.bind (Term_Rewriting.check_left_linear_trs r)
      (\ _ ->
        Error_Monad.bind (Term_Rewriting.check_left_linear_trs s)
          (\ _ ->
            Error_Monad.bind
              (check_cp_parstep_steps_joinable ren r "R" s "S" hints_cp)
              (\ _ -> check_toyama_pcp_condition ren r "R" s "S" hints_pcp))))
    (\ x ->
      Sum_Type.Inl
        (((((Shows_Literal.showsl_lit
               "failed to apply PCP-closed criterion for commutation of R and S\n\n" .
              x) .
             Shows_Literal.showsl_lit "\n\nR: ") .
            Term_Rewriting.showsl_trs r) .
           Shows_Literal.showsl_lit "\n\nS: ") .
          Term_Rewriting.showsl_trs s));

}
