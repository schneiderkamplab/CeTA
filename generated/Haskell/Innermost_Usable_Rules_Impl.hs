{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Innermost_Usable_Rules_Impl(rule_match_impl, is_ur_closed_impl_dpp_mv,
                               usable_rules_proc, inn_usable_rules_pair,
                               inn_usable_rules_wf_tp, inn_usable_rules_wf_dpp,
                               is_ur_closed_term_af_impl,
                               is_ur_closed_af_impl_tp_mv,
                               is_ur_closed_af_impl_dpp_mv,
                               mono_inn_usable_rules_ce_proc)
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
import qualified Inductive_Set_Impl;
import qualified Map_Choice;
import qualified Term_Order;
import qualified Compare_Order_Instances;
import qualified Termination_Problem_Spec;
import qualified Icap_Impl;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Dependency_Pair_Problem_Spec;
import qualified Compare;
import qualified Icap;
import qualified HOL;
import qualified Sum_Type;
import qualified Term_Rewriting;
import qualified Arith;

rule_match_impl ::
  forall a b.
    (Eq a) => (Term_Rewriting.Term a [Arith.Char] -> Bool) ->
                (b -> Term_Rewriting.Term a (Sum_Type.Sum () [Arith.Char])) ->
                  [Term_Rewriting.Term a [Arith.Char]] ->
                    a -> [b] -> Term_Rewriting.Term a [Arith.Char] -> Bool;
rule_match_impl nfq e_cap s f ts l =
  (case Icap.mgu_class (Term_Rewriting.Fun f (map e_cap ts)) l of {
    Nothing -> False;
    Just mu ->
      all (\ u ->
            nfq (Term_Rewriting.eval_term Term_Rewriting.Fun
                  (Term_Rewriting.map_term (\ x -> x)
                    (\ a -> Arith.char_0x79 : a) u)
                  mu))
        (Term_Rewriting.args l) &&
        all (\ u -> nfq (Term_Rewriting.eval_term Term_Rewriting.Fun u mu)) s;
  });

ur_term_impl ::
  forall a b c.
    (Eq a,
      Eq c) => (Term_Rewriting.Term a [Arith.Char] -> Bool) ->
                 (Term_Rewriting.Term a b ->
                   Term_Rewriting.Term a (Sum_Type.Sum () [Arith.Char])) ->
                   [(Term_Rewriting.Term a [Arith.Char], c)] ->
                     ((a, Arith.Nat) -> Arith.Set Arith.Nat) ->
                       [Term_Rewriting.Term a [Arith.Char]] ->
                         Term_Rewriting.Term a b ->
                           [(Term_Rewriting.Term a [Arith.Char], c)];
ur_term_impl nfq e_cap r pi s (Term_Rewriting.Var x) = [];
ur_term_impl nfq e_cap r pi s (Term_Rewriting.Fun f ts) =
  let {
    n = Arith.size_list ts;
    rec = map (ur_term_impl nfq e_cap r pi s) ts;
  } in Arith.remdups
         (concatMap
            (\ (i, urs) -> (if Arith.member i (pi (f, n)) then urs else []))
            (zip (Arith.upt Arith.zero_nat n) rec) ++
           filter (\ (l, _) -> rule_match_impl nfq e_cap s f ts l) r);

usable_rules_calc_impl ::
  forall a.
    (Compare.Compare_order a,
      Eq a) => (Term_Rewriting.Term a [Arith.Char] -> Bool) ->
                 ([Term_Rewriting.Term a [Arith.Char]] ->
                   Term_Rewriting.Term a [Arith.Char] ->
                     Term_Rewriting.Term a (Sum_Type.Sum () [Arith.Char])) ->
                   [(Term_Rewriting.Term a [Arith.Char],
                      Term_Rewriting.Term a [Arith.Char])] ->
                     [([Term_Rewriting.Term a [Arith.Char]],
                        Term_Rewriting.Term a [Arith.Char])] ->
                       [(Term_Rewriting.Term a [Arith.Char],
                          Term_Rewriting.Term a [Arith.Char])];
usable_rules_calc_impl nfq e_cap r =
  let {
    urt = (\ (s, t) ->
            let {
              sa = map (Term_Rewriting.map_term (\ x -> x)
                         (\ a -> Arith.char_0x78 : a))
                     s;
            } in ur_term_impl nfq (e_cap sa) r Term_Order.full_af sa
                   (Term_Rewriting.map_term (\ x -> x)
                     (\ a -> Arith.char_0x78 : a) t));
    urules = map (\ (l, a) -> (Term_Rewriting.args l, a)) r;
    ufun = Map_Choice.precompute_fun urt urules;
  } in Inductive_Set_Impl.inductive_set_impl_lazy ufun
         (\ (l, ra) -> [(Term_Rewriting.args l, ra)]);

ur_calc_singleton ::
  forall a.
    (Compare.Compare_order a,
      Eq a) => (Term_Rewriting.Term a [Arith.Char] -> Bool) ->
                 ([Term_Rewriting.Term a [Arith.Char]] ->
                   Term_Rewriting.Term a [Arith.Char] ->
                     Term_Rewriting.Term a (Sum_Type.Sum () [Arith.Char])) ->
                   [(Term_Rewriting.Term a [Arith.Char],
                      Term_Rewriting.Term a [Arith.Char])] ->
                     ([Term_Rewriting.Term a [Arith.Char]],
                       Term_Rewriting.Term a [Arith.Char]) ->
                       [(Term_Rewriting.Term a [Arith.Char],
                          Term_Rewriting.Term a [Arith.Char])];
ur_calc_singleton nfq e_cap r st = usable_rules_calc_impl nfq e_cap r [st];

rule_match_impl_aux ::
  forall a.
    (Eq a) => (Term_Rewriting.Term a [Arith.Char] -> Bool) ->
                [Term_Rewriting.Term a [Arith.Char]] ->
                  Term_Rewriting.Term a [Arith.Char] ->
                    Term_Rewriting.Term a [Arith.Char] -> Bool;
rule_match_impl_aux nfq s fts l =
  (case Term_Rewriting.mgu fts
          (Term_Rewriting.map_term (\ x -> x) (\ a -> Arith.char_0x79 : a) l)
    of {
    Nothing -> False;
    Just mu ->
      all (\ u ->
            nfq (Term_Rewriting.eval_term Term_Rewriting.Fun
                  (Term_Rewriting.map_term (\ x -> x)
                    (\ a -> Arith.char_0x79 : a) u)
                  mu))
        (Term_Rewriting.args l) &&
        all (\ u -> nfq (Term_Rewriting.eval_term Term_Rewriting.Fun u mu)) s;
  });

is_ur_closed_term_impl ::
  forall a b c.
    (Compare.Compare a, Eq a, Arith.Ceq c,
      Arith.Ccompare c) => (Term_Rewriting.Term a [Arith.Char] -> Bool) ->
                             (Term_Rewriting.Term a b ->
                               Term_Rewriting.Term a
                                 (Sum_Type.Sum () [Arith.Char])) ->
                               [(Term_Rewriting.Term a [Arith.Char], c)] ->
                                 Arith.Set
                                   (Term_Rewriting.Term a [Arith.Char], c) ->
                                   [Term_Rewriting.Term a [Arith.Char]] ->
                                     Term_Rewriting.Term a b -> Bool;
is_ur_closed_term_impl nfq e_cap r u s (Term_Rewriting.Var x) = True;
is_ur_closed_term_impl nfq e_cap r u s (Term_Rewriting.Fun f ts) =
  all (is_ur_closed_term_impl nfq e_cap r u s) ts &&
    let {
      fts = Icap.class_to_term Arith.char_0x7A
              (Term_Rewriting.Fun f (map e_cap ts));
    } in all (\ (l, ra) ->
               Arith.member (l, ra) u || not (rule_match_impl_aux nfq s fts l))
           r;

is_ur_closed_impl_dpp_mv ::
  forall a b.
    (Compare.Compare_order b, Eq b,
      Term_Rewriting.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b
                                   [Arith.Char] () ->
                                   a -> [(Term_Rewriting.Term b [Arith.Char],
   Term_Rewriting.Term b [Arith.Char])] ->
  [Term_Rewriting.Term b [Arith.Char]] ->
    Term_Rewriting.Term b [Arith.Char] -> Bool;
is_ur_closed_impl_dpp_mv i d u =
  let {
    ic = Icap_Impl.icap_impl_dpp i d;
    qnf = Dependency_Pair_Problem_Spec.is_QNF i d;
    r = Dependency_Pair_Problem_Spec.rules i d;
    urc = (\ s -> is_ur_closed_term_impl qnf (ic s) r (Arith.set u));
  } in (\ s ->
         let {
           sa = map (Term_Rewriting.map_term (\ x -> x)
                      (\ a -> Arith.char_0x78 : a))
                  s;
         } in (\ t ->
                urc sa sa
                  (Term_Rewriting.map_term (\ x -> x)
                    (\ a -> Arith.char_0x78 : a) t)));

usable_rules_proc ::
  forall a b.
    (Compare.Compare_order b, Eq b,
      Term_Rewriting.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b
                                   [Arith.Char] () ->
                                   [(Term_Rewriting.Term b [Arith.Char],
                                      Term_Rewriting.Term b [Arith.Char])] ->
                                     a -> Sum_Type.Sum (String -> String) a;
usable_rules_proc i u dpp =
  (case Error_Monad.bind
          (Check_Monad.check
            (Dependency_Pair_Problem_Spec.nFQ_subset_NF_rules i dpp)
            (Term_Rewriting.showsl_lit "innermost rewriting required"))
          (\ _ ->
            Error_Monad.bind
              (Check_Monad.check
                (Dependency_Pair_Problem_Spec.nfs i dpp ||
                  (Dependency_Pair_Problem_Spec.minimal i dpp ||
                    Dependency_Pair_Problem_Spec.wwf_rules i dpp))
                (Term_Rewriting.showsl_lit
                  "normal form subst, minimality or well-formedness required"))
              (\ _ ->
                let {
                  p = Dependency_Pair_Problem_Spec.pairs i dpp;
                  urc = is_ur_closed_impl_dpp_mv i dpp u;
                  check_urc =
                    (\ s t ->
                      Check_Monad.check (urc s t)
                        ((Term_Rewriting.showsl_lit "term " .
                           Term_Rewriting.showsl_terma t) .
                          Term_Rewriting.showsl_lit
                            " is not closed under usable rules"));
                  nfs = Dependency_Pair_Problem_Spec.nfs i dpp;
                } in Error_Monad.bind
                       (Error_Monad.catch_error
                         (Error_Monad.forallM
                           (\ (l, r) ->
                             Error_Monad.bind
                               (if nfs then Sum_Type.Inr ()
                                 else Error_Monad.catch_error
(Check_Monad.check_subseteq (Term_Rewriting.vars_term_list r)
  (Term_Rewriting.vars_term_list l))
(\ _ ->
  Sum_Type.Inl (Term_Rewriting.showsl_lit "variable condition in P violated")))
                               (\ _ -> check_urc [l] r))
                           p)
                         (\ x -> Sum_Type.Inl (snd x)))
                       (\ _ ->
                         Error_Monad.catch_error
                           (Error_Monad.forallM
                             (\ (l, a) -> check_urc (Term_Rewriting.args l) a)
                             u)
                           (\ x -> Sum_Type.Inl (snd x)))))
    of {
    Sum_Type.Inl a -> Sum_Type.Inl a;
    Sum_Type.Inr _ ->
      Sum_Type.Inr (Dependency_Pair_Problem_Spec.intersect_rules i dpp u);
  });

inn_usable_rules_wf ::
  forall a.
    (Compare.Compare_order a,
      Eq a) => (Term_Rewriting.Term a [Arith.Char] -> Bool) ->
                 ([Term_Rewriting.Term a [Arith.Char]] ->
                   Term_Rewriting.Term a [Arith.Char] ->
                     Term_Rewriting.Term a (Sum_Type.Sum () [Arith.Char])) ->
                   [(Term_Rewriting.Term a [Arith.Char],
                      Term_Rewriting.Term a [Arith.Char])] ->
                     Bool ->
                       ([Term_Rewriting.Term a [Arith.Char]],
                         Term_Rewriting.Term a [Arith.Char]) ->
                         [(Term_Rewriting.Term a [Arith.Char],
                            Term_Rewriting.Term a [Arith.Char])];
inn_usable_rules_wf nfq e_cap r nfs =
  (\ (ss, t) ->
    (if nfs ||
          all (\ x -> any (Term_Rewriting.contains_var_term x) ss)
            (Arith.remdups (Term_Rewriting.vars_term_list t))
      then ur_calc_singleton nfq e_cap r (ss, t) else r));

inn_usable_rules_pair ::
  forall a b.
    (Compare.Compare_order b,
      Eq b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b [Arith.Char] () ->
                 a -> (Term_Rewriting.Term b [Arith.Char],
                        Term_Rewriting.Term b [Arith.Char]) ->
                        [(Term_Rewriting.Term b [Arith.Char],
                           Term_Rewriting.Term b [Arith.Char])];
inn_usable_rules_pair i d =
  let {
    inn = Dependency_Pair_Problem_Spec.nFQ_subset_NF_rules i d;
    r = Dependency_Pair_Problem_Spec.rules i d;
    qnf = Dependency_Pair_Problem_Spec.is_QNF i d;
    ic = Icap_Impl.icap_impl_dpp i d;
    calc = ur_calc_singleton qnf ic r;
    nfs = Dependency_Pair_Problem_Spec.nfs i d;
    wwf = Dependency_Pair_Problem_Spec.wwf_rules i d;
    m = Dependency_Pair_Problem_Spec.minimal i d;
  } in (\ (s, t) ->
         (if inn &&
               (nfs ||
                 Arith.less_eq_set (Term_Rewriting.vars_term t)
                   (Term_Rewriting.vars_term s)) &&
                 (nfs || (m || wwf))
           then calc ([s], t) else r));

inn_usable_rules_wf_tp ::
  forall a b.
    (Compare.Compare_order b,
      Eq b) => Termination_Problem_Spec.Tp_ops_ext a b [Arith.Char] () ->
                 a -> Bool ->
                        ([Term_Rewriting.Term b [Arith.Char]],
                          Term_Rewriting.Term b [Arith.Char]) ->
                          [(Term_Rewriting.Term b [Arith.Char],
                             Term_Rewriting.Term b [Arith.Char])];
inn_usable_rules_wf_tp i d nfs =
  inn_usable_rules_wf (Termination_Problem_Spec.is_QNF i d)
    (Icap_Impl.icap_impl_tp i d) (Termination_Problem_Spec.rules i d) nfs;

inn_usable_rules_wf_dpp ::
  forall a b.
    (Compare.Compare_order b,
      Eq b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b [Arith.Char] () ->
                 a -> Bool ->
                        ([Term_Rewriting.Term b [Arith.Char]],
                          Term_Rewriting.Term b [Arith.Char]) ->
                          [(Term_Rewriting.Term b [Arith.Char],
                             Term_Rewriting.Term b [Arith.Char])];
inn_usable_rules_wf_dpp i d nfs =
  inn_usable_rules_wf (Dependency_Pair_Problem_Spec.is_QNF i d)
    (Icap_Impl.icap_impl_dpp i d) (Dependency_Pair_Problem_Spec.rules i d) nfs;

is_ur_closed_term_af_impl ::
  forall a b c.
    (Compare.Compare a, Eq a, Arith.Ceq c,
      Arith.Ccompare c) => (Term_Rewriting.Term a [Arith.Char] -> Bool) ->
                             (Term_Rewriting.Term a b ->
                               Term_Rewriting.Term a
                                 (Sum_Type.Sum () [Arith.Char])) ->
                               ((a, Arith.Nat) -> Arith.Set Arith.Nat) ->
                                 [(Term_Rewriting.Term a [Arith.Char], c)] ->
                                   Arith.Set
                                     (Term_Rewriting.Term a [Arith.Char], c) ->
                                     [Term_Rewriting.Term a [Arith.Char]] ->
                                       Term_Rewriting.Term a b -> Bool;
is_ur_closed_term_af_impl nfq e_cap pi r u s (Term_Rewriting.Var x) = True;
is_ur_closed_term_af_impl nfq e_cap pi r u s (Term_Rewriting.Fun f ts) =
  let {
    n = Arith.size_list ts;
    pi_f = pi (f, n);
  } in all (\ (i, t) ->
             (if Arith.member i pi_f
               then is_ur_closed_term_af_impl nfq e_cap pi r u s t else True))
         (zip (Arith.upt Arith.zero_nat n) ts) &&
         let {
           fts = Icap.class_to_term Arith.char_0x7A
                   (Term_Rewriting.Fun f (map e_cap ts));
         } in all (\ (l, ra) ->
                    Arith.member (l, ra) u ||
                      not (rule_match_impl_aux nfq s fts l))
                r;

is_ur_closed_af_impl_tp_mv ::
  forall a b.
    (Compare.Compare_order b, Eq b,
      Term_Rewriting.Showl b) => Termination_Problem_Spec.Tp_ops_ext a b
                                   [Arith.Char] () ->
                                   a -> ((b, Arith.Nat) ->
  Arith.Set Arith.Nat) ->
  [(Term_Rewriting.Term b [Arith.Char], Term_Rewriting.Term b [Arith.Char])] ->
    [Term_Rewriting.Term b [Arith.Char]] ->
      Term_Rewriting.Term b [Arith.Char] -> Bool;
is_ur_closed_af_impl_tp_mv i d pi u =
  let {
    ic = Icap_Impl.icap_impl_tp i d;
    qnf = Termination_Problem_Spec.is_QNF i d;
    r = Termination_Problem_Spec.rules i d;
    urc = (\ s -> is_ur_closed_term_af_impl qnf (ic s) pi r (Arith.set u));
  } in (\ s ->
         let {
           sa = map (Term_Rewriting.map_term (\ x -> x)
                      (\ a -> Arith.char_0x78 : a))
                  s;
         } in (\ t ->
                urc sa sa
                  (Term_Rewriting.map_term (\ x -> x)
                    (\ a -> Arith.char_0x78 : a) t)));

is_ur_closed_af_impl_dpp_mv ::
  forall a b.
    (Compare.Compare_order b, Eq b,
      Term_Rewriting.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b
                                   [Arith.Char] () ->
                                   a -> ((b, Arith.Nat) ->
  Arith.Set Arith.Nat) ->
  [(Term_Rewriting.Term b [Arith.Char], Term_Rewriting.Term b [Arith.Char])] ->
    [Term_Rewriting.Term b [Arith.Char]] ->
      Term_Rewriting.Term b [Arith.Char] -> Bool;
is_ur_closed_af_impl_dpp_mv i d pi u =
  let {
    ic = Icap_Impl.icap_impl_dpp i d;
    qnf = Dependency_Pair_Problem_Spec.is_QNF i d;
    r = Dependency_Pair_Problem_Spec.rules i d;
    urc = (\ s -> is_ur_closed_term_af_impl qnf (ic s) pi r (Arith.set u));
  } in (\ s ->
         let {
           sa = map (Term_Rewriting.map_term (\ x -> x)
                      (\ a -> Arith.char_0x78 : a))
                  s;
         } in (\ t ->
                urc sa sa
                  (Term_Rewriting.map_term (\ x -> x)
                    (\ a -> Arith.char_0x78 : a) t)));

mono_inn_usable_rules_ce_proc ::
  forall a b.
    (Arith.Ceq b, Arith.Ccompare b, Compare.Compare_order b, Eq b,
      Arith.Set_impl b,
      Term_Rewriting.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b
                                   [Arith.Char] () ->
                                   Term_Rewriting.Rel_impl_ext b [Arith.Char]
                                     () ->
                                     [(Term_Rewriting.Term b [Arith.Char],
Term_Rewriting.Term b [Arith.Char])] ->
                                       [(Term_Rewriting.Term b [Arith.Char],
  Term_Rewriting.Term b [Arith.Char])] ->
 [(Term_Rewriting.Term b [Arith.Char], Term_Rewriting.Term b [Arith.Char])] ->
   a -> Sum_Type.Sum (String -> String) a;
mono_inn_usable_rules_ce_proc i rp premove rrem ur dpp =
  let {
    r = Dependency_Pair_Problem_Spec.rules i dpp;
    ura = Arith.set ur;
    non_ur = filter (\ ra -> not (Arith.member ra ura)) r;
    rremove = non_ur ++ rrem;
  } in (case Error_Monad.catch_error
               (Error_Monad.bind (usable_rules_proc i ur dpp)
                 (\ _ ->
                   let {
                     p = Dependency_Pair_Problem_Spec.pairs i dpp;
                     us = Arith.foldr
                            (Arith.sup_set . Term_Rewriting.funas_term . snd)
                            (p ++ ur) Arith.bot_set;
                     filt =
                       (\ lr ->
                         Arith.ball (Term_Rewriting.funas_term (fst lr))
                           (\ f -> Arith.member f us));
                   } in (case Dependency_Pair_Problem_Spec.split_pairs i dpp
                                premove
                          of {
                          (pms, pns) ->
                            (case Arith.partition filt pms of {
                              (ps, pnwf) ->
                                (case Arith.partition (Arith.membera rremove) ur
                                  of {
                                  (urms, urns) ->
                                    (case Arith.partition filt urms of {
                                      (urs, urnwf) ->
Error_Monad.bind
  (Term_Rewriting.rel_impl_mono_ce_redpair rp (ps ++ urs)
    (urns ++ urnwf ++ pns ++ pnwf))
  (\ _ ->
    Error_Monad.bind
      (Error_Monad.catch_error (Term_Rewriting.rel_impl_ns rp (urns ++ urnwf))
        (\ x ->
          Sum_Type.Inl
            (Term_Rewriting.showsl_lit "problem when orienting usable rules\n" .
              x)))
      (\ _ ->
        Error_Monad.bind
          (Error_Monad.catch_error (Term_Rewriting.rel_impl_s rp urs)
            (\ x ->
              Sum_Type.Inl
                (Term_Rewriting.showsl_lit
                   "problem when orienting usable rules\n" .
                  x)))
          (\ _ ->
            Error_Monad.bind
              (Error_Monad.catch_error
                (Term_Rewriting.rel_impl_ns rp (pns ++ pnwf))
                (\ x ->
                  Sum_Type.Inl
                    (Term_Rewriting.showsl_lit "problem when orienting DPs\n" .
                      x)))
              (\ _ ->
                Error_Monad.catch_error (Term_Rewriting.rel_impl_s rp ps)
                  (\ x ->
                    Sum_Type.Inl
                      (Term_Rewriting.showsl_lit
                         "problem when orienting DPs\n" .
                        x))))));
                                    });
                                });
                            });
                        })))
               (\ x ->
                 Sum_Type.Inl
                   (((Term_Rewriting.showsl_lit
                        "could not apply the innermost usable rules reduction pair processor with the following\n" .
                       Term_Rewriting.desc rp) .
                      Term_Rewriting.showsl_literal "\n") .
                     x))
         of {
         Sum_Type.Inl a -> Sum_Type.Inl a;
         Sum_Type.Inr _ ->
           Sum_Type.Inr
             (Dependency_Pair_Problem_Spec.delete_R_Rw i
               (Dependency_Pair_Problem_Spec.delete_P_Pw i dpp premove premove)
               rremove rremove);
       });

}
