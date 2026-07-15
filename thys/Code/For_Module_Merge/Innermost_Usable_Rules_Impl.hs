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
import qualified Subterm_and_Context;
import qualified Term_Order_Impl;
import qualified Inductive_Set_Impl;
import qualified Map_Choice;
import qualified Term_Order;
import qualified Compare_Order_Instances;
import qualified Container_Setup;
import qualified Compare_Instances;
import qualified Termination_Problem_Spec;
import qualified Icap_Impl;
import qualified Collection_Enum;
import qualified Set_Impl;
import qualified Unification;
import qualified Term_Impl;
import qualified Term_More;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Dependency_Pair_Problem_Spec;
import qualified Shows_Literal;
import qualified Compare;
import qualified Option;
import qualified Icap;
import qualified Product_Type;
import qualified List;
import qualified HOL;
import qualified Sum_Type;
import qualified Set;
import qualified Arith;
import qualified Str;
import qualified Term;
import qualified Collection_Order;
import qualified Collection_Eq;

rule_match_impl ::
  forall a b.
    (Eq a) => (Term.Term a [Str.Char] -> Bool) ->
                (b -> Term.Term a (Sum_Type.Sum () [Str.Char])) ->
                  [Term.Term a [Str.Char]] ->
                    a -> [b] -> Term.Term a [Str.Char] -> Bool;
rule_match_impl nfq e_cap s f ts l =
  (case Icap.mgu_class (Term.Fun f (map e_cap ts)) l of {
    Nothing -> False;
    Just mu ->
      all (\ u ->
            nfq (Term.eval_term Term.Fun
                  (Term.map_term (\ x -> x) (\ a -> Str.char_0x79 : a) u) mu))
        (Term.args l) &&
        all (\ u -> nfq (Term.eval_term Term.Fun u mu)) s;
  });

ur_term_impl ::
  forall a b c.
    (Eq a,
      Eq c) => (Term.Term a [Str.Char] -> Bool) ->
                 (Term.Term a b -> Term.Term a (Sum_Type.Sum () [Str.Char])) ->
                   [(Term.Term a [Str.Char], c)] ->
                     ((a, Arith.Nat) -> Set.Set Arith.Nat) ->
                       [Term.Term a [Str.Char]] ->
                         Term.Term a b -> [(Term.Term a [Str.Char], c)];
ur_term_impl nfq e_cap r pi s (Term.Var x) = [];
ur_term_impl nfq e_cap r pi s (Term.Fun f ts) =
  let {
    n = List.size_list ts;
    rec = map (ur_term_impl nfq e_cap r pi s) ts;
  } in List.remdups
         (concatMap
            (\ (i, urs) -> (if Set.member i (pi (f, n)) then urs else []))
            (zip (List.upt Arith.zero_nat n) rec) ++
           filter (\ (l, _) -> rule_match_impl nfq e_cap s f ts l) r);

usable_rules_calc_impl ::
  forall a.
    (Compare.Compare_order a,
      Eq a) => (Term.Term a [Str.Char] -> Bool) ->
                 ([Term.Term a [Str.Char]] ->
                   Term.Term a [Str.Char] ->
                     Term.Term a (Sum_Type.Sum () [Str.Char])) ->
                   [(Term.Term a [Str.Char], Term.Term a [Str.Char])] ->
                     [([Term.Term a [Str.Char]], Term.Term a [Str.Char])] ->
                       [(Term.Term a [Str.Char], Term.Term a [Str.Char])];
usable_rules_calc_impl nfq e_cap r =
  let {
    urt = (\ (s, t) ->
            let {
              sa = map (Term.map_term (\ x -> x) (\ a -> Str.char_0x78 : a)) s;
            } in ur_term_impl nfq (e_cap sa) r Term_Order.full_af sa
                   (Term.map_term (\ x -> x) (\ a -> Str.char_0x78 : a) t));
    urules = map (\ (l, a) -> (Term.args l, a)) r;
    ufun = Map_Choice.precompute_fun urt urules;
  } in Inductive_Set_Impl.inductive_set_impl_lazy ufun
         (\ (l, ra) -> [(Term.args l, ra)]);

ur_calc_singleton ::
  forall a.
    (Compare.Compare_order a,
      Eq a) => (Term.Term a [Str.Char] -> Bool) ->
                 ([Term.Term a [Str.Char]] ->
                   Term.Term a [Str.Char] ->
                     Term.Term a (Sum_Type.Sum () [Str.Char])) ->
                   [(Term.Term a [Str.Char], Term.Term a [Str.Char])] ->
                     ([Term.Term a [Str.Char]], Term.Term a [Str.Char]) ->
                       [(Term.Term a [Str.Char], Term.Term a [Str.Char])];
ur_calc_singleton nfq e_cap r st = usable_rules_calc_impl nfq e_cap r [st];

rule_match_impl_aux ::
  forall a.
    (Eq a) => (Term.Term a [Str.Char] -> Bool) ->
                [Term.Term a [Str.Char]] ->
                  Term.Term a [Str.Char] -> Term.Term a [Str.Char] -> Bool;
rule_match_impl_aux nfq s fts l =
  (case Unification.mgu fts
          (Term.map_term (\ x -> x) (\ a -> Str.char_0x79 : a) l)
    of {
    Nothing -> False;
    Just mu ->
      all (\ u ->
            nfq (Term.eval_term Term.Fun
                  (Term.map_term (\ x -> x) (\ a -> Str.char_0x79 : a) u) mu))
        (Term.args l) &&
        all (\ u -> nfq (Term.eval_term Term.Fun u mu)) s;
  });

is_ur_closed_term_impl ::
  forall a b c.
    (Compare.Compare a, Eq a, Collection_Eq.Ceq c,
      Collection_Order.Ccompare c) => (Term.Term a [Str.Char] -> Bool) ->
(Term.Term a b -> Term.Term a (Sum_Type.Sum () [Str.Char])) ->
  [(Term.Term a [Str.Char], c)] ->
    Set.Set (Term.Term a [Str.Char], c) ->
      [Term.Term a [Str.Char]] -> Term.Term a b -> Bool;
is_ur_closed_term_impl nfq e_cap r u s (Term.Var x) = True;
is_ur_closed_term_impl nfq e_cap r u s (Term.Fun f ts) =
  all (is_ur_closed_term_impl nfq e_cap r u s) ts &&
    let {
      fts = Icap.class_to_term Str.char_0x7A (Term.Fun f (map e_cap ts));
    } in all (\ (l, ra) ->
               Set.member (l, ra) u || not (rule_match_impl_aux nfq s fts l))
           r;

is_ur_closed_impl_dpp_mv ::
  forall a b.
    (Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b
                                  [Str.Char] () ->
                                  a -> [(Term.Term b [Str.Char],
  Term.Term b [Str.Char])] ->
 [Term.Term b [Str.Char]] -> Term.Term b [Str.Char] -> Bool;
is_ur_closed_impl_dpp_mv i d u =
  let {
    ic = Icap_Impl.icap_impl_dpp i d;
    qnf = Dependency_Pair_Problem_Spec.is_QNF i d;
    r = Dependency_Pair_Problem_Spec.rules i d;
    urc = (\ s -> is_ur_closed_term_impl qnf (ic s) r (List.set u));
  } in (\ s ->
         let {
           sa = map (Term.map_term (\ x -> x) (\ a -> Str.char_0x78 : a)) s;
         } in (\ t ->
                urc sa sa
                  (Term.map_term (\ x -> x) (\ a -> Str.char_0x78 : a) t)));

usable_rules_proc ::
  forall a b.
    (Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b
                                  [Str.Char] () ->
                                  [(Term.Term b [Str.Char],
                                     Term.Term b [Str.Char])] ->
                                    a -> Sum_Type.Sum (String -> String) a;
usable_rules_proc i u dpp =
  (case Error_Monad.bind
          (Check_Monad.check
            (Dependency_Pair_Problem_Spec.nFQ_subset_NF_rules i dpp)
            (Shows_Literal.showsl_lit "innermost rewriting required"))
          (\ _ ->
            Error_Monad.bind
              (Check_Monad.check
                (Dependency_Pair_Problem_Spec.nfs i dpp ||
                  (Dependency_Pair_Problem_Spec.minimal i dpp ||
                    Dependency_Pair_Problem_Spec.wwf_rules i dpp))
                (Shows_Literal.showsl_lit
                  "normal form subst, minimality or well-formedness required"))
              (\ _ ->
                let {
                  p = Dependency_Pair_Problem_Spec.pairs i dpp;
                  urc = is_ur_closed_impl_dpp_mv i dpp u;
                  check_urc =
                    (\ s t ->
                      Check_Monad.check (urc s t)
                        ((Shows_Literal.showsl_lit "term " .
                           Term_More.showsl_terma t) .
                          Shows_Literal.showsl_lit
                            " is not closed under usable rules"));
                  nfs = Dependency_Pair_Problem_Spec.nfs i dpp;
                } in Error_Monad.bind
                       (Error_Monad.catch_error
                         (Error_Monad.forallM
                           (\ (l, r) ->
                             Error_Monad.bind
                               (if nfs then Sum_Type.Inr ()
                                 else Error_Monad.catch_error
(Check_Monad.check_subseteq (Term_More.vars_term_list r)
  (Term_More.vars_term_list l))
(\ _ ->
  Sum_Type.Inl (Shows_Literal.showsl_lit "variable condition in P violated")))
                               (\ _ -> check_urc [l] r))
                           p)
                         (\ x -> Sum_Type.Inl (snd x)))
                       (\ _ ->
                         Error_Monad.catch_error
                           (Error_Monad.forallM
                             (\ (l, a) -> check_urc (Term.args l) a) u)
                           (\ x -> Sum_Type.Inl (snd x)))))
    of {
    Sum_Type.Inl a -> Sum_Type.Inl a;
    Sum_Type.Inr _ ->
      Sum_Type.Inr (Dependency_Pair_Problem_Spec.intersect_rules i dpp u);
  });

inn_usable_rules_wf ::
  forall a.
    (Compare.Compare_order a,
      Eq a) => (Term.Term a [Str.Char] -> Bool) ->
                 ([Term.Term a [Str.Char]] ->
                   Term.Term a [Str.Char] ->
                     Term.Term a (Sum_Type.Sum () [Str.Char])) ->
                   [(Term.Term a [Str.Char], Term.Term a [Str.Char])] ->
                     Bool ->
                       ([Term.Term a [Str.Char]], Term.Term a [Str.Char]) ->
                         [(Term.Term a [Str.Char], Term.Term a [Str.Char])];
inn_usable_rules_wf nfq e_cap r nfs =
  (\ (ss, t) ->
    (if nfs ||
          all (\ x -> any (Term_Impl.contains_var_term x) ss)
            (List.remdups (Term_More.vars_term_list t))
      then ur_calc_singleton nfq e_cap r (ss, t) else r));

inn_usable_rules_pair ::
  forall a b.
    (Compare.Compare_order b,
      Eq b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b [Str.Char] () ->
                 a -> (Term.Term b [Str.Char], Term.Term b [Str.Char]) ->
                        [(Term.Term b [Str.Char], Term.Term b [Str.Char])];
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
               (nfs || Set.less_eq_set (Term.vars_term t) (Term.vars_term s)) &&
                 (nfs || (m || wwf))
           then calc ([s], t) else r));

inn_usable_rules_wf_tp ::
  forall a b.
    (Compare.Compare_order b,
      Eq b) => Termination_Problem_Spec.Tp_ops_ext a b [Str.Char] () ->
                 a -> Bool ->
                        ([Term.Term b [Str.Char]], Term.Term b [Str.Char]) ->
                          [(Term.Term b [Str.Char], Term.Term b [Str.Char])];
inn_usable_rules_wf_tp i d nfs =
  inn_usable_rules_wf (Termination_Problem_Spec.is_QNF i d)
    (Icap_Impl.icap_impl_tp i d) (Termination_Problem_Spec.rules i d) nfs;

inn_usable_rules_wf_dpp ::
  forall a b.
    (Compare.Compare_order b,
      Eq b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b [Str.Char] () ->
                 a -> Bool ->
                        ([Term.Term b [Str.Char]], Term.Term b [Str.Char]) ->
                          [(Term.Term b [Str.Char], Term.Term b [Str.Char])];
inn_usable_rules_wf_dpp i d nfs =
  inn_usable_rules_wf (Dependency_Pair_Problem_Spec.is_QNF i d)
    (Icap_Impl.icap_impl_dpp i d) (Dependency_Pair_Problem_Spec.rules i d) nfs;

is_ur_closed_term_af_impl ::
  forall a b c.
    (Compare.Compare a, Eq a, Collection_Eq.Ceq c,
      Collection_Order.Ccompare c) => (Term.Term a [Str.Char] -> Bool) ->
(Term.Term a b -> Term.Term a (Sum_Type.Sum () [Str.Char])) ->
  ((a, Arith.Nat) -> Set.Set Arith.Nat) ->
    [(Term.Term a [Str.Char], c)] ->
      Set.Set (Term.Term a [Str.Char], c) ->
        [Term.Term a [Str.Char]] -> Term.Term a b -> Bool;
is_ur_closed_term_af_impl nfq e_cap pi r u s (Term.Var x) = True;
is_ur_closed_term_af_impl nfq e_cap pi r u s (Term.Fun f ts) =
  let {
    n = List.size_list ts;
    pi_f = pi (f, n);
  } in all (\ (i, t) ->
             (if Set.member i pi_f
               then is_ur_closed_term_af_impl nfq e_cap pi r u s t else True))
         (zip (List.upt Arith.zero_nat n) ts) &&
         let {
           fts = Icap.class_to_term Str.char_0x7A (Term.Fun f (map e_cap ts));
         } in all (\ (l, ra) ->
                    Set.member (l, ra) u ||
                      not (rule_match_impl_aux nfq s fts l))
                r;

is_ur_closed_af_impl_tp_mv ::
  forall a b.
    (Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => Termination_Problem_Spec.Tp_ops_ext a b
                                  [Str.Char] () ->
                                  a -> ((b, Arith.Nat) -> Set.Set Arith.Nat) ->
 [(Term.Term b [Str.Char], Term.Term b [Str.Char])] ->
   [Term.Term b [Str.Char]] -> Term.Term b [Str.Char] -> Bool;
is_ur_closed_af_impl_tp_mv i d pi u =
  let {
    ic = Icap_Impl.icap_impl_tp i d;
    qnf = Termination_Problem_Spec.is_QNF i d;
    r = Termination_Problem_Spec.rules i d;
    urc = (\ s -> is_ur_closed_term_af_impl qnf (ic s) pi r (List.set u));
  } in (\ s ->
         let {
           sa = map (Term.map_term (\ x -> x) (\ a -> Str.char_0x78 : a)) s;
         } in (\ t ->
                urc sa sa
                  (Term.map_term (\ x -> x) (\ a -> Str.char_0x78 : a) t)));

is_ur_closed_af_impl_dpp_mv ::
  forall a b.
    (Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b
                                  [Str.Char] () ->
                                  a -> ((b, Arith.Nat) -> Set.Set Arith.Nat) ->
 [(Term.Term b [Str.Char], Term.Term b [Str.Char])] ->
   [Term.Term b [Str.Char]] -> Term.Term b [Str.Char] -> Bool;
is_ur_closed_af_impl_dpp_mv i d pi u =
  let {
    ic = Icap_Impl.icap_impl_dpp i d;
    qnf = Dependency_Pair_Problem_Spec.is_QNF i d;
    r = Dependency_Pair_Problem_Spec.rules i d;
    urc = (\ s -> is_ur_closed_term_af_impl qnf (ic s) pi r (List.set u));
  } in (\ s ->
         let {
           sa = map (Term.map_term (\ x -> x) (\ a -> Str.char_0x78 : a)) s;
         } in (\ t ->
                urc sa sa
                  (Term.map_term (\ x -> x) (\ a -> Str.char_0x78 : a) t)));

mono_inn_usable_rules_ce_proc ::
  forall a b.
    (Collection_Eq.Ceq b, Collection_Order.Ccompare b, Compare.Compare_order b,
      Eq b, Set_Impl.Set_impl b,
      Shows_Literal.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b
                                  [Str.Char] () ->
                                  Term_Order_Impl.Rel_impl_ext b [Str.Char]
                                    () ->
                                    [(Term.Term b [Str.Char],
                                       Term.Term b [Str.Char])] ->
                                      [(Term.Term b [Str.Char],
 Term.Term b [Str.Char])] ->
[(Term.Term b [Str.Char], Term.Term b [Str.Char])] ->
  a -> Sum_Type.Sum (String -> String) a;
mono_inn_usable_rules_ce_proc i rp premove rrem ur dpp =
  let {
    r = Dependency_Pair_Problem_Spec.rules i dpp;
    ura = List.set ur;
    non_ur = filter (\ ra -> not (Set.member ra ura)) r;
    rremove = non_ur ++ rrem;
  } in (case Error_Monad.catch_error
               (Error_Monad.bind (usable_rules_proc i ur dpp)
                 (\ _ ->
                   let {
                     p = Dependency_Pair_Problem_Spec.pairs i dpp;
                     us = List.foldr
                            (Set.sup_set . Subterm_and_Context.funas_term . snd)
                            (p ++ ur) Set.bot_set;
                     filt =
                       (\ lr ->
                         Set.ball (Subterm_and_Context.funas_term (fst lr))
                           (\ f -> Set.member f us));
                   } in (case Dependency_Pair_Problem_Spec.split_pairs i dpp
                                premove
                          of {
                          (pms, pns) ->
                            (case List.partition filt pms of {
                              (ps, pnwf) ->
                                (case List.partition (List.member rremove) ur of
                                  {
                                  (urms, urns) ->
                                    (case List.partition filt urms of {
                                      (urs, urnwf) ->
Error_Monad.bind
  (Term_Order_Impl.rel_impl_mono_ce_redpair rp (ps ++ urs)
    (urns ++ urnwf ++ pns ++ pnwf))
  (\ _ ->
    Error_Monad.bind
      (Error_Monad.catch_error (Term_Order_Impl.rel_impl_ns rp (urns ++ urnwf))
        (\ x ->
          Sum_Type.Inl
            (Shows_Literal.showsl_lit "problem when orienting usable rules\n" .
              x)))
      (\ _ ->
        Error_Monad.bind
          (Error_Monad.catch_error (Term_Order_Impl.rel_impl_s rp urs)
            (\ x ->
              Sum_Type.Inl
                (Shows_Literal.showsl_lit
                   "problem when orienting usable rules\n" .
                  x)))
          (\ _ ->
            Error_Monad.bind
              (Error_Monad.catch_error
                (Term_Order_Impl.rel_impl_ns rp (pns ++ pnwf))
                (\ x ->
                  Sum_Type.Inl
                    (Shows_Literal.showsl_lit "problem when orienting DPs\n" .
                      x)))
              (\ _ ->
                Error_Monad.catch_error (Term_Order_Impl.rel_impl_s rp ps)
                  (\ x ->
                    Sum_Type.Inl
                      (Shows_Literal.showsl_lit "problem when orienting DPs\n" .
                        x))))));
                                    });
                                });
                            });
                        })))
               (\ x ->
                 Sum_Type.Inl
                   (((Shows_Literal.showsl_lit
                        "could not apply the innermost usable rules reduction pair processor with the following\n" .
                       Term_Order_Impl.desc rp) .
                      Shows_Literal.showsl_literal "\n") .
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
