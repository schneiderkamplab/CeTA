{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Usable_Replacement_Map_Impl(showsl_position_set, rule_shift_complexity_urm_tt,
                               get_innermost_strict_repl_map_dpp, get_fs_mu,
                               get_fs_mu_DP)
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
import qualified Complexity_Framework_Impl;
import qualified Inductive_Set_Impl;
import qualified Dependency_Pair_Problem_Spec;
import qualified Name;
import qualified Icap_Impl;
import qualified Innermost_Usable_Rules_Impl;
import qualified Map_Choice;
import qualified Missing_List;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Termination_Problem_Spec;
import qualified Sum_Type;
import qualified Compare;
import qualified Compare_Order_Instances;
import qualified Term_Rewriting;
import qualified Term_Order;
import qualified HOL;
import qualified Phantom_Type;
import qualified Arith;

full_empty ::
  forall a.
    (Eq a) => [(a, Arith.Nat)] ->
                ([(a, Arith.Nat)],
                  ((a, Arith.Nat) -> Arith.Set Arith.Nat, String));
full_empty fs =
  let {
    fsa = filter (\ (_, n) -> not (Arith.equal_nat n Arith.zero_nat)) fs;
  } in (fsa, ((\ f ->
                (if Arith.membera fsa f then Term_Order.full_af f
                  else Arith.set_empty
                         (Phantom_Type.of_phantom Arith.set_impl_nat))),
               "full AF"));

get_args_impl ::
  forall a b. Bool -> Term_Rewriting.Term a b -> [Term_Rewriting.Term a b];
get_args_impl True t = Term_Rewriting.args t;
get_args_impl False t = [t];

showsl_position_set ::
  forall a. (a, Arith.Nat) -> Arith.Set Arith.Nat -> String -> String;
showsl_position_set f s =
  Term_Rewriting.showsl_list_nat
    (concatMap (\ i -> (if Arith.member i s then [Arith.suc i] else []))
      (Arith.upt Arith.zero_nat (snd f)));

default_fs ::
  forall a.
    (Compare.Compare_order a,
      Term_Rewriting.Showl a) => [(Term_Rewriting.Term a [Arith.Char],
                                    Term_Rewriting.Term a [Arith.Char])] ->
                                   [(a, Arith.Nat)];
default_fs r = Term_Rewriting.funas_trs_list r;

all_terms_impl ::
  forall a.
    (Compare.Compare_order a,
      Eq a) => [(Term_Rewriting.Term a [Arith.Char],
                  Term_Rewriting.Term a [Arith.Char])] ->
                 [([Term_Rewriting.Term a [Arith.Char]],
                    (Term_Rewriting.Term a [Arith.Char],
                      (Term_Rewriting.Term a [Arith.Char],
                        Term_Rewriting.Term a [Arith.Char])))] ->
                   [([Term_Rewriting.Term a [Arith.Char]],
                      Term_Rewriting.Term a [Arith.Char])];
all_terms_impl rr initt =
  Arith.remdups
    (map (\ (ss, (t, _)) -> (ss, t)) initt ++
      map (\ (l, a) -> (Term_Rewriting.args l, a)) rr);

all_subterms_impl ::
  forall a.
    (Compare.Compare_order a,
      Eq a) => [(Term_Rewriting.Term a [Arith.Char],
                  Term_Rewriting.Term a [Arith.Char])] ->
                 [([Term_Rewriting.Term a [Arith.Char]],
                    (Term_Rewriting.Term a [Arith.Char],
                      (Term_Rewriting.Term a [Arith.Char],
                        Term_Rewriting.Term a [Arith.Char])))] ->
                   [([Term_Rewriting.Term a [Arith.Char]],
                      Term_Rewriting.Term a [Arith.Char])];
all_subterms_impl rr initt =
  Arith.remdups
    (concatMap
      (\ (ss, s) -> map (\ a -> (ss, a)) (Term_Rewriting.supteq_list s))
      (all_terms_impl rr initt));

everything_impl ::
  forall a.
    (Compare.Compare_order a,
      Eq a) => [(Term_Rewriting.Term a [Arith.Char],
                  Term_Rewriting.Term a [Arith.Char])] ->
                 [([Term_Rewriting.Term a [Arith.Char]],
                    (Term_Rewriting.Term a [Arith.Char],
                      (Term_Rewriting.Term a [Arith.Char],
                        Term_Rewriting.Term a [Arith.Char])))] ->
                   [Sum_Type.Sum
                      ([Term_Rewriting.Term a [Arith.Char]],
                        (Term_Rewriting.Term a [Arith.Char],
                          (Term_Rewriting.Term a [Arith.Char],
                            Term_Rewriting.Term a [Arith.Char])))
                      ((a, Arith.Nat), Arith.Nat)];
everything_impl rr initt =
  map Sum_Type.Inl
    (concatMap
      (\ (ss, t) ->
        map (\ lr -> (ss, (t, lr))) (Arith.remdups (map (snd . snd) initt)))
      (all_subterms_impl rr initt)) ++
    Arith.remdups
      (map Sum_Type.Inr
        (concatMap
          (\ t ->
            (if not (Term_Rewriting.is_Var t)
              then concatMap
                     (\ (f, ts) ->
                       map (\ a -> ((f, Arith.size_list ts), a))
                         (Arith.upt Arith.zero_nat (Arith.size_list ts)))
                     (case t of {
                       Term_Rewriting.Fun f ts -> [(f, ts)];
                     })
              else []))
          (Arith.remdups (map snd (all_subterms_impl rr initt)))));

generate_impl ::
  forall a b c d.
    (Compare.Compare_order a, Eq a, Eq b,
      Eq c) => [(Term_Rewriting.Term a [Arith.Char],
                  Term_Rewriting.Term a [Arith.Char])] ->
                 (Term_Rewriting.Term a [Arith.Char] -> Bool) ->
                   ([Term_Rewriting.Term a [Arith.Char]] ->
                     Term_Rewriting.Term a [Arith.Char] ->
                       Term_Rewriting.Term a (Sum_Type.Sum () [Arith.Char])) ->
                     ([Term_Rewriting.Term a [Arith.Char]] ->
                       Term_Rewriting.Term a [Arith.Char] -> [(b, c)]) ->
                       Sum_Type.Sum
                         ([Term_Rewriting.Term a [Arith.Char]],
                           (Term_Rewriting.Term a [Arith.Char], (b, c)))
                         d ->
                         [Sum_Type.Sum
                            ([Term_Rewriting.Term a [Arith.Char]],
                              (Term_Rewriting.Term a [Arith.Char], (b, c)))
                            ((a, Arith.Nat), Arith.Nat)];
generate_impl rr nfq e_cap uu
  (Sum_Type.Inl (ss, (Term_Rewriting.Fun f ts, (l, r)))) =
  concatMap
    (\ i ->
      (if Arith.membera (uu ss (Arith.nth ts i)) (l, r)
        then map (\ u -> u)
               [Sum_Type.Inl (ss, (Arith.nth ts i, (l, r))),
                 Sum_Type.Inr ((f, Arith.size_list ts), i)]
        else []))
    (Arith.upt Arith.zero_nat (Arith.size_list ts)) ++
    concatMap
      (\ (la, ra) ->
        concatMap
          (\ mss ->
            (if Innermost_Usable_Rules_Impl.rule_match_impl nfq (e_cap mss) mss
                  f (map (Term_Rewriting.map_term (\ x -> x)
                           (\ a -> Arith.char_0x78 : a))
                      ts)
                  la
              then (if Arith.membera (uu (Term_Rewriting.args la) ra) (l, r)
                     then [Sum_Type.Inl (Term_Rewriting.args la, (ra, (l, r)))]
                     else [])
              else []))
          [map (Term_Rewriting.map_term (\ x -> x) (\ a -> Arith.char_0x78 : a))
             ss])
      rr;
generate_impl rr nfq e_cap uu (Sum_Type.Inl (va, (Term_Rewriting.Var ve, vd))) =
  [];
generate_impl rr nfq e_cap uu (Sum_Type.Inr v) = [];

mu_approx_impl ::
  forall a.
    (Compare.Compare_order a,
      Eq a) => [(Term_Rewriting.Term a [Arith.Char],
                  Term_Rewriting.Term a [Arith.Char])] ->
                 [([Term_Rewriting.Term a [Arith.Char]],
                    (Term_Rewriting.Term a [Arith.Char],
                      (Term_Rewriting.Term a [Arith.Char],
                        Term_Rewriting.Term a [Arith.Char])))] ->
                   ([Term_Rewriting.Term a [Arith.Char]] ->
                     Term_Rewriting.Term a [Arith.Char] ->
                       [(Term_Rewriting.Term a [Arith.Char],
                          Term_Rewriting.Term a [Arith.Char])]) ->
                     (Term_Rewriting.Term a [Arith.Char] -> Bool) ->
                       ([Term_Rewriting.Term a [Arith.Char]] ->
                         Term_Rewriting.Term a [Arith.Char] ->
                           Term_Rewriting.Term a
                             (Sum_Type.Sum () [Arith.Char])) ->
                         ([(a, Arith.Nat)],
                           ((a, Arith.Nat) -> Arith.Set Arith.Nat, String));
mu_approx_impl rr initt u_impl nfq e_cap =
  let {
    uu = Map_Choice.precompute_fun (\ (a, b) -> u_impl a b)
           (all_subterms_impl rr initt);
    uua = (\ s t -> uu (s, t));
    fis = Arith.remdups
            (concatMap (\ entry -> map (\ fi -> fi) (case entry of {
              Sum_Type.Inl _ -> [];
              Sum_Type.Inr fi -> [fi];
            }))
              (Inductive_Set_Impl.inductive_set_impl (everything_impl rr initt)
                Sum_Type.equal_sum (generate_impl rr nfq e_cap uua)
                (map Sum_Type.Inl initt)));
    fs = Arith.remdups (map fst fis);
    mu = (\ f ->
           Arith.set
             (Arith.map_filter
               (\ x -> (if (case x of {
                             (g, _) -> g == f;
                           })
                         then Just (snd x) else Nothing))
               fis));
  } in (fs, (Map_Choice.precompute_fun mu fs,
              "innermost URM wrt. specific rules"));

get_innermost_strict_repl_map_rc ::
  forall a b c.
    (Arith.Cenum b, Arith.Ceq b, Arith.Ccompare b, Compare.Compare_order b,
      Eq b, Arith.Set_impl b,
      Term_Rewriting.Showl b) => Termination_Problem_Spec.Tp_ops_ext a b
                                   [Arith.Char] () ->
                                   a -> [(Term_Rewriting.Term b [Arith.Char],
   Term_Rewriting.Term b [Arith.Char])] ->
  Term_Rewriting.Complexity_measure b c ->
    ([(b, Arith.Nat)], ((b, Arith.Nat) -> Arith.Set Arith.Nat, String));
get_innermost_strict_repl_map_rc i d s
  (Term_Rewriting.Derivational_Complexity f) =
  full_empty
    (Arith.remdups (f ++ default_fs (Termination_Problem_Spec.rules i d)));
get_innermost_strict_repl_map_rc i da s (Term_Rewriting.Runtime_Complexity c d)
  = let {
      r = Termination_Problem_Spec.rules i da;
    } in (if Termination_Problem_Spec.nFQ_subset_NF_rules i da &&
               Arith.less_eq_set
                 (Arith.inf_set (Arith.set c)
                   (Arith.set (Term_Rewriting.defined_list r)))
                 Arith.bot_set
           then let {
                  isNF = Termination_Problem_Spec.is_QNF i da;
                  u = Innermost_Usable_Rules_Impl.inn_usable_rules_wf_tp i da
                        True;
                  a = Icap_Impl.icap_impl_tp i da;
                } in mu_approx_impl r
                       (concatMap
                         (\ (f, n) ->
                           concatMap
                             (\ xs ->
                               map (\ lr -> (xs, (Term_Rewriting.Fun f xs, lr)))
                                 s)
                             [map Term_Rewriting.Var (Name.x_1_to_x_n n)])
                         d)
                       (\ ss t -> u (ss, t)) isNF a
           else full_empty (Arith.remdups (c ++ d ++ default_fs r)));

get_innermost_strict_repl_map_rc_DP ::
  forall a b.
    (Arith.Card_UNIV b, Arith.Cenum b, Arith.Ceq b, Arith.Cproper_interval b,
      Compare.Compare_order b, Eq b, Arith.Set_impl b,
      Term_Rewriting.Showl b) => Termination_Problem_Spec.Tp_ops_ext a b
                                   [Arith.Char] () ->
                                   a -> [(Term_Rewriting.Term b [Arith.Char],
   Term_Rewriting.Term b [Arith.Char])] ->
  Term_Rewriting.Complexity_measure b [Arith.Char] ->
    ([(b, Arith.Nat)], ((b, Arith.Nat) -> Arith.Set Arith.Nat, String));
get_innermost_strict_repl_map_rc_DP i d s t =
  (case get_innermost_strict_repl_map_rc i d s t of {
    (fs, (mu, info)) ->
      (case Complexity_Framework_Impl.check_DP_complexity
              (Termination_Problem_Spec.rules i d) t
        of {
        Sum_Type.Inl _ -> (fs, (mu, info));
        Sum_Type.Inr (rs, (_, (cp, (_, _)))) ->
          (if Arith.superset rs s
            then (Arith.inter_list_set fs cp,
                   ((\ f ->
                      (if Arith.membera cp f then mu f
                        else Arith.set_empty
                               (Phantom_Type.of_phantom Arith.set_impl_nat))),
                     info ++ " with DPs"))
            else (fs, (mu, info)));
      });
  });

rule_shift_complexity_urm_tt ::
  forall a b.
    (Arith.Card_UNIV b, Arith.Cenum b, Arith.Ceq b, Arith.Cproper_interval b,
      Compare.Compare_order b, Eq b, Arith.Set_impl b,
      Term_Rewriting.Showl b) => Termination_Problem_Spec.Tp_ops_ext a b
                                   [Arith.Char] () ->
                                   Term_Rewriting.Rel_impl_ext b [Arith.Char]
                                     () ->
                                     [(Term_Rewriting.Term b [Arith.Char],
Term_Rewriting.Term b [Arith.Char])] ->
                                       Term_Rewriting.Complexity_measure b
 [Arith.Char] ->
 Term_Rewriting.Complexity_class -> a -> Sum_Type.Sum (String -> String) a;
rule_shift_complexity_urm_tt i rp rdelete cm cc tp =
  let {
    rb = Termination_Problem_Spec.rules i tp;
    r = Termination_Problem_Spec.r i tp;
    rw = Termination_Problem_Spec.rw i tp;
    r2 = Map_Choice.ceta_list_diff r rdelete;
    _ = Termination_Problem_Spec.q i tp;
  } in (case Error_Monad.catch_error
               (Error_Monad.bind
                 (Error_Monad.catch_error
                   (Check_Monad.check_subseteq rdelete rb)
                   (\ x ->
                     Sum_Type.Inl
                       ((Term_Rewriting.showsl_lit "rule " .
                          Term_Rewriting.showsl_rule x) .
                         Term_Rewriting.showsl_lit
                           " should be deleted, but does not occur in problem")))
                 (\ _ ->
                   Error_Monad.bind (Term_Rewriting.check_wf_trs rb)
                     (\ _ ->
                       (case get_innermost_strict_repl_map_rc_DP i tp rdelete cm
                         of {
                         (fs, (mu, info)) ->
                           Error_Monad.bind (Term_Rewriting.rel_impl_redpair rp)
                             (\ _ ->
                               Error_Monad.bind
                                 (Error_Monad.catch_error
                                   (Error_Monad.catch_error
                                     (Error_Monad.forallM
                                       (\ f ->
 Check_Monad.check (Arith.less_eq_set (mu f) (Term_Rewriting.mono_af rp f))
   (((((Term_Rewriting.showsl_lit "error in monotonicity: strict order for " .
         Term_Rewriting.showsl_prod f) .
        Term_Rewriting.showsl_lit " ensures monotonicity in positions ") .
       showsl_position_set f (Term_Rewriting.mono_af rp f)) .
      Term_Rewriting.showsl_lit "\nbut usable replacement map is ") .
     showsl_position_set f (mu f)))
                                       fs)
                                     (\ x -> Sum_Type.Inl (snd x)))
                                   (\ x ->
                                     Sum_Type.Inl
                                       (((((x .
     Term_Rewriting.showsl_lit "\nthe computed usable replacement map (") .
    Term_Rewriting.showsl_literal info) .
   Term_Rewriting.showsl_lit ") is\n") .
  Term_Rewriting.showsl_sep
    (\ f ->
      ((Term_Rewriting.showsl_lit "mu(" . Term_Rewriting.showsl_prod f) .
        Term_Rewriting.showsl_lit ") = ") .
        showsl_position_set f (mu f))
    (Term_Rewriting.showsl_literal "\n") fs) .
 Term_Rewriting.showsl_lit "\nand mu(f) = {} for all other symbols f")))
                                 (\ _ ->
                                   Error_Monad.bind
                                     (Error_Monad.catch_error
                                       (Term_Rewriting.rel_impl_s rp rdelete)
                                       (\ x ->
 Sum_Type.Inl
   (Term_Rewriting.showsl_lit "problem when orienting strict TRS\n" . x)))
                                     (\ _ ->
                                       Error_Monad.bind
 (Error_Monad.catch_error (Term_Rewriting.rel_impl_ns rp (rw ++ r2))
   (\ x ->
     Sum_Type.Inl
       (Term_Rewriting.showsl_lit "problem when orienting non-strict TRS\n" .
         x)))
 (\ _ ->
   Error_Monad.catch_error (Term_Rewriting.cpx rp cm cc)
     (\ x ->
       Sum_Type.Inl
         (Term_Rewriting.showsl_lit
            "problem when ensuring complexity of order\n" .
           x))))));
                       }))))
               (\ x ->
                 Sum_Type.Inl
                   (((((Term_Rewriting.showsl_lit
                          "could not derive the intended complexity " .
                         Term_Rewriting.showsl_complexity_class cc) .
                        Term_Rewriting.showsl_lit " from the following\n") .
                       Term_Rewriting.desc rp) .
                      Term_Rewriting.showsl_literal "\n") .
                     x))
         of {
         Sum_Type.Inl a -> Sum_Type.Inl a;
         Sum_Type.Inr _ ->
           Sum_Type.Inr
             (Termination_Problem_Spec.mk i (Termination_Problem_Spec.nfs i tp)
               (Termination_Problem_Spec.q i tp) r2
               (Missing_List.list_union rw rdelete));
       });

get_innermost_strict_repl_map_dpp ::
  forall a b.
    (Compare.Compare_order b,
      Eq b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b [Arith.Char] () ->
                 a -> [(Term_Rewriting.Term b [Arith.Char],
                         Term_Rewriting.Term b [Arith.Char])] ->
                        ([(b, Arith.Nat)],
                          ((b, Arith.Nat) -> Arith.Set Arith.Nat, String));
get_innermost_strict_repl_map_dpp i d s =
  let {
    r = Dependency_Pair_Problem_Spec.rules i d;
    p = Dependency_Pair_Problem_Spec.pairs i d;
    isNF = Dependency_Pair_Problem_Spec.is_QNF i d;
    u = Innermost_Usable_Rules_Impl.inn_usable_rules_wf_dpp i d True;
    a = Icap_Impl.icap_impl_dpp i d;
  } in mu_approx_impl r
         (concatMap (\ (sa, t) -> map (\ lr -> ([sa], (t, lr))) s) p)
         (\ ss t -> u (ss, t)) isNF a;

innermost_repl_map_impl ::
  forall a.
    (Compare.Compare_order a, Eq a,
      Term_Rewriting.Showl a) => [(Term_Rewriting.Term a [Arith.Char],
                                    Term_Rewriting.Term a [Arith.Char])] ->
                                   ([Term_Rewriting.Term a [Arith.Char]] ->
                                     Term_Rewriting.Term a [Arith.Char] ->
                                       Term_Rewriting.Term a
 (Sum_Type.Sum () [Arith.Char])) ->
                                     [(Term_Rewriting.Term a [Arith.Char],
Term_Rewriting.Term a [Arith.Char])] ->
                                       [((a, Arith.Nat), Arith.Nat)];
innermost_repl_map_impl r ecap p =
  Arith.remdups
    (concatMap
      (\ (a, b) ->
        (case a of {
          (l, ra) ->
            (\ ba ->
              concatMap
                (\ u ->
                  (if not (Term_Rewriting.is_Var u)
                    then concatMap
                           (\ rs ->
                             concatMap
                               (\ f ->
                                 concatMap
                                   (\ n ->
                                     concatMap
                                       (\ i ->
 (if Term_Rewriting.contains_var_term (Sum_Type.Inl ())
       (ecap (get_args_impl ba l) (Arith.nth rs i))
   then [(f, i)] else []))
                                       (Arith.upt Arith.zero_nat n))
                                   [snd f])
                               [Arith.the (Term_Rewriting.root u)])
                           [Term_Rewriting.args u]
                    else []))
                (Term_Rewriting.supteq_list ra));
        })
          b)
      (map (\ lr -> (lr, True)) r ++ map (\ st -> (st, False)) p));

mu_i_P_impl ::
  forall a.
    (Compare.Compare_order a, Eq a,
      Term_Rewriting.Showl a) => [(Term_Rewriting.Term a [Arith.Char],
                                    Term_Rewriting.Term a [Arith.Char])] ->
                                   ([Term_Rewriting.Term a [Arith.Char]] ->
                                     Term_Rewriting.Term a [Arith.Char] ->
                                       Term_Rewriting.Term a
 (Sum_Type.Sum () [Arith.Char])) ->
                                     [(Term_Rewriting.Term a [Arith.Char],
Term_Rewriting.Term a [Arith.Char])] ->
                                       ([(a, Arith.Nat)],
 ((a, Arith.Nat) -> Arith.Set Arith.Nat, String));
mu_i_P_impl r ecap p =
  let {
    fis = innermost_repl_map_impl r ecap p;
    fs = Arith.remdups (map fst fis);
    mu = (\ f ->
           Arith.set
             (Arith.map_filter
               (\ x -> (if (case x of {
                             (g, _) -> g == f;
                           })
                         then Just (snd x) else Nothing))
               fis));
  } in (fs, (Map_Choice.precompute_fun mu fs, "innermost URM"));

mu_i_impl ::
  forall a.
    (Compare.Compare_order a, Eq a,
      Term_Rewriting.Showl a) => [(Term_Rewriting.Term a [Arith.Char],
                                    Term_Rewriting.Term a [Arith.Char])] ->
                                   ([Term_Rewriting.Term a [Arith.Char]] ->
                                     Term_Rewriting.Term a [Arith.Char] ->
                                       Term_Rewriting.Term a
 (Sum_Type.Sum () [Arith.Char])) ->
                                     ([(a, Arith.Nat)],
                                       ((a, Arith.Nat) -> Arith.Set Arith.Nat,
 String));
mu_i_impl r ecap = mu_i_P_impl r ecap [];

get_fs_mu ::
  forall a.
    (Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a, Compare.Compare_order a,
      Eq a, Arith.Set_impl a,
      Term_Rewriting.Showl a) => [(Term_Rewriting.Term a [Arith.Char],
                                    Term_Rewriting.Term a [Arith.Char])] ->
                                   ([Term_Rewriting.Term a [Arith.Char]] ->
                                     Term_Rewriting.Term a [Arith.Char] ->
                                       Term_Rewriting.Term a
 (Sum_Type.Sum () [Arith.Char])) ->
                                     Bool ->
                                       Term_Rewriting.Complexity_measure a
 [Arith.Char] ->
 ([(a, Arith.Nat)], ((a, Arith.Nat) -> Arith.Set Arith.Nat, String));
get_fs_mu r ecap inn (Term_Rewriting.Derivational_Complexity f) =
  full_empty (Arith.remdups (f ++ default_fs r));
get_fs_mu r ecap inn (Term_Rewriting.Runtime_Complexity c d) =
  (if inn &&
        Arith.less_eq_set
          (Arith.inf_set (Arith.set c)
            (Arith.set (Term_Rewriting.defined_list r)))
          Arith.bot_set
    then mu_i_impl r ecap
    else full_empty (Arith.remdups (c ++ d ++ default_fs r)));

get_fs_mu_DP ::
  forall a.
    (Arith.Card_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Compare.Compare_order a, Eq a, Arith.Set_impl a,
      Term_Rewriting.Showl a) => [(Term_Rewriting.Term a [Arith.Char],
                                    Term_Rewriting.Term a [Arith.Char])] ->
                                   ([Term_Rewriting.Term a [Arith.Char]] ->
                                     Term_Rewriting.Term a [Arith.Char] ->
                                       Term_Rewriting.Term a
 (Sum_Type.Sum () [Arith.Char])) ->
                                     Bool ->
                                       [(Term_Rewriting.Term a [Arith.Char],
  Term_Rewriting.Term a [Arith.Char])] ->
 Term_Rewriting.Complexity_measure a [Arith.Char] ->
   ([(a, Arith.Nat)], ((a, Arith.Nat) -> Arith.Set Arith.Nat, String));
get_fs_mu_DP r ecap inn s cm =
  (case get_fs_mu r ecap inn cm of {
    (fs, (mu, info)) ->
      (case Complexity_Framework_Impl.check_DP_complexity r cm of {
        Sum_Type.Inl _ -> (fs, (mu, info));
        Sum_Type.Inr (rs, (_, (cp, (_, _)))) ->
          (if Arith.superset rs s
            then (Arith.inter_list_set fs cp,
                   ((\ f ->
                      (if Arith.membera cp f then mu f
                        else Arith.set_empty
                               (Phantom_Type.of_phantom Arith.set_impl_nat))),
                     info ++ " with DPs"))
            else (fs, (mu, info)));
      });
  });

}
