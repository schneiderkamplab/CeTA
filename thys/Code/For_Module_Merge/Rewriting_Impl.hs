{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Rewriting_Impl(Rewriting_complete_proc_prf(..), check_nfc,
                  check_rewrite_common_preconditions, rewriting_proc,
                  rewriting_complete_proc)
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
import qualified Innermost_Usable_Rules_Impl;
import qualified Critical_Pairs_Impl;
import qualified Renaming2_String;
import qualified Renaming2;
import qualified Lists_are_Infinite;
import qualified Q_Restricted_Rewriting_Impl;
import qualified Trs;
import qualified List;
import qualified HOL;
import qualified Dependency_Pair_Problem_Spec;
import qualified RTrancl;
import qualified Product_Type;
import qualified Term_More;
import qualified Term_Impl;
import qualified Trs_Impl;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Compare;
import qualified Mapping_Impl;
import qualified Collection_Order;
import qualified Shows_Literal;
import qualified Option;
import qualified Icap_Impl;
import qualified Icap;
import qualified Sum_Type;
import qualified Str;
import qualified Term;
import qualified Arith;

data Rewriting_complete_proc_prf a b =
  Rewriting_complete_proc_prf (Maybe [(Term.Term a b, Term.Term a b)])
    (Term.Term a b, Term.Term a b) (Term.Term a b, Term.Term a b)
    (Term.Term a b, Term.Term a b) (Term.Term a b, Term.Term a b) [Arith.Nat];

enfc_q ::
  forall a.
    (Eq a) => (Term.Term a [Str.Char] -> Bool) ->
                (Term.Term a [Str.Char] -> Bool) ->
                  [(Term.Term a [Str.Char], Term.Term a [Str.Char])] ->
                    [Term.Term a [Str.Char]] ->
                      [Term.Term a [Str.Char]] ->
                        Term.Term a [Str.Char] -> Bool;
enfc_q isQnf isRnf r q s (Term.Var x) = True;
enfc_q isQnf isRnf r q s (Term.Fun f ts) =
  all (\ qa ->
        (case Icap.mgu_class
                (Term.Fun f (map (Icap_Impl.icap_impl isQnf r s) ts)) qa
          of {
          Nothing -> True;
          Just mu ->
            not (all (\ u ->
                       isQnf (Term.eval_term Term.Fun
                               (Term.map_term (\ x -> x)
                                 (\ a -> Str.char_0x78 : a) u)
                               mu))
                   s &&
                  isRnf (Term.eval_term Term.Fun
                          (Term.map_term (\ x -> x) (\ a -> Str.char_0x79 : a)
                            qa)
                          mu));
        }))
    q;

enfc_cand ::
  forall a b.
    (Eq a) => (Term.Term a [Str.Char] -> Bool) ->
                [(Term.Term a [Str.Char], Term.Term a [Str.Char])] ->
                  b -> ([Term.Term a [Str.Char]], Term.Term a [Str.Char]) ->
                         [([Term.Term a [Str.Char]], Term.Term a [Str.Char])];
enfc_cand isQnf r q (uu, Term.Var uv) = [];
enfc_cand isQnf r q (s, Term.Fun f ts) =
  map (\ a -> (s, a)) ts ++
    concatMap
      (\ (l, ra) ->
        (if (case Icap.mgu_class
                    (Term.Fun f (map (Icap_Impl.icap_impl isQnf r s) ts)) l
              of {
              Nothing -> False;
              Just mu ->
                all (\ u ->
                      isQnf (Term.eval_term Term.Fun
                              (Term.map_term (\ x -> x)
                                (\ a -> Str.char_0x79 : a) u)
                              mu))
                  (Term.args l) &&
                  all (\ u ->
                        isQnf (Term.eval_term Term.Fun
                                (Term.map_term (\ x -> x)
                                  (\ a -> Str.char_0x78 : a) u)
                                mu))
                    s;
            })
          then [(Term.args l, ra)] else []))
      r;

enfc_impl ::
  forall a.
    (Eq a) => (Term.Term a [Str.Char] -> Bool) ->
                (Term.Term a [Str.Char] -> Bool) ->
                  [(Term.Term a [Str.Char], Term.Term a [Str.Char])] ->
                    [Term.Term a [Str.Char]] ->
                      [Term.Term a [Str.Char]] ->
                        Term.Term a [Str.Char] -> Bool;
enfc_impl isQnf isRnf r q s t =
  all (\ (a, b) -> enfc_q isQnf isRnf r q a b)
    (RTrancl.mk_rtrancl_list (\ a b -> a == b) (enfc_cand isQnf r q) [(s, t)]);

check_nfc ::
  forall a.
    (Compare.Compare_order a, Eq a,
      Shows_Literal.Showl a) => Bool ->
                                  [(Term.Term a [Str.Char],
                                     Term.Term a [Str.Char])] ->
                                    [Term.Term a [Str.Char]] ->
                                      (Term.Term a [Str.Char] -> Bool) ->
[Term.Term a [Str.Char]] ->
  Bool -> Term.Term a [Str.Char] -> Sum_Type.Sum (String -> String) ();
check_nfc inn r q isQnf ss nfs t =
  Error_Monad.bind (Trs_Impl.check_wf_trs r)
    (\ _ ->
      (if inn then Sum_Type.Inr ()
        else Error_Monad.catch_error
               (Error_Monad.forallM
                 (\ ta ->
                   Check_Monad.check
                     (enfc_impl isQnf (Trs_Impl.is_NF_trs r) r q ss ta)
                     (Shows_Literal.showsl_lit " nfc not satisfied for " .
                       Term_More.showsl_terma ta))
                 (Term_Impl.supteq_list t))
               (\ x -> Sum_Type.Inl (snd x))));

check_rewrite_common_preconditions ::
  forall a b c d.
    (Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b
                                  [Str.Char] () ->
                                  Maybe [(Term.Term b [Str.Char],
   Term.Term b [Str.Char])] ->
                                    (Term.Term b [Str.Char],
                                      Term.Term c [Str.Char]) ->
                                      [Term.Term b [Str.Char]] ->
[Term.Term b [Str.Char]] ->
  d -> (Term.Term b [Str.Char], Term.Term b [Str.Char]) ->
         [Arith.Nat] -> Bool -> a -> Sum_Type.Sum (String -> String) ();
check_rewrite_common_preconditions i u_opt st ss ts t lr p sound dpp =
  let {
    r = Dependency_Pair_Problem_Spec.rules i dpp;
    s = fst st;
    ta = snd st;
    tp = Term_More.subt_at ta p;
    u = (case u_opt of {
          Nothing ->
            concatMap
              (\ tb ->
                Innermost_Usable_Rules_Impl.inn_usable_rules_pair i dpp (s, tb))
              ts;
          Just u -> u;
        });
  } in Error_Monad.bind
         (Error_Monad.catch_error (Check_Monad.check_subseteq u r)
           (\ x ->
             Sum_Type.Inl
               (Trs_Impl.showsl_rule x .
                 Shows_Literal.showsl_lit
                   " is not a rule of the rewrite system ")))
         (\ _ ->
           let {
             urc = Innermost_Usable_Rules_Impl.is_ur_closed_impl_dpp_mv i dpp u;
             check_urc =
               (\ sa tb ->
                 Check_Monad.check (urc sa tb)
                   ((Shows_Literal.showsl_lit "term " .
                      Term_More.showsl_terma tb) .
                     Shows_Literal.showsl_lit
                       " is not closed under usable rules"));
             nfs = Dependency_Pair_Problem_Spec.nfs i dpp;
           } in Error_Monad.bind
                  (Error_Monad.catch_error
                    (Error_Monad.forallM
                      (\ (l, _) ->
                        Check_Monad.check (not (Term.is_Var l))
                          (Shows_Literal.showsl_lit
                            "lhss must not be variables"))
                      u)
                    (\ x -> Sum_Type.Inl (snd x)))
                  (\ _ ->
                    Error_Monad.bind
                      (Check_Monad.check (Trs.wf_rule lr)
                        (Trs_Impl.showsl_rule lr .
                          Shows_Literal.showsl_lit
                            " is not a well formed rule"))
                      (\ _ ->
                        Error_Monad.bind
                          (if nfs && sound then Sum_Type.Inr ()
                            else Error_Monad.catch_error
                                   (Check_Monad.check_subseteq
                                     (Term_More.vars_term_list tp)
                                     (Term_More.vars_term_list s))
                                   (\ _ ->
                                     Sum_Type.Inl
                                       (Shows_Literal.showsl_lit
 "variable condition in pair violated")))
                          (\ _ ->
                            Error_Monad.bind
                              (Error_Monad.catch_error
                                (Error_Monad.forallM (check_urc ss) ts)
                                (\ x -> Sum_Type.Inl (snd x)))
                              (\ _ ->
                                Error_Monad.bind
                                  (Error_Monad.catch_error
                                    (Error_Monad.forallM
                                      (\ (l, a) -> check_urc (Term.args l) a) u)
                                    (\ x -> Sum_Type.Inl (snd x)))
                                  (\ _ ->
                                    Error_Monad.bind
                                      (Error_Monad.catch_error
(Critical_Pairs_Impl.check_critical_pairs_innermost
  Renaming2_String.string_rename u)
(\ x ->
  Sum_Type.Inl
    (Shows_Literal.showsl_lit "problem in showing UNF of usable rules\n" . x)))
                                      (\ _ ->
Error_Monad.catch_error
  (Error_Monad.forallM
    (\ (_, (sa, tb)) ->
      Check_Monad.check (Term.equal_term sa tb)
        (Shows_Literal.showsl_lit
          "non-trivial critical pair between rule to rewrite and usable rules"))
    (Critical_Pairs_Impl.critical_pairs_impl Renaming2_String.string_rename [lr]
      u))
  (\ x -> Sum_Type.Inl (snd x)))))))));

rewriting_proc ::
  forall a b.
    (Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b
                                  [Str.Char] () ->
                                  Maybe [(Term.Term b [Str.Char],
   Term.Term b [Str.Char])] ->
                                    (Term.Term b [Str.Char],
                                      Term.Term b [Str.Char]) ->
                                      (Term.Term b [Str.Char],
Term.Term b [Str.Char]) ->
(Term.Term b [Str.Char], Term.Term b [Str.Char]) ->
  (Term.Term b [Str.Char], Term.Term b [Str.Char]) ->
    [Arith.Nat] -> a -> Sum_Type.Sum (String -> String) a;
rewriting_proc i u stb sta st lr p dpp =
  (case let {
          s = fst stb;
          t = snd sta;
        } in Error_Monad.bind
               (Q_Restricted_Rewriting_Impl.check_rstep
                 (Dependency_Pair_Problem_Spec.rules i dpp) p lr (snd stb) t)
               (\ _ ->
                 Error_Monad.bind
                   (Check_Monad.check
                     (Dependency_Pair_Problem_Spec.nFQ_subset_NF_rules i dpp)
                     (Shows_Literal.showsl_lit "innermost rewriting required"))
                   (\ _ ->
                     Error_Monad.bind
                       (check_rewrite_common_preconditions i u stb [s]
                         [Term_More.subt_at (snd stb) p] t lr p True dpp)
                       (\ _ ->
                         Error_Monad.bind
                           (Check_Monad.check (Trs.eq_rule_mod_vars sta st)
                             (((Shows_Literal.showsl_lit "the rule " .
                                 Trs_Impl.showsl_rule sta) .
                                Shows_Literal.showsl_lit
                                  " is not a renamed variant of ") .
                               Trs_Impl.showsl_rule st))
                           (\ _ ->
                             Error_Monad.bind
                               (Check_Monad.check (Term.equal_term s (fst sta))
                                 (Shows_Literal.showsl_lit
                                   "left-hand sides of old and new pair differ"))
                               (\ _ ->
                                 Error_Monad.bind
                                   (Check_Monad.check
                                     (List.member
(Dependency_Pair_Problem_Spec.p i dpp) stb ||
                                       null
 (Dependency_Pair_Problem_Spec.r i dpp))
                                     (Shows_Literal.showsl_lit
                                       "strict DP or no strict rules required"))
                                   (\ _ ->
                                     Check_Monad.check
                                       (Dependency_Pair_Problem_Spec.nfs i
  dpp ||
 Dependency_Pair_Problem_Spec.wwf_rules i dpp)
                                       (Shows_Literal.showsl_lit
 "well-formed rules or normal subst. required")))))))
    of {
    Sum_Type.Inl a -> Sum_Type.Inl a;
    Sum_Type.Inr _ ->
      Sum_Type.Inr (Dependency_Pair_Problem_Spec.replace_pair i dpp stb [st]);
  });

rewriting_complete_proc ::
  forall a b.
    (Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b
                                  [Str.Char] () ->
                                  Rewriting_complete_proc_prf b [Str.Char] ->
                                    a -> Sum_Type.Sum (String -> String) a;
rewriting_complete_proc i prf dpp =
  (case prf of {
    Rewriting_complete_proc_prf u_opt st sta stb lr p ->
      (case Error_Monad.catch_error
              (let {
                 s = fst st;
                 t = snd st;
                 ta = snd sta;
                 r = Dependency_Pair_Problem_Spec.rules i dpp;
               } in Error_Monad.bind
                      (Q_Restricted_Rewriting_Impl.check_rstep r p lr t ta)
                      (\ _ ->
                        Error_Monad.bind
                          (Check_Monad.check
                            (Dependency_Pair_Problem_Spec.nFQ_subset_NF_rules i
                              dpp)
                            (Shows_Literal.showsl_lit
                              "innermost rewriting required"))
                          (\ _ ->
                            Error_Monad.bind
                              (check_rewrite_common_preconditions i u_opt st
                                (Term.args s)
                                (Term.args (Term_More.subt_at t p)) ta lr p
                                False dpp)
                              (\ _ ->
                                Error_Monad.bind
                                  (Check_Monad.check (not (Term.is_Var s))
                                    (Shows_Literal.showsl_lit
                                      "lhs of pair must not be variable"))
                                  (\ _ ->
                                    Error_Monad.bind
                                      (Check_Monad.check
(Trs.eq_rule_mod_vars sta stb)
(((Shows_Literal.showsl_lit "the rule " . Trs_Impl.showsl_rule sta) .
   Shows_Literal.showsl_lit " is not a renamed variant of ") .
  Trs_Impl.showsl_rule stb))
                                      (\ _ ->
Error_Monad.bind
  (Check_Monad.check (Term.equal_term s (fst sta))
    (Shows_Literal.showsl_lit "left-hand sides of old and new pair differ"))
  (\ _ ->
    let {
      q = Dependency_Pair_Problem_Spec.q i dpp;
      inn = Error_Monad.isOK
              (Q_Restricted_Rewriting_Impl.check_NF_trs_subset r q);
    } in Error_Monad.bind
           (check_nfc inn r q (Dependency_Pair_Problem_Spec.is_QNF i dpp)
             (Term.args s) (Dependency_Pair_Problem_Spec.nfs i dpp)
             (Term_More.subt_at t p))
           (\ _ ->
             Error_Monad.bind
               (Error_Monad.catch_error
                 (Error_Monad.forallM
                   (\ (l, _) ->
                     Check_Monad.check (not (Term.is_Var l))
                       (Shows_Literal.showsl_lit "lhss must not be variables"))
                   r)
                 (\ x -> Sum_Type.Inl (snd x)))
               (\ _ ->
                 (if not (Term.is_Var t)
                   then Check_Monad.check
                          (not (not (null (Dependency_Pair_Problem_Spec.rules_map
    i dpp (Option.the (Term.root t))))))
                          ((Shows_Literal.showsl_lit "root of " .
                             Term_More.showsl_terma t) .
                            Shows_Literal.showsl_lit " must not be defined")
                   else Sum_Type.Inr ()))))))))))
              (\ x ->
                Sum_Type.Inl
                  (((((Shows_Literal.showsl_lit
                         "error when rewriting the pair\n" .
                        Trs_Impl.showsl_rule st) .
                       Shows_Literal.showsl_lit "\n to the pair\n") .
                      Trs_Impl.showsl_rule stb) .
                     Shows_Literal.showsl_literal "\n") .
                    x))
        of {
        Sum_Type.Inl a -> Sum_Type.Inl a;
        Sum_Type.Inr _ ->
          Sum_Type.Inr
            (Dependency_Pair_Problem_Spec.replace_pair i dpp st [stb]);
      });
  });

}
