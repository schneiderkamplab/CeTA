{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Narrowing_Impl(Narrowing_complete_proc_prf(..), narrowing_proc,
                  narrowing_complete_proc)
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
import qualified List_Lexorder;
import qualified Matching;
import qualified Dependency_Graph_Impl;
import qualified Icap_Impl;
import qualified Option;
import qualified Trs_Impl;
import qualified Check_Monad;
import qualified Trs;
import qualified List;
import qualified Mapping_Impl;
import qualified Collection_Order;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Q_Restricted_Rewriting_Impl;
import qualified Unification_String;
import qualified Option_Util;
import qualified Term_Impl;
import qualified HOL;
import qualified Subterm_and_Context;
import qualified Product_Type;
import qualified Rewriting_Impl;
import qualified Term_More;
import qualified Error_Monad;
import qualified Dependency_Pair_Problem_Spec;
import qualified Sum_Type;
import qualified Str;
import qualified Compare;
import qualified Shows_Literal;
import qualified Term;
import qualified Arith;

data Narrowing_complete_proc_prf a b =
  Narrowing_complete_proc_prf (Term.Term a b, Term.Term a b) [Arith.Nat]
    [(Term.Term a b, Term.Term a b)];

check_narrow ::
  forall a b.
    (Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => Bool ->
                                  Dependency_Pair_Problem_Spec.Dpp_ops_ext a b
                                    [Str.Char] () ->
                                    a -> [(Term.Term b [Str.Char],
    Term.Term b [Str.Char])] ->
   [Term.Term b [Str.Char]] ->
     Bool ->
       (Term.Term b [Str.Char], Term.Term b [Str.Char]) ->
         (Term.Term b [Str.Char], Term.Term b [Str.Char]) ->
           ([Str.Char] -> Term.Term b [Str.Char],
             ((Term.Term b [Str.Char], Term.Term b [Str.Char]),
               ([Arith.Nat], [Str.Char] -> Term.Term b [Str.Char]))) ->
             Sum_Type.Sum (String -> String) ();
check_narrow inn i dpp r q nfs sta st quad =
  (case (sta, (st, quad)) of {
    ((_, t), ((s, ta), (mu, (lr, (p, _))))) ->
      Error_Monad.bind
        (Rewriting_Impl.check_nfc inn r q
          (Dependency_Pair_Problem_Spec.is_QNF i dpp) (Term.args s) nfs
          (Term_More.subt_at (Term.eval_term Term.Fun t mu) p))
        (\ _ ->
          Rewriting_Impl.check_rewrite_common_preconditions i Nothing
            (s, Term.eval_term Term.Fun t mu) (Term.args s)
            (Term.args (Term_More.subt_at (Term.eval_term Term.Fun t mu) p)) ta
            lr p False dpp);
  });

qnarrows_impl ::
  forall a.
    (Eq a) => (Term.Term a [Str.Char] -> Bool) ->
                Bool ->
                  [(Term.Term a [Str.Char], Term.Term a [Str.Char])] ->
                    Term.Term a [Str.Char] ->
                      [(Term.Term a [Str.Char],
                         [Str.Char] -> Term.Term a [Str.Char])];
qnarrows_impl isnf nfs r t =
  concatMap
    (\ p ->
      let {
        tp = Term_More.subt_at t p;
      } in (if not (Term.is_Var tp)
             then concatMap
                    (\ (l, ra) ->
                      concatMap
                        (\ (mu_1, mu_2) ->
                          (if Q_Restricted_Rewriting_Impl.nF_subst_impl isnf nfs
                                (l, ra) mu_2
                            then (if all isnf
                                       (Term.args
 (Term.eval_term Term.Fun l mu_2))
                                   then [(Subterm_and_Context.intp_actxt
    Term.Fun (Term_More.ctxt_of_pos_term p (Term.eval_term Term.Fun t mu_1))
    (Term.eval_term Term.Fun ra mu_2),
   mu_1)]
                                   else [])
                            else []))
                        (Option_Util.option_to_list
                          (Unification_String.mgu_vd_string tp l)))
                    r
             else []))
    (Term_Impl.poss_list t);

narrowing_proc ::
  forall a b.
    (Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b
                                  [Str.Char] () ->
                                  (Term.Term b [Str.Char],
                                    Term.Term b [Str.Char]) ->
                                    [Arith.Nat] ->
                                      [(Term.Term b [Str.Char],
 Term.Term b [Str.Char])] ->
a -> Sum_Type.Sum (String -> String) a;
narrowing_proc i st p sts dpp =
  (case (case st of {
          (s, t) ->
            let {
              q = Dependency_Pair_Problem_Spec.q i dpp;
            } in Error_Monad.bind
                   (Check_Monad.check
                     (Dependency_Pair_Problem_Spec.nFQ_subset_NF_rules i dpp ||
                       null q && Term_More.linear_term t)
                     (Shows_Literal.showsl_lit
                       "innermost or full rewriting required (and linearity of t in full rewriting case)"))
                   (\ _ ->
                     let {
                       ic = Icap_Impl.icap_impl_dpp_mv i dpp;
                       isnf = Dependency_Pair_Problem_Spec.is_QNF i dpp;
                       pairs = Dependency_Pair_Problem_Spec.pairs i dpp;
                     } in Error_Monad.bind
                            (Check_Monad.check
                              (List.member (Term_Impl.poss_list t) p)
                              (Shows_Literal.showsl_lit
                                 "position not contained in " .
                                Term_More.showsl_terma t))
                            (\ _ ->
                              let {
                                tp = Term_More.subt_at t p;
                                nftp = isnf tp;
                              } in Error_Monad.bind
                                     (Check_Monad.check
                                       (List.member
  (Term_Impl.poss_list (ic [s] t)) p ||
 not nftp)
                                       (Shows_Literal.showsl_lit
 "neither is position contained in capped term of t, nor is t|_p not in Q-normal form"))
                                     (\ _ ->
                                       let {
 nfs = Dependency_Pair_Problem_Spec.nfs i dpp;
 narrows = qnarrows_impl isnf nfs (Dependency_Pair_Problem_Spec.rules i dpp) tp;
 stsa =
   filter (\ (smu, _) -> isnf smu)
     (map (\ (ta, mu) ->
            (Term.eval_term Term.Fun s mu,
              Subterm_and_Context.intp_actxt Term.Fun
                (Term_More.ctxt_of_pos_term p (Term.eval_term Term.Fun t mu))
                ta))
       narrows);
                                       } in
 Error_Monad.bind
   (Error_Monad.catch_error
     (Error_Monad.forallM
       (\ new ->
         Check_Monad.check
           (any (\ sta ->
                  Trs.instance_rule new sta &&
                    (not nfs || (null q || Trs.wf_rule sta)))
             sts)
           (Shows_Literal.showsl_lit "could not find narrowed pair " .
             Trs_Impl.showsl_rule new))
       stsa)
     (\ x -> Sum_Type.Inl (snd x)))
   (\ _ ->
     let {
       iedg = Dependency_Graph_Impl.is_iedg_edge_dpp i dpp (s, t);
     } in Error_Monad.bind
            (Error_Monad.catch_error
              (Check_Monad.check_subseteq (Term_More.vars_term_list tp)
                (Term_More.vars_term_list s))
              (\ x ->
                Sum_Type.Inl
                  ((Shows_Literal.showsl_lit "variable " .
                     Shows_Literal.showsl_lista x) .
                    Shows_Literal.showsl_lit " only occurs on rhs of pair")))
            (\ _ ->
              Error_Monad.bind
                (Check_Monad.check
                  (List.member (Dependency_Pair_Problem_Spec.p i dpp) st ||
                    null (Dependency_Pair_Problem_Spec.r i dpp))
                  (Shows_Literal.showsl_lit
                    "strict DP or no strict rules required"))
                (\ _ ->
                  (if nftp
                    then Error_Monad.catch_error
                           (Error_Monad.forallM
                             (\ (u, v) ->
                               Error_Monad.bind
                                 (Check_Monad.check
                                   (List.member (Term_Impl.poss_list u) p)
                                   (Shows_Literal.showsl_lit
                                      "position not contained in lhs of pair " .
                                     Trs_Impl.showsl_rule (u, v)))
                                 (\ _ ->
                                   (case Unification_String.mgu_vd_string tp
   (Term_More.subt_at u p)
                                     of {
                                     Nothing -> Sum_Type.Inr ();
                                     Just (mu_1, mu_2) ->
                                       Check_Monad.check
 (not (isnf (Term.eval_term Term.Fun s mu_1)) ||
   not (isnf (Term.eval_term Term.Fun u mu_2)))
 (Shows_Literal.showsl_lit
    "t |_ p and u |_ p unify and satisfy variable condition for pair (u,v) = " .
   Trs_Impl.showsl_rule (u, v));
                                   })))
                             (filter (\ (u, _) -> iedg u) pairs))
                           (\ x -> Sum_Type.Inl (snd x))
                    else Sum_Type.Inr ())))))));
        })
    of {
    Sum_Type.Inl a -> Sum_Type.Inl a;
    Sum_Type.Inr _ ->
      Sum_Type.Inr (Dependency_Pair_Problem_Spec.replace_pair i dpp st sts);
  });

rstep_enum_impl ::
  forall a b.
    (Eq a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b) => [(Term.Term a b, Term.Term a b)] ->
Term.Term a b ->
  Term.Term a b ->
    [Arith.Nat] ->
      [((Term.Term a b, Term.Term a b), (b -> Term.Term a b, [Arith.Nat]))];
rstep_enum_impl r ta t p =
  concat
    (List.map_filter
      (\ x ->
        (if List_Lexorder.less_eq_list p x
          then Just (let {
                       tp = Term_More.subt_at ta x;
                     } in (if List.member (Term_Impl.poss_list t) x
                            then (if Subterm_and_Context.equal_actxt
                                       (Term_More.ctxt_of_pos_term x ta)
                                       (Term_More.ctxt_of_pos_term x t)
                                   then concatMap
  (\ tpa ->
    concatMap
      (\ (l, ra) ->
        map (\ mu -> ((l, ra), (mu, x)))
          (Option_Util.option_to_list
            (Matching.match_list Term.Var [(l, tp), (ra, tpa)])))
      r)
  [Term_More.subt_at t x]
                                   else [])
                            else []))
          else Nothing))
      (Term_Impl.poss_list ta));

narrow_enum_impl ::
  forall a b.
    (Eq a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b) => [(Term.Term a b, Term.Term a b)] ->
(Term.Term a b, Term.Term a b) ->
  (Term.Term a b, Term.Term a b) ->
    [Arith.Nat] ->
      [(b -> Term.Term a b,
         ((Term.Term a b, Term.Term a b), ([Arith.Nat], b -> Term.Term a b)))];
narrow_enum_impl r sta st p =
  (case sta of {
    (s, t) ->
      (case st of {
        (sa, ta) ->
          concatMap
            (\ mu ->
              map (\ (lr, (tau, q)) -> (mu, (lr, (q, tau))))
                (rstep_enum_impl r (Term.eval_term Term.Fun t mu) ta p))
            (Option_Util.option_to_list (Matching.match sa s));
      });
  });

narrowing_complete_proc ::
  forall a b.
    (Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b
                                  [Str.Char] () ->
                                  Narrowing_complete_proc_prf b [Str.Char] ->
                                    a -> Sum_Type.Sum (String -> String) a;
narrowing_complete_proc i (Narrowing_complete_proc_prf st p sts) dpp =
  (case Error_Monad.catch_error
          (case st of {
            (s, t) ->
              let {
                q = Dependency_Pair_Problem_Spec.q i dpp;
                nfs = Dependency_Pair_Problem_Spec.nfs i dpp;
                rules = Dependency_Pair_Problem_Spec.rules i dpp;
                check_ndef =
                  Q_Restricted_Rewriting_Impl.check_no_defined_root
                    (\ fn ->
                      not (null (Dependency_Pair_Problem_Spec.rules_map i dpp
                                  fn)));
                inn = Error_Monad.isOK
                        (Q_Restricted_Rewriting_Impl.check_NF_trs_subset rules
                          q);
                cnarrow = check_narrow inn i dpp rules q nfs st;
              } in Error_Monad.bind
                     (Check_Monad.check
                       (null q ||
                         Dependency_Pair_Problem_Spec.nFQ_subset_NF_rules i dpp)
                       (Shows_Literal.showsl_lit
                         "full or innermost rewriting required"))
                     (\ _ ->
                       Error_Monad.bind
                         (if null q then Sum_Type.Inr ()
                           else Error_Monad.bind (Term_Impl.check_no_var s)
                                  (\ _ ->
                                    Error_Monad.bind (Term_Impl.check_no_var t)
                                      (\ _ ->
Error_Monad.bind (check_ndef t)
  (\ _ ->
    (if nfs
      then Error_Monad.bind
             (Error_Monad.catch_error
               (Error_Monad.forallM (\ (l, _) -> Term_Impl.check_no_var l)
                 rules)
               (\ x -> Sum_Type.Inl (snd x)))
             (\ _ ->
               Check_Monad.check (Trs.wf_rule (s, t))
                 (Trs_Impl.showsl_rule (s, t) .
                   Shows_Literal.showsl_lit " is not well formed"))
      else Sum_Type.Inr ())))))
                         (\ _ ->
                           Error_Monad.catch_error
                             (Error_Monad.forallM
                               (\ sta ->
                                 let {
                                   quads = narrow_enum_impl rules st sta p;
                                 } in Error_Monad.catch_error
(Error_Monad.existsM
  (\ quad ->
    Error_Monad.catch_error
      (Check_Monad.check (null q) (Shows_Literal.showsl_lit "q not empty"))
      (\ _ -> cnarrow sta quad))
  quads)
(\ x ->
  Sum_Type.Inl
    ((Trs_Impl.showsl_rule sta .
       Shows_Literal.showsl_lit
         (case quads of {
           [] -> " does not seem to be narrowed pair";
           _ : _ -> " violates side conditions for completeness";
         })) .
      Shows_Literal.showsl_list_gen id "" "" "" "" x)))
                               sts)
                             (\ x -> Sum_Type.Inl (snd x))));
          })
          (\ x ->
            Sum_Type.Inl
              (((((Shows_Literal.showsl_lit "error when narrowing\n" .
                    Trs_Impl.showsl_rule st) .
                   Shows_Literal.showsl_lit "\n to the pairs\n") .
                  Trs_Impl.showsl_trs sts) .
                 Shows_Literal.showsl_literal "\n") .
                x))
    of {
    Sum_Type.Inl a -> Sum_Type.Inl a;
    Sum_Type.Inr _ ->
      Sum_Type.Inr (Dependency_Pair_Problem_Spec.replace_pair i dpp st sts);
  });

}
