{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Nonloop_Impl(Pat_eqv_prf(..), Pat_rule_pos(..), Pat_rule_prf(..),
                Non_loop_prf(..), check_non_loop_dp_prf, check_non_loop_trs_prf)
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
import qualified Termination_Problem_Spec;
import qualified Dependency_Pair_Problem_Spec;
import qualified Q_Restricted_Rewriting_Impl;
import qualified Mapping;
import qualified Innermost_Loops_Impl;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified HOL;
import qualified Sum_Type;
import qualified Compare;
import qualified Arith;
import qualified Term_Rewriting;

data Pat_eqv_prf a b = Pat_Dom_Renaming [(b, Term_Rewriting.Term a b)]
  | Pat_Irrelevant [(b, Term_Rewriting.Term a b)] [(b, Term_Rewriting.Term a b)]
  | Pat_Simplify [(b, Term_Rewriting.Term a b)] [(b, Term_Rewriting.Term a b)];

data Pat_rule_pos = Pat_Base | Pat_Pump | Pat_Close;

data Pat_rule_prf a b =
  Pat_OrigRule (Term_Rewriting.Term a b, Term_Rewriting.Term a b) Bool
  | Pat_InitPump (Pat_rule_prf a b) [(b, Term_Rewriting.Term a b)]
      [(b, Term_Rewriting.Term a b)]
  | Pat_InitPumpCtxt (Pat_rule_prf a b) [(b, Term_Rewriting.Term a b)]
      [Arith.Nat] b
  | Pat_Equiv (Pat_rule_prf a b) Bool (Pat_eqv_prf a b)
  | Pat_Narrow (Pat_rule_prf a b) (Pat_rule_prf a b) [Arith.Nat]
  | Pat_Inst (Pat_rule_prf a b) [(b, Term_Rewriting.Term a b)] Pat_rule_pos
  | Pat_Rewr (Pat_rule_prf a b)
      (Term_Rewriting.Term a b,
        [([Arith.Nat],
           ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
             Term_Rewriting.Term a b))])
      Pat_rule_pos b
  | Pat_Exp_Sigma (Pat_rule_prf a b) Arith.Nat;

data Non_loop_prf a b =
  Non_loop_prf (Pat_rule_prf a b) [(b, Term_Rewriting.Term a b)]
    [(b, Term_Rewriting.Term a b)] Arith.Nat Arith.Nat [Arith.Nat];

pat_dv_impl ::
  forall a b.
    (Eq a,
      Eq b) => (Term_Rewriting.Term a b,
                 ([(b, Term_Rewriting.Term a b)],
                   [(b, Term_Rewriting.Term a b)])) ->
                 [b];
pat_dv_impl p =
  (case p of {
    (_, (sigma, mu)) ->
      Arith.remdups
        (map fst
          (Term_Rewriting.mk_subst_domain sigma ++
            Term_Rewriting.mk_subst_domain mu));
  });

showsl_pat_term ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Eq b,
      Term_Rewriting.Showl b) => (Term_Rewriting.Term a b,
                                   ([(b, Term_Rewriting.Term a b)],
                                     [(b, Term_Rewriting.Term a b)])) ->
                                   String -> String;
showsl_pat_term p =
  (case p of {
    (s, (sigma, tau)) ->
      Term_Rewriting.showsl_prod
        (s, (Term_Rewriting.mk_subst_domain sigma,
              Term_Rewriting.mk_subst_domain tau));
  });

showsl_pat_rule ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Eq b,
      Term_Rewriting.Showl b) => ((Term_Rewriting.Term a b,
                                    ([(b, Term_Rewriting.Term a b)],
                                      [(b, Term_Rewriting.Term a b)])),
                                   ((Term_Rewriting.Term a b,
                                      ([(b, Term_Rewriting.Term a b)],
[(b, Term_Rewriting.Term a b)])),
                                     Bool)) ->
                                   String -> String;
showsl_pat_rule pr =
  (case pr of {
    (p1, (p2, _)) ->
      (showsl_pat_term p1 . Term_Rewriting.showsl_lit " --> ") .
        showsl_pat_term p2;
  });

vars_pat_term_impl ::
  forall a b.
    (Eq a,
      Eq b) => (Term_Rewriting.Term a b,
                 ([(b, Term_Rewriting.Term a b)],
                   [(b, Term_Rewriting.Term a b)])) ->
                 [b];
vars_pat_term_impl p =
  (case p of {
    (s, (sigma, mu)) ->
      Arith.remdups
        (Term_Rewriting.vars_term_list s ++
          Term_Rewriting.vars_subst_impl sigma ++
            Term_Rewriting.vars_subst_impl mu);
  });

pat_dom_renaming_impl ::
  forall a b.
    (Eq a,
      Eq b) => (Term_Rewriting.Term a b,
                 ([(b, Term_Rewriting.Term a b)],
                   [(b, Term_Rewriting.Term a b)])) ->
                 [(b, Term_Rewriting.Term a b)] -> Bool;
pat_dom_renaming_impl p rho =
  let {
    rhoa = Term_Rewriting.mk_subst_domain rho;
    xs = map Term_Rewriting.Var (vars_pat_term_impl p);
  } in Term_Rewriting.is_renaming_impl rho &&
         Arith.superset (pat_dv_impl p) (map fst rhoa) &&
           all (\ t -> not (Arith.membera xs t)) (map snd rhoa);

check_pat_eqv_prf ::
  forall a b.
    (Compare.Compare a, Eq a, Term_Rewriting.Showl a, Arith.Cenum b,
      Arith.Ceq b, Arith.Ccompare b, Compare.Compare b, Eq b, Arith.Set_impl b,
      Term_Rewriting.Showl b) => Pat_eqv_prf a b ->
                                   (Term_Rewriting.Term a b,
                                     ([(b, Term_Rewriting.Term a b)],
                                       [(b, Term_Rewriting.Term a b)])) ->
                                     Sum_Type.Sum (String -> String)
                                       (Term_Rewriting.Term a b,
 ([(b, Term_Rewriting.Term a b)], [(b, Term_Rewriting.Term a b)]));
check_pat_eqv_prf (Pat_Irrelevant sigmaa mua) (t, (sigma, mu)) =
  let {
    w = Innermost_Loops_Impl.w_impl (Term_Rewriting.mk_subst_domain sigma) t;
    sig = Term_Rewriting.mk_subst Term_Rewriting.Var sigma;
    siga = Term_Rewriting.mk_subst Term_Rewriting.Var sigmaa;
    mub = Term_Rewriting.mk_subst Term_Rewriting.Var mu;
    muba = Term_Rewriting.mk_subst Term_Rewriting.Var mua;
  } in Error_Monad.bind
         (Error_Monad.catch_error
           (Error_Monad.catch_error
             (Error_Monad.forallM
               (\ x ->
                 Error_Monad.bind
                   (Check_Monad.check
                     (Term_Rewriting.equal_term (sig x) (siga x))
                     (x, (sig x,
                           (siga x,
                             [Arith.char_0x70, Arith.char_0x75, Arith.char_0x6D,
                               Arith.char_0x70, Arith.char_0x69,
                               Arith.char_0x6E, Arith.char_0x67]))))
                   (\ _ ->
                     Check_Monad.check
                       (Term_Rewriting.equal_term (mub x) (muba x))
                       (x, (mub x,
                             (muba x,
                               [Arith.char_0x63, Arith.char_0x6C,
                                 Arith.char_0x6F, Arith.char_0x73,
                                 Arith.char_0x69, Arith.char_0x6E,
                                 Arith.char_0x67])))))
               w)
             (\ x -> Sum_Type.Inl (snd x)))
           (\ x ->
             Sum_Type.Inl
               (case x of {
                 (xa, (tb, (ta, sub))) ->
                   ((((((Term_Rewriting.showsl_lit
                           "error in equivalence (irrelevant): for variable " .
                          Term_Rewriting.showsl xa) .
                         Term_Rewriting.showsl_lit
                           " obtain different values for ") .
                        Term_Rewriting.showsl_lista sub) .
                       Term_Rewriting.showsl_lit " substitution: ") .
                      Term_Rewriting.showsl_terma tb) .
                     Term_Rewriting.showsl_lit " != ") .
                     Term_Rewriting.showsl_terma ta;
               })))
         (\ _ -> Sum_Type.Inr (t, (sigmaa, mua)));
check_pat_eqv_prf (Pat_Simplify mu_1 mu_2) (t, (sigma, mu)) =
  Error_Monad.bind
    (Check_Monad.check
      (Term_Rewriting.subst_eq mu (Term_Rewriting.subst_compose_impl mu_1 mu_2))
      (Term_Rewriting.showsl_lit "mu != mu1 mu2"))
    (\ _ ->
      Error_Monad.bind
        (Check_Monad.check (Term_Rewriting.commutes_impl mu_1 sigma)
          (Term_Rewriting.showsl_lit "sigma and mu1 do not commute"))
        (\ _ ->
          Sum_Type.Inr
            (Term_Rewriting.eval_term Term_Rewriting.Fun t
               (Term_Rewriting.mk_subst Term_Rewriting.Var mu_1),
              (sigma, mu_2))));
check_pat_eqv_prf (Pat_Dom_Renaming rho) (t, (sigma, mu)) =
  Error_Monad.bind
    (Check_Monad.check (pat_dom_renaming_impl (t, (sigma, mu)) rho)
      (Term_Rewriting.showsl_lit "rho is not a domain renaming for p"))
    (\ _ ->
      let {
        i_rho = Term_Rewriting.is_inverse_renaming_impl rho;
        sigmaa =
          Term_Rewriting.mk_subst_case
            (map (Term_Rewriting.the_Var .
                   Term_Rewriting.mk_subst Term_Rewriting.Var rho)
              (map fst (Term_Rewriting.mk_subst_domain sigma)))
            (\ x ->
              Term_Rewriting.eval_term Term_Rewriting.Fun
                (Term_Rewriting.eval_term Term_Rewriting.Fun
                  (Term_Rewriting.eval_term Term_Rewriting.Fun
                    (Term_Rewriting.Var x)
                    (Term_Rewriting.mk_subst Term_Rewriting.Var i_rho))
                  (Term_Rewriting.mk_subst Term_Rewriting.Var sigma))
                (Term_Rewriting.mk_subst Term_Rewriting.Var rho))
            [];
        mua = Term_Rewriting.mk_subst_case
                (map (Term_Rewriting.the_Var .
                       Term_Rewriting.mk_subst Term_Rewriting.Var rho)
                  (map fst (Term_Rewriting.mk_subst_domain mu)))
                (\ x ->
                  Term_Rewriting.eval_term Term_Rewriting.Fun
                    (Term_Rewriting.eval_term Term_Rewriting.Fun
                      (Term_Rewriting.Var x)
                      (Term_Rewriting.mk_subst Term_Rewriting.Var i_rho))
                    (Term_Rewriting.mk_subst Term_Rewriting.Var mu))
                i_rho;
      } in Sum_Type.Inr
             (Term_Rewriting.eval_term Term_Rewriting.Fun t
                (Term_Rewriting.mk_subst Term_Rewriting.Var rho),
               (sigmaa, mua)));

check_pat_rule_prf ::
  forall a b.
    (Compare.Compare a, Eq a, Term_Rewriting.Showl a, Arith.Cenum b,
      Arith.Ceq b, Arith.Ccompare b, Compare.Compare b, Eq b,
      Mapping.Mapping_impl b, Arith.Set_impl b,
      Term_Rewriting.Showl b) => [(Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b)] ->
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)] ->
                                     Pat_rule_prf a b ->
                                       Sum_Type.Sum (String -> String)
 ((Term_Rewriting.Term a b,
    ([(b, Term_Rewriting.Term a b)], [(b, Term_Rewriting.Term a b)])),
   ((Term_Rewriting.Term a b,
      ([(b, Term_Rewriting.Term a b)], [(b, Term_Rewriting.Term a b)])),
     Bool));
check_pat_rule_prf ra p (Pat_OrigRule (l, r) isPair) =
  (if isPair
    then Error_Monad.bind
           (Check_Monad.check (Arith.membera p (l, r))
             (Term_Rewriting.showsl_rule (l, r) .
               Term_Rewriting.showsl_lit " is not a pair"))
           (\ _ -> Sum_Type.Inr ((l, ([], [])), ((r, ([], [])), isPair)))
    else Error_Monad.bind
           (Check_Monad.check (Arith.membera ra (l, r))
             (Term_Rewriting.showsl_rule (l, r) .
               Term_Rewriting.showsl_lit " is not a rule"))
           (\ _ -> Sum_Type.Inr ((l, ([], [])), ((r, ([], [])), isPair))));
check_pat_rule_prf r p (Pat_InitPump pat sigma theta) =
  Error_Monad.bind (check_pat_rule_prf r p pat)
    (\ (a, b) ->
      (case a of {
        (s, (sig, tau)) ->
          (\ (aa, ba) ->
            (case aa of {
              (t, (siga, taua)) ->
                (\ bb ->
                  Error_Monad.catch_error
                    (Error_Monad.bind
                      (Check_Monad.check (null (sig ++ tau ++ siga ++ taua))
                        (Term_Rewriting.showsl_lit
                          "substitutions must be empty"))
                      (\ _ ->
                        Error_Monad.bind
                          (Check_Monad.check
                            (Term_Rewriting.equal_term
                              (Term_Rewriting.eval_term Term_Rewriting.Fun s
                                (Term_Rewriting.mk_subst Term_Rewriting.Var
                                  theta))
                              (Term_Rewriting.eval_term Term_Rewriting.Fun t
                                (Term_Rewriting.mk_subst Term_Rewriting.Var
                                  sigma)))
                            (Term_Rewriting.showsl_lit "s theta != t sigma"))
                          (\ _ ->
                            Error_Monad.bind
                              (Check_Monad.check
                                (Term_Rewriting.commutes_impl theta sigma)
                                (Term_Rewriting.showsl_lit
                                  "sigma and theta do not commute"))
                              (\ _ ->
                                Sum_Type.Inr
                                  ((s, (sigma, [])), ((t, (theta, [])), bb))))))
                    (\ x ->
                      Sum_Type.Inl
                        ((Term_Rewriting.showsl_lit
                            "problem with initial pumping after deriving correct pattern rule\n" .
                           showsl_pat_rule
                             ((s, (sig, tau)), ((t, (siga, taua)), bb))) .
                          x)));
            })
              ba);
      })
        b);
check_pat_rule_prf r pa (Pat_InitPumpCtxt pat sigma p z) =
  Error_Monad.bind (check_pat_rule_prf r pa pat)
    (\ (a, b) ->
      (case a of {
        (s, (sig, tau)) ->
          (\ (aa, ba) ->
            (case aa of {
              (t, (siga, taua)) ->
                (\ bb ->
                  Error_Monad.catch_error
                    (Error_Monad.bind
                      (Check_Monad.check (not bb)
                        (Term_Rewriting.showsl_lit
                          "pairs not allowed in init pump ctxt"))
                      (\ _ ->
                        Error_Monad.bind
                          (Check_Monad.check (null (sig ++ tau ++ siga ++ taua))
                            (Term_Rewriting.showsl_lit
                              "substitutions must be empty"))
                          (\ _ ->
                            Error_Monad.bind
                              (Check_Monad.check (Term_Rewriting.in_poss p t)
                                (Term_Rewriting.showsl_lit
                                  "p is not a valid position"))
                              (\ _ ->
                                Error_Monad.bind
                                  (Check_Monad.check
                                    (Term_Rewriting.equal_term s
                                      (Term_Rewriting.eval_term
Term_Rewriting.Fun (Term_Rewriting.subt_at t p)
(Term_Rewriting.mk_subst Term_Rewriting.Var sigma)))
                                    (Term_Rewriting.showsl_lit
                                      "s != t |_ p sigma"))
                                  (\ _ ->
                                    Error_Monad.bind
                                      (Check_Monad.check
(not (Arith.membera
       (Term_Rewriting.vars_term_list s ++
         Term_Rewriting.vars_term_list t ++
           Term_Rewriting.vars_subst_impl sigma)
       z))
(Term_Rewriting.showsl_lit "z is not fresh"))
                                      (\ _ ->
let {
  tz = Term_Rewriting.intp_actxt Term_Rewriting.Fun
         (Term_Rewriting.ctxt_of_pos_term p t) (Term_Rewriting.Var z);
} in Sum_Type.Inr
       ((s, (sigma, [])),
         ((tz, ((z, tz) : sigma, [(z, Term_Rewriting.subt_at t p)])), bb))))))))
                    (\ x ->
                      Sum_Type.Inl
                        ((Term_Rewriting.showsl_lit
                            "problem with initial pumping (with ctxt) after deriving correct pattern rule\n" .
                           showsl_pat_rule
                             ((s, (sig, tau)), ((t, (siga, taua)), bb))) .
                          x)));
            })
              ba);
      })
        b);
check_pat_rule_prf r p (Pat_Equiv pat left eqv) =
  Error_Monad.bind (check_pat_rule_prf r p pat)
    (\ (pleft, (pright, b)) ->
      Error_Monad.catch_error
        (Error_Monad.bind
          (check_pat_eqv_prf eqv (if left then pleft else pright))
          (\ pnew ->
            Sum_Type.Inr
              (if left then (pnew, (pright, b)) else (pleft, (pnew, b)))))
        (\ x ->
          Sum_Type.Inl
            ((Term_Rewriting.showsl_lit
                "problem with pattern equivalence after deriving correct pattern rule\n" .
               showsl_pat_rule (pleft, (pright, b))) .
              x)));
check_pat_rule_prf r pa (Pat_Narrow pat1 pat2 p) =
  Error_Monad.bind (check_pat_rule_prf r pa pat1)
    (\ (a, b) ->
      (case a of {
        (s, (sigma, mu)) ->
          (\ (aa, ba) ->
            (case aa of {
              (t, (sig, mua)) ->
                (\ b1 ->
                  Error_Monad.bind (check_pat_rule_prf r pa pat2)
                    (\ (ab, bb) ->
                      (case ab of {
                        (u, (sig1, mu1)) ->
                          (\ (ac, bc) ->
                            (case ac of {
                              (v, (sig2, mu2)) ->
                                (\ b2 ->
                                  Error_Monad.catch_error
                                    (Error_Monad.bind
                                      (Check_Monad.check
(Term_Rewriting.subst_eq sig sigma &&
  Term_Rewriting.subst_eq sig1 sigma &&
    Term_Rewriting.subst_eq sig2 sigma &&
      Term_Rewriting.subst_eq mua mu &&
        Term_Rewriting.subst_eq mu1 mu && Term_Rewriting.subst_eq mu2 mu)
(Term_Rewriting.showsl_lit "substitutions are not identical"))
                                      (\ _ ->
Error_Monad.bind
  (Check_Monad.check (Term_Rewriting.in_poss p t)
    (Term_Rewriting.showsl_lit "p is not a valid position"))
  (\ _ ->
    Error_Monad.bind
      (Check_Monad.check
        (Term_Rewriting.equal_term (Term_Rewriting.subt_at t p) u)
        (Term_Rewriting.showsl_lit "t |_ p != u"))
      (\ _ ->
        Error_Monad.bind
          (Check_Monad.check (if b2 then null p else True)
            (Term_Rewriting.showsl_lit
              "there is a P step, so p must be epsilon"))
          (\ _ ->
            Sum_Type.Inr
              ((s, (sigma, mu)),
                ((Term_Rewriting.intp_actxt Term_Rewriting.Fun
                    (Term_Rewriting.ctxt_of_pos_term p t) v,
                   (sigma, mu)),
                  b1 || b2)))))))
                                    (\ x ->
                                      Sum_Type.Inl
((((Term_Rewriting.showsl_lit
      "problem with pattern narrowing after deriving correct pattern rules\n" .
     showsl_pat_rule ((s, (sigma, mu)), ((t, (sig, mua)), b1))) .
    Term_Rewriting.showsl_lit "\nand\n") .
   showsl_pat_rule ((u, (sig1, mu1)), ((v, (sig2, mu2)), b2))) .
  x)));
                            })
                              bc);
                      })
                        bb));
            })
              ba);
      })
        b);
check_pat_rule_prf r p (Pat_Inst pat rho Pat_Base) =
  Error_Monad.bind (check_pat_rule_prf r p pat)
    (\ (a, b) ->
      (case a of {
        (s, (sigma_s, mu_s)) ->
          (\ (aa, ba) ->
            (case aa of {
              (t, (sigma_t, mu_t)) ->
                (\ bb ->
                  Error_Monad.catch_error
                    (let {
                       xs = map fst
                              (Term_Rewriting.mk_subst_domain sigma_s ++
                                Term_Rewriting.mk_subst_domain mu_s ++
                                  Term_Rewriting.mk_subst_domain sigma_t ++
                                    Term_Rewriting.mk_subst_domain mu_t);
                     } in Error_Monad.bind
                            (Error_Monad.catch_error
                              (Error_Monad.forallM
                                (\ x ->
                                  Check_Monad.check (not (Arith.membera xs x))
                                    (Term_Rewriting.showsl_lit
                                      "domains not disjoint"))
                                (Term_Rewriting.vars_subst_impl rho))
                              (\ x -> Sum_Type.Inl (snd x)))
                            (\ _ ->
                              let {
                                rhoa =
                                  Term_Rewriting.mk_subst Term_Rewriting.Var
                                    rho;
                              } in Sum_Type.Inr
                                     ((Term_Rewriting.eval_term
 Term_Rewriting.Fun s rhoa,
(Term_Rewriting.subst_compose_impla sigma_s rhoa,
  Term_Rewriting.subst_compose_impla mu_s rhoa)),
                                       ((Term_Rewriting.eval_term
   Term_Rewriting.Fun t rhoa,
  (Term_Rewriting.subst_compose_impla sigma_t rhoa,
    Term_Rewriting.subst_compose_impla mu_t rhoa)),
 bb))))
                    (\ x ->
                      Sum_Type.Inl
                        ((Term_Rewriting.showsl_lit
                            "problem with pattern instantiation (base) after deriving correct pattern rule\n" .
                           showsl_pat_rule
                             ((s, (sigma_s, mu_s)),
                               ((t, (sigma_t, mu_t)), bb))) .
                          x)));
            })
              ba);
      })
        b);
check_pat_rule_prf r p (Pat_Inst pat rho Pat_Pump) =
  Error_Monad.bind (check_pat_rule_prf r p pat)
    (\ (a, b) ->
      (case a of {
        (s, (sigma_s, mu_s)) ->
          (\ (aa, ba) ->
            (case aa of {
              (t, (sigma_t, mu_t)) ->
                (\ bb ->
                  Error_Monad.catch_error
                    (Error_Monad.bind
                      (Check_Monad.check
                        (Term_Rewriting.commutes_impl rho sigma_s)
                        (Term_Rewriting.showsl_lit
                          "rho does not commute with sigma_s"))
                      (\ _ ->
                        Error_Monad.bind
                          (Check_Monad.check
                            (Term_Rewriting.commutes_impl rho mu_s)
                            (Term_Rewriting.showsl_lit
                              "rho does not commute with mu_s"))
                          (\ _ ->
                            Error_Monad.bind
                              (Check_Monad.check
                                (Term_Rewriting.commutes_impl rho sigma_t)
                                (Term_Rewriting.showsl_lit
                                  "rho does not commute with sigma_t"))
                              (\ _ ->
                                Error_Monad.bind
                                  (Check_Monad.check
                                    (Term_Rewriting.commutes_impl rho mu_t)
                                    (Term_Rewriting.showsl_lit
                                      "rho does not commute with mu_t"))
                                  (\ _ ->
                                    Sum_Type.Inr
                                      ((s,
 (Term_Rewriting.subst_compose_impl sigma_s rho, mu_s)),
((t, (Term_Rewriting.subst_compose_impl sigma_t rho, mu_t)), bb)))))))
                    (\ x ->
                      Sum_Type.Inl
                        ((Term_Rewriting.showsl_lit
                            "problem with pattern instantiation (pumping) after deriving correct pattern rule\n" .
                           showsl_pat_rule
                             ((s, (sigma_s, mu_s)),
                               ((t, (sigma_t, mu_t)), bb))) .
                          x)));
            })
              ba);
      })
        b);
check_pat_rule_prf r p (Pat_Inst pat rho Pat_Close) =
  Error_Monad.bind (check_pat_rule_prf r p pat)
    (\ (a, b) ->
      (case a of {
        (s, (sigma_s, mu_s)) ->
          (\ (aa, ba) ->
            (case aa of {
              (t, (sigma_t, mu_t)) ->
                (\ bb ->
                  Sum_Type.Inr
                    ((s, (sigma_s, Term_Rewriting.subst_compose_impl mu_s rho)),
                      ((t, (sigma_t,
                             Term_Rewriting.subst_compose_impl mu_t rho)),
                        bb)));
            })
              ba);
      })
        b);
check_pat_rule_prf r p (Pat_Rewr pat rewr Pat_Base uu) =
  Error_Monad.bind (check_pat_rule_prf r p pat)
    (\ (a, b) ->
      (case a of {
        (s, (sigma_s, mu_s)) ->
          (\ (aa, ba) ->
            (case aa of {
              (t, (sigma_t, mu_t)) ->
                (\ bb ->
                  Error_Monad.catch_error
                    (case rewr of {
                      (ta, rseq) ->
                        let {
                          tb = Arith.last
                                 (ta : map (\ (_, (_, tb)) -> tb) rseq);
                        } in Error_Monad.bind
                               (Check_Monad.check
                                 (Term_Rewriting.equal_term t ta)
                                 (Term_Rewriting.showsl_lit
                                   "terms t do not match"))
                               (\ _ ->
                                 Error_Monad.bind
                                   (Q_Restricted_Rewriting_Impl.check_rsteps r
                                     rseq ta tb)
                                   (\ _ ->
                                     Sum_Type.Inr
                                       ((s, (sigma_s, mu_s)),
 ((tb, (sigma_t, mu_t)), bb))));
                    })
                    (\ x ->
                      Sum_Type.Inl
                        ((Term_Rewriting.showsl_lit
                            "problem with pattern rewriting (base) after deriving correct pattern rule\n" .
                           showsl_pat_rule
                             ((s, (sigma_s, mu_s)),
                               ((t, (sigma_t, mu_t)), bb))) .
                          x)));
            })
              ba);
      })
        b);
check_pat_rule_prf r p (Pat_Rewr pat rewr Pat_Pump x) =
  Error_Monad.bind (check_pat_rule_prf r p pat)
    (\ (a, b) ->
      (case a of {
        (s, (sigma_s, mu_s)) ->
          (\ (aa, ba) ->
            (case aa of {
              (t, (sigma_t, mu_t)) ->
                (\ bb ->
                  Error_Monad.catch_error
                    (case rewr of {
                      (ta, rseq) ->
                        let {
                          tb = Arith.last
                                 (ta : map (\ (_, (_, tb)) -> tb) rseq);
                        } in Error_Monad.bind
                               (Check_Monad.check
                                 (Term_Rewriting.equal_term
                                   (Term_Rewriting.mk_subst Term_Rewriting.Var
                                     sigma_t x)
                                   ta)
                                 (Term_Rewriting.showsl_lit
                                   "sigma_t x does not match starting term"))
                               (\ _ ->
                                 Error_Monad.bind
                                   (Q_Restricted_Rewriting_Impl.check_rsteps r
                                     rseq ta tb)
                                   (\ _ ->
                                     Sum_Type.Inr
                                       ((s, (sigma_s, mu_s)),
 ((t, (Term_Rewriting.subst_replace_impl sigma_t x tb, mu_t)), bb))));
                    })
                    (\ xa ->
                      Sum_Type.Inl
                        ((Term_Rewriting.showsl_lit
                            "problem with pattern rewriting (pumping) after deriving correct pattern rule\n" .
                           showsl_pat_rule
                             ((s, (sigma_s, mu_s)),
                               ((t, (sigma_t, mu_t)), bb))) .
                          xa)));
            })
              ba);
      })
        b);
check_pat_rule_prf r p (Pat_Rewr pat rewr Pat_Close x) =
  Error_Monad.bind (check_pat_rule_prf r p pat)
    (\ (a, b) ->
      (case a of {
        (s, (sigma_s, mu_s)) ->
          (\ (aa, ba) ->
            (case aa of {
              (t, (sigma_t, mu_t)) ->
                (\ bb ->
                  Error_Monad.catch_error
                    (case rewr of {
                      (ta, rseq) ->
                        let {
                          tb = Arith.last
                                 (ta : map (\ (_, (_, tb)) -> tb) rseq);
                        } in Error_Monad.bind
                               (Check_Monad.check
                                 (Term_Rewriting.equal_term
                                   (Term_Rewriting.mk_subst Term_Rewriting.Var
                                     mu_t x)
                                   ta)
                                 (Term_Rewriting.showsl_lit
                                   "sigma_t x does not match starting term"))
                               (\ _ ->
                                 Error_Monad.bind
                                   (Q_Restricted_Rewriting_Impl.check_rsteps r
                                     rseq ta tb)
                                   (\ _ ->
                                     Sum_Type.Inr
                                       ((s, (sigma_s, mu_s)),
 ((t, (sigma_t, Term_Rewriting.subst_replace_impl mu_t x tb)), bb))));
                    })
                    (\ xa ->
                      Sum_Type.Inl
                        ((Term_Rewriting.showsl_lit
                            "problem with pattern rewriting (closing) after deriving correct pattern rule\n" .
                           showsl_pat_rule
                             ((s, (sigma_s, mu_s)),
                               ((t, (sigma_t, mu_t)), bb))) .
                          xa)));
            })
              ba);
      })
        b);
check_pat_rule_prf r p (Pat_Exp_Sigma pat k) =
  Error_Monad.bind (check_pat_rule_prf r p pat)
    (\ (a, b) ->
      (case a of {
        (s, (sigma_s, mu_s)) ->
          (\ (aa, ba) ->
            (case aa of {
              (t, (sigma_t, mu_t)) ->
                (\ bb ->
                  Sum_Type.Inr
                    ((Term_Rewriting.eval_term Term_Rewriting.Fun s
                        (Term_Rewriting.mk_subst Term_Rewriting.Var
                          (Term_Rewriting.subst_power_impl sigma_s k)),
                       (sigma_s, mu_s)),
                      ((Term_Rewriting.eval_term Term_Rewriting.Fun t
                          (Term_Rewriting.mk_subst Term_Rewriting.Var
                            (Term_Rewriting.subst_power_impl sigma_t k)),
                         (sigma_t, mu_t)),
                        bb)));
            })
              ba);
      })
        b);

check_non_loop_prf ::
  forall a b.
    (Compare.Compare a, Eq a, Term_Rewriting.Showl a, Arith.Cenum b,
      Arith.Ceq b, Arith.Ccompare b, Compare.Compare b, Eq b,
      Mapping.Mapping_impl b, Arith.Set_impl b,
      Term_Rewriting.Showl b) => [(Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b)] ->
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)] ->
                                     Non_loop_prf a b ->
                                       Sum_Type.Sum (String -> String) ();
check_non_loop_prf r pa (Non_loop_prf pat sigma mu m b p) =
  Error_Monad.bind (check_pat_rule_prf r pa pat)
    (\ (a, c) ->
      (case a of {
        (s, (sigmaa, mua)) ->
          (\ (aa, ca) ->
            (case aa of {
              (t, (sigma_t, mu_t)) ->
                (\ is_pair ->
                  Error_Monad.catch_error
                    (Error_Monad.bind
                      (Check_Monad.check (if is_pair then null p else True)
                        (Term_Rewriting.showsl_lit
                          "p must be empty, since pairs are contained"))
                      (\ _ ->
                        Error_Monad.bind
                          (Check_Monad.check
                            (Term_Rewriting.commutes_impl sigmaa sigma)
                            (Term_Rewriting.showsl_lit
                              "sigma and sigma\' do not commute"))
                          (\ _ ->
                            Error_Monad.bind
                              (Check_Monad.check
                                (Term_Rewriting.commutes_impl mua sigma)
                                (Term_Rewriting.showsl_lit
                                  "mu and sigma\' do not commute"))
                              (\ _ ->
                                Error_Monad.bind
                                  (Check_Monad.check
                                    (Term_Rewriting.subst_eq sigma_t
                                      (Term_Rewriting.subst_compose_impl
(Term_Rewriting.subst_power_impl sigmaa m) sigma))
                                    (Term_Rewriting.showsl_lit
                                      "sigma_t != sigma^m sigma\' "))
                                  (\ _ ->
                                    Error_Monad.bind
                                      (Check_Monad.check
(Term_Rewriting.subst_eq mu_t (Term_Rewriting.subst_compose_impl mua mu))
(Term_Rewriting.showsl_lit "mu_t != mu mu\' "))
                                      (\ _ ->
Error_Monad.bind
  (Check_Monad.check (Term_Rewriting.in_poss p t)
    (Term_Rewriting.showsl_lit "p is not a position in t"))
  (\ _ ->
    Check_Monad.check
      (Term_Rewriting.equal_term
        (Term_Rewriting.eval_term Term_Rewriting.Fun s
          (Term_Rewriting.mk_subst Term_Rewriting.Var
            (Term_Rewriting.subst_power_impl sigmaa b)))
        (Term_Rewriting.subt_at t p))
      (Term_Rewriting.showsl_lit "s sigma^b != t |_ p"))))))))
                    (\ x ->
                      Sum_Type.Inl
                        ((Term_Rewriting.showsl_lit
                            "problem with application condition of non-loop theorem after deriving correct pattern rule\n" .
                           showsl_pat_rule
                             ((s, (sigmaa, mua)),
                               ((t, (sigma_t, mu_t)), is_pair))) .
                          x)));
            })
              ca);
      })
        c);

check_non_loop_dp_prf ::
  forall a b c d.
    (Compare.Compare b, Eq b, Term_Rewriting.Showl b, Arith.Cenum c,
      Arith.Ceq c, Arith.Ccompare c, Compare.Compare c, Eq c,
      Mapping.Mapping_impl c, Arith.Set_impl c,
      Term_Rewriting.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b c
                                   d ->
                                   a -> Non_loop_prf b c ->
  Sum_Type.Sum (String -> String) ();
check_non_loop_dp_prf i dpp prf =
  let {
    p = Dependency_Pair_Problem_Spec.pairs i dpp;
    r = Dependency_Pair_Problem_Spec.rules i dpp;
  } in Error_Monad.bind
         (Check_Monad.check (null (Dependency_Pair_Problem_Spec.q i dpp))
           (Term_Rewriting.showsl_lit "strategy for non-loops unsupported"))
         (\ _ -> check_non_loop_prf r p prf);

check_non_loop_trs_prf ::
  forall a b c d.
    (Compare.Compare b, Eq b, Term_Rewriting.Showl b, Arith.Cenum c,
      Arith.Ceq c, Arith.Ccompare c, Compare.Compare c, Eq c,
      Mapping.Mapping_impl c, Arith.Set_impl c,
      Term_Rewriting.Showl c) => Termination_Problem_Spec.Tp_ops_ext a b c d ->
                                   a -> Non_loop_prf b c ->
  Sum_Type.Sum (String -> String) ();
check_non_loop_trs_prf i tp prf =
  let {
    r = Termination_Problem_Spec.rules i tp;
  } in Error_Monad.bind
         (Check_Monad.check (null (Termination_Problem_Spec.q i tp))
           (Term_Rewriting.showsl_lit "strategy for non-loops unsupported"))
         (\ _ -> check_non_loop_prf r [] prf);

}
