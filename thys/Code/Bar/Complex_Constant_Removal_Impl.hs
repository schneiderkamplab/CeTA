{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Complex_Constant_Removal_Impl(Complex_constant_removal_prf(..),
                                 complex_constant_removal_proc)
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
import qualified Critical_Pairs_Impl;
import qualified Q_Restricted_Rewriting_Impl;
import qualified Dependency_Pair_Problem_Spec;
import qualified Renaming2;
import qualified Mapping;
import qualified Compare;
import qualified Fresh;
import qualified Map;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified HOL;
import qualified Sum_Type;
import qualified Arith;
import qualified Shows_Literal;
import qualified Term_Rewriting;

data Complex_constant_removal_prf a b =
  Complex_Constant_Removal_Proof (Term_Rewriting.Term a b)
    [((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
       (Term_Rewriting.Term a b, Term_Rewriting.Term a b))];

check_drop ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => a -> Term_Rewriting.Term b a ->
                                       ((b, Arith.Nat) -> b) ->
 ((Term_Rewriting.Term b a, Term_Rewriting.Term b a),
   (Term_Rewriting.Term b a, Term_Rewriting.Term b a)) ->
   Sum_Type.Sum (String -> String) ();
check_drop x c ren st_st =
  (case st_st of {
    ((s, t), (sa, ta)) ->
      (case s of {
        Term_Rewriting.Fun f ss ->
          (case t of {
            Term_Rewriting.Fun g ts ->
              Error_Monad.bind
                (Check_Monad.check
                  (Term_Rewriting.equal_term sa
                    (Term_Rewriting.Fun (ren (f, Arith.size_list ss))
                      (ss ++ [Term_Rewriting.Var x])))
                  (((Shows_Literal.showsl_lit "could not relate " .
                      Term_Rewriting.showsl_terma s) .
                     Shows_Literal.showsl_lit " with ") .
                    Term_Rewriting.showsl_terma sa))
                (\ _ ->
                  let {
                    tsa = Term_Rewriting.args ta;
                    tsaa =
                      Arith.take
                        (Arith.minus_nat (Arith.size_list tsa) Arith.one_nat)
                        tsa;
                  } in Check_Monad.check
                         (Term_Rewriting.equal_term ta
                            (Term_Rewriting.Fun (ren (g, Arith.size_list ts))
                              (tsaa ++ [Term_Rewriting.Var x])) &&
                           ts == map (\ tb ->
                                       Term_Rewriting.eval_term
 Term_Rewriting.Fun tb (Term_Rewriting.subst x c))
                                   tsaa)
                         (((Shows_Literal.showsl_lit "could not relate " .
                             Term_Rewriting.showsl_terma t) .
                            Shows_Literal.showsl_lit " with ") .
                           Term_Rewriting.showsl_terma ta));
          });
      });
  });

extract_ren ::
  forall a b.
    (Eq a) => [((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                 (Term_Rewriting.Term a b, Term_Rewriting.Term a b))] ->
                Sum_Type.Sum (String -> String) ((a, Arith.Nat) -> a);
extract_ren ps_ps =
  Error_Monad.bind
    (Check_Monad.check
      (all (\ (a, b) ->
             (case a of {
               (s, t) ->
                 (\ (sa, ta) ->
                   not (Term_Rewriting.is_Var s) &&
                     not (Term_Rewriting.is_Var t) &&
                       not (Term_Rewriting.is_Var sa) &&
                         not (Term_Rewriting.is_Var ta));
             })
               b)
        ps_ps)
      (Shows_Literal.showsl_lit
        "all lhss and rhss of pairs must be non-variables"))
    (\ _ ->
      let {
        rt = (\ t -> Arith.the (Term_Rewriting.root t));
        pair = (\ s sa -> (rt s, fst (rt sa)));
        pairs =
          (\ (st, sta) -> [pair (fst st) (fst sta), pair (snd st) (snd sta)]);
        ren = Map.map_of (Arith.remdups (concatMap pairs ps_ps));
        a = (\ fn -> (case ren fn of {
                       Nothing -> fst fn;
                       Just f -> f;
                     }));
      } in Sum_Type.Inr a);

extract_fresh_var ::
  forall a b.
    [((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
       (Term_Rewriting.Term a b, Term_Rewriting.Term a b))] ->
      Sum_Type.Sum (String -> String) b;
extract_fresh_var sts =
  (case (case sts of {
          [] -> Nothing;
          (_, (Term_Rewriting.Var _, _)) : _ -> Nothing;
          (_, (Term_Rewriting.Fun _ ss, _)) : _ ->
            (if null ss then Nothing else (case Arith.last ss of {
    Term_Rewriting.Var a -> Just a;
    Term_Rewriting.Fun _ _ -> Nothing;
  }));
        })
    of {
    Nothing ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
          "could not extract fresh variable (as last argument from some lhs of new pairs)");
    Just a -> Sum_Type.Inr a;
  });

complex_constant_removal_proc ::
  forall a b c.
    (Arith.Ccompare a, Fresh.Infinite a, Eq a, Mapping.Mapping_impl a,
      Shows_Literal.Showl a, Compare.Compare_order c, Eq c,
      Shows_Literal.Showl c) => Renaming2.Renaming2 a ->
                                  Dependency_Pair_Problem_Spec.Dpp_ops_ext b c a
                                    () ->
                                    Complex_constant_removal_prf c a ->
                                      b -> Sum_Type.Sum (String -> String) b;
complex_constant_removal_proc rename i (Complex_Constant_Removal_Proof c ps) dpp
  = Error_Monad.catch_error
      (let {
         p = Dependency_Pair_Problem_Spec.p i dpp;
         pw = Dependency_Pair_Problem_Spec.pw i dpp;
         r = Dependency_Pair_Problem_Spec.rw i dpp;
         q = Dependency_Pair_Problem_Spec.q i dpp;
         pairs = Dependency_Pair_Problem_Spec.pairs i dpp;
       } in Error_Monad.bind (extract_fresh_var ps)
              (\ x ->
                Error_Monad.bind (extract_ren ps)
                  (\ ren ->
                    let {
                      is_def =
                        (\ fn ->
                          not (null (Dependency_Pair_Problem_Spec.rules_map i
                                      dpp fn)));
                      rQs = Arith.remdups (map Term_Rewriting.root q);
                    } in Error_Monad.bind
                           (Error_Monad.catch_error
                             (Error_Monad.forallM
                               (\ (s, t) ->
                                 Error_Monad.bind
                                   (Term_Rewriting.check_no_var s)
                                   (\ _ ->
                                     Error_Monad.bind
                                       (Term_Rewriting.check_no_var t)
                                       (\ _ ->
 Error_Monad.bind (Q_Restricted_Rewriting_Impl.check_no_defined_root is_def t)
   (\ _ ->
     Error_Monad.bind
       (Check_Monad.check
         (not (Arith.membera (Term_Rewriting.vars_rule_list (s, t)) x))
         ((Shows_Literal.showsl x .
            Shows_Literal.showsl_lit " is not fresh for pair ") .
           Term_Rewriting.showsl_rule (s, t)))
       (\ _ ->
         let {
           f = Arith.the (Term_Rewriting.root s);
           fa = (ren f, Arith.suc (snd f));
         } in Error_Monad.bind
                (Check_Monad.check (not (Arith.membera rQs (Just fa)))
                  (Shows_Literal.showsl_lit
                    "renaming delivers defined symbol of Q"))
                (\ _ ->
                  Check_Monad.check (not (is_def fa))
                    (Shows_Literal.showsl_lit
                      "renaming delivers defined symbol of R")))))))
                               pairs)
                             (\ xa -> Sum_Type.Inl (snd xa)))
                           (\ _ ->
                             let {
                               pps = filter
                                       (\ st_st -> Arith.membera p (fst st_st))
                                       ps;
                               pwps =
                                 filter
                                   (\ st_st -> Arith.membera pw (fst st_st)) ps;
                             } in Error_Monad.bind
                                    (Error_Monad.catch_error
                                      (Error_Monad.forallM
(\ st ->
  Check_Monad.check (Arith.membera (map fst pps) st)
    (Shows_Literal.showsl_lit "could not find entry for pair " .
      Term_Rewriting.showsl_rule st))
p)
                                      (\ xa -> Sum_Type.Inl (snd xa)))
                                    (\ _ ->
                                      Error_Monad.bind
(Error_Monad.catch_error
  (Error_Monad.forallM
    (\ st ->
      Check_Monad.check (Arith.membera (map fst pwps) st)
        (Shows_Literal.showsl_lit "could not find entry for pair " .
          Term_Rewriting.showsl_rule st))
    pw)
  (\ xa -> Sum_Type.Inl (snd xa)))
(\ _ ->
  Error_Monad.bind
    (Check_Monad.check (Term_Rewriting.ground c)
      ((Shows_Literal.showsl_lit "the term " . Term_Rewriting.showsl_terma c) .
        Shows_Literal.showsl_lit " is not ground"))
    (\ _ ->
      Error_Monad.bind
        (Check_Monad.check
          (Dependency_Pair_Problem_Spec.nFQ_subset_NF_rules i dpp)
          (Shows_Literal.showsl_lit "innermost required"))
        (\ _ ->
          Error_Monad.bind
            (Check_Monad.check (null (Dependency_Pair_Problem_Spec.r i dpp))
              (Shows_Literal.showsl_lit "strict rules not allowed"))
            (\ _ ->
              Error_Monad.bind
                (Check_Monad.check
                  (Dependency_Pair_Problem_Spec.rules_no_left_var i dpp)
                  (Shows_Literal.showsl_lit
                    "rules may not have variables as lhss"))
                (\ _ ->
                  Error_Monad.bind
                    (if Term_Rewriting.is_NF_trs r c then Sum_Type.Inr ()
                      else Error_Monad.catch_error
                             (Critical_Pairs_Impl.check_critical_pairs_innermost
                               rename r)
                             (\ xa ->
                               Sum_Type.Inl
                                 (Shows_Literal.showsl_lit
                                    "could not ensure confluence\n" .
                                   xa)))
                    (\ _ ->
                      Error_Monad.bind
                        (Error_Monad.catch_error
                          (Error_Monad.forallM
                            (\ st_st ->
                              Error_Monad.catch_error (check_drop x c ren st_st)
                                (\ xa ->
                                  Sum_Type.Inl
                                    (((((Shows_Literal.showsl_lit
   "problem in finding correspondence between rule " .
  Term_Rewriting.showsl_rule (fst st_st)) .
 Shows_Literal.showsl_lit " and rule ") .
Term_Rewriting.showsl_rule (snd st_st)) .
                                       Shows_Literal.showsl_literal "\n") .
                                      xa)))
                            ps)
                          (\ xa -> Sum_Type.Inl (snd xa)))
                        (\ _ ->
                          Sum_Type.Inr
                            (Dependency_Pair_Problem_Spec.mk i
                              (Dependency_Pair_Problem_Spec.nfs i dpp)
                              (Dependency_Pair_Problem_Spec.minimal i dpp)
                              (map snd pps) (map snd pwps) q [] r)))))))))))))
      (\ x ->
        Sum_Type.Inl
          (Shows_Literal.showsl_lit
             "problem in complex constant removal proc:\n" .
            x));

}
