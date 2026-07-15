{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Critical_Pairs_Impl(Join_info(..), critical_pairs_impl,
                       check_critical_pairs_NF, check_critical_pairs,
                       check_critical_pairs_innermost)
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
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Mapping;
import qualified Compare;
import qualified HOL;
import qualified Renaming2;
import qualified Arith;
import qualified Fresh;
import qualified Term_Rewriting;
import qualified Shows_Literal;
import qualified Check_Joins;

data Join_info a b = Guided_BFS (Check_Joins.Cp_join_hints a b) | Join_NF;

showsl_crit_pair ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => (Term_Rewriting.Term a b,
                                  Term_Rewriting.Term a b) ->
                                  String -> String;
showsl_crit_pair lr =
  (((Shows_Literal.showsl_lit "(" . Term_Rewriting.showsl_terma (fst lr)) .
     Shows_Literal.showsl_lit ", ") .
    Term_Rewriting.showsl_terma (snd lr)) .
    Shows_Literal.showsl_lit ")";

critical_pairs_impl ::
  forall a b.
    (Fresh.Infinite a, Eq a,
      Eq b) => Renaming2.Renaming2 a ->
                 [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
                   [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
                     [(Bool,
                        (Term_Rewriting.Term b a, Term_Rewriting.Term b a))];
critical_pairs_impl ren p r =
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
                        (\ (laa, rb) ->
                          (case Term_Rewriting.mgu_vd ren la laa of {
                            Nothing -> [];
                            Just (sigma, tau) ->
                              [(b, (Term_Rewriting.intp_actxt Term_Rewriting.Fun
                                      (Term_Rewriting.map_actxt (\ x -> x)
(\ t -> Term_Rewriting.eval_term Term_Rewriting.Fun t sigma) c)
                                      (Term_Rewriting.eval_term
Term_Rewriting.Fun rb tau),
                                     Term_Rewriting.eval_term Term_Rewriting.Fun
                                       ra sigma))];
                          }))
                        r))
        (Term_Rewriting.poss_list l))
    p;

check_critical_pairs_cp_info ::
  forall a b.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a, Arith.Ccompare b,
      Compare.Compare b, Eq b, Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => [(Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b)] ->
                                  [(Bool,
                                     (Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b))] ->
                                    Check_Joins.Cp_join_hints a b ->
                                      Sum_Type.Sum (String -> String) ();
check_critical_pairs_cp_info r cp hints =
  Error_Monad.bind (Check_Joins.is_rsteps_join_one r hints)
    (\ checker ->
      Error_Monad.catch_error (Error_Monad.forallM (\ (_, a) -> checker a) cp)
        (\ x -> Sum_Type.Inl (snd x)));

check_critical_pairs_NF ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => [(Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b)] ->
                                  [(Bool,
                                     (Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b))] ->
                                    Sum_Type.Sum (String -> String) ();
check_critical_pairs_NF r cp =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ (_, (s, t)) ->
        (if Term_Rewriting.equal_term s t then Sum_Type.Inr ()
          else Error_Monad.catch_error (Term_Rewriting.check_join_NF r s t)
                 (\ x ->
                   Sum_Type.Inl
                     (((Shows_Literal.showsl_lit
                          "problem when joining critical pair " .
                         showsl_crit_pair (s, t)) .
                        Shows_Literal.showsl_literal "\n") .
                       x))))
      cp)
    (\ x -> Sum_Type.Inl (snd x));

check_critical_pairs ::
  forall a b.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a, Arith.Ccompare b,
      Compare.Compare b, Eq b, Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => [(Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b)] ->
                                  [(Bool,
                                     (Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b))] ->
                                    Join_info a b ->
                                      Sum_Type.Sum (String -> String) ();
check_critical_pairs r cp join_info =
  (case join_info of {
    Guided_BFS a -> check_critical_pairs_cp_info r cp a;
    Join_NF -> check_critical_pairs_NF r cp;
  });

critical_pairs_top_impl ::
  forall a b.
    (Fresh.Infinite a, Eq a,
      Eq b) => Renaming2.Renaming2 a ->
                 [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
                   [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
                     [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)];
critical_pairs_top_impl ren p r =
  concatMap
    (\ (l, ra) ->
      (if Term_Rewriting.is_Var l then []
        else concatMap
               (\ (la, rb) ->
                 (case Term_Rewriting.mgu_vd ren l la of {
                   Nothing -> [];
                   Just (sigma, tau) ->
                     [(Term_Rewriting.eval_term Term_Rewriting.Fun rb tau,
                        Term_Rewriting.eval_term Term_Rewriting.Fun ra sigma)];
                 }))
               r))
    p;

check_critical_pairs_innermost ::
  forall a b.
    (Fresh.Infinite a, Eq a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => Renaming2.Renaming2 a ->
                                  [(Term_Rewriting.Term b a,
                                     Term_Rewriting.Term b a)] ->
                                    Sum_Type.Sum (String -> String) ();
check_critical_pairs_innermost ren r =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ (l, ra) ->
        Check_Monad.check (Term_Rewriting.equal_term l ra)
          (Shows_Literal.showsl_lit "there is a non-trivial critical pair " .
            showsl_crit_pair (l, ra)))
      (critical_pairs_top_impl ren r r))
    (\ x -> Sum_Type.Inl (snd x));

}
