{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Outermost_Loops(ident_prob_of_emp) where {

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
import qualified Innermost_Loops_Impl;
import qualified Option_Monad;
import qualified HOL;
import qualified Option_Util;
import qualified Sum_Type;
import qualified Compare;
import qualified Arith;
import qualified Map;
import qualified Innermost_Loops;
import qualified Term_Rewriting;

ident_prob_of_semp ::
  forall a b.
    (Eq a,
      Eq b) => (Term_Rewriting.Actxt a (Term_Rewriting.Term a b),
                 (Term_Rewriting.Term a b,
                   (Term_Rewriting.Actxt a (Term_Rewriting.Term a b),
                     (Term_Rewriting.Term a b,
                       [(Term_Rewriting.Term a b,
                          Term_Rewriting.Term a b)])))) ->
                 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
ident_prob_of_semp (d, (l, (c, (t, mp)))) =
  Innermost_Loops.ident_prob_of_smp mp;

eident_prob_of_semp ::
  forall a b.
    (Eq a,
      Eq b) => (Term_Rewriting.Actxt a (Term_Rewriting.Term a b),
                 (Term_Rewriting.Term a b,
                   (Term_Rewriting.Actxt a (Term_Rewriting.Term a b),
                     (Term_Rewriting.Term a b,
                       [(Term_Rewriting.Term a b,
                          Term_Rewriting.Term a b)])))) ->
                 Maybe (Term_Rewriting.Actxt a (Term_Rewriting.Term a b),
                         (Term_Rewriting.Term a b,
                           (Term_Rewriting.Actxt a (Term_Rewriting.Term a b),
                             Term_Rewriting.Term a b)));
eident_prob_of_semp (d, (l, (c, (t, mp)))) =
  Arith.bind (Map.map_of (Term_Rewriting.reverse_rules mp) l)
    (\ si -> Just (d, (si, (c, t))));

eident_prob_to_ident_prob ::
  forall a b.
    (Term_Rewriting.Actxt a (Term_Rewriting.Term a b),
      (Term_Rewriting.Term a b,
        (Term_Rewriting.Actxt a (Term_Rewriting.Term a b),
          Term_Rewriting.Term a b))) ->
      (Term_Rewriting.Term a b, Term_Rewriting.Term a b);
eident_prob_to_ident_prob (d, (si, (c, t))) =
  (Term_Rewriting.intp_actxt Term_Rewriting.Fun d t, si);

simplify_emp_main ::
  forall a b.
    (Compare.Compare a, Eq a, Arith.Ceq b, Arith.Ccompare b, Compare.Compare b,
      Eq b) => Innermost_Loops.Subst_incr a b ->
                 (Term_Rewriting.Actxt a (Term_Rewriting.Term a b),
                   (Term_Rewriting.Term a b,
                     (Term_Rewriting.Actxt a (Term_Rewriting.Term a b),
                       (Term_Rewriting.Term a b,
                         [(Term_Rewriting.Term a b,
                            Term_Rewriting.Term a b)])))) ->
                   [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                     Maybe (Maybe (Term_Rewriting.Actxt a
                                     (Term_Rewriting.Term a b),
                                    (Term_Rewriting.Term a b,
                                      (Term_Rewriting.Actxt a
 (Term_Rewriting.Term a b),
(Term_Rewriting.Term a b,
  [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)])))));
simplify_emp_main mu_incr (d, (l, (c, (t, (s, Term_Rewriting.Var x) : mp))))
  solved =
  simplify_emp_main mu_incr (d, (l, (c, (t, mp))))
    ((s, Term_Rewriting.Var x) : solved);
simplify_emp_main mu_incr
  (d, (l, (c, (t, (Term_Rewriting.Fun g ts, Term_Rewriting.Fun f ls) : mp))))
  solved =
  Arith.bind (Option_Monad.guard (f == g))
    (\ _ ->
      Arith.bind (Option_Monad.zip_option ts ls)
        (\ pairs ->
          simplify_emp_main mu_incr (d, (l, (c, (t, pairs ++ mp)))) solved));
simplify_emp_main mu_incr
  (d, (l, (c, (t, (Term_Rewriting.Var x, Term_Rewriting.Fun f ls) : mp))))
  solved =
  Arith.bind
    (Option_Monad.guard (Arith.member x (Innermost_Loops.si_v_incr mu_incr)))
    (\ _ ->
      let {
        m = map (\ (s, a) ->
                  (Term_Rewriting.eval_term Term_Rewriting.Fun s
                     (Innermost_Loops.si_subst mu_incr),
                    a));
      } in simplify_emp_main mu_incr
             (Term_Rewriting.map_actxt (\ xa -> xa)
                (\ ta ->
                  Term_Rewriting.eval_term Term_Rewriting.Fun ta
                    (Innermost_Loops.si_subst mu_incr))
                d,
               (l, (Term_Rewriting.map_actxt (\ xa -> xa)
                      (\ ta ->
                        Term_Rewriting.eval_term Term_Rewriting.Fun ta
                          (Innermost_Loops.si_subst mu_incr))
                      c,
                     (Term_Rewriting.eval_term Term_Rewriting.Fun t
                        (Innermost_Loops.si_subst mu_incr),
                       m ((Term_Rewriting.Var x, Term_Rewriting.Fun f ls) :
                           mp)))))
             (m solved));
simplify_emp_main mu_incr (d, (Term_Rewriting.Var x, (c, (t, [])))) solved =
  Just (Just (d, (Term_Rewriting.Var x, (c, (t, solved)))));
simplify_emp_main mu_incr
  (Term_Rewriting.More f bef d aft, (Term_Rewriting.Fun g ls, (c, (t, []))))
  solved =
  Arith.bind (Option_Monad.guard (f == g))
    (\ _ ->
      Arith.bind
        (Option_Monad.guard
          (Arith.equal_nat (Arith.size_list ls)
            (Arith.suc
              (Arith.plus_nat (Arith.size_list bef) (Arith.size_list aft)))))
        (\ _ ->
          let {
            pairs_bef = zip bef (Arith.take (Arith.size_list bef) ls);
            pairs_aft =
              zip aft (Arith.drop (Arith.suc (Arith.size_list bef)) ls);
          } in simplify_emp_main mu_incr
                 (d, (Arith.nth ls (Arith.size_list bef),
                       (c, (t, pairs_bef ++ pairs_aft))))
                 solved));
simplify_emp_main mu_incr
  (Term_Rewriting.Hole, (Term_Rewriting.Fun g ls, (c, (t, [])))) solved =
  (if Innermost_Loops_Impl.gmatch_decision mu_incr
        ((t, Term_Rewriting.Fun g ls) : solved)
    then Just Nothing
    else (if Term_Rewriting.equal_actxt c Term_Rewriting.Hole then Nothing
           else simplify_emp_main mu_incr
                  (c, (Term_Rewriting.Fun g ls,
                        (Term_Rewriting.map_actxt (\ x -> x)
                           (\ ta ->
                             Term_Rewriting.eval_term Term_Rewriting.Fun ta
                               (Innermost_Loops.si_subst mu_incr))
                           c,
                          (Term_Rewriting.eval_term Term_Rewriting.Fun t
                             (Innermost_Loops.si_subst mu_incr),
                            []))))
                  solved));

simplify_emp ::
  forall a b.
    (Compare.Compare a, Eq a, Arith.Ceq b, Arith.Ccompare b, Compare.Compare b,
      Eq b) => Innermost_Loops.Subst_incr a b ->
                 (Term_Rewriting.Actxt a (Term_Rewriting.Term a b),
                   (Term_Rewriting.Term a b,
                     (Term_Rewriting.Actxt a (Term_Rewriting.Term a b),
                       Term_Rewriting.Term a b))) ->
                   Sum_Type.Sum
                     (Term_Rewriting.Actxt a (Term_Rewriting.Term a b),
                       (Term_Rewriting.Term a b,
                         (Term_Rewriting.Actxt a (Term_Rewriting.Term a b),
                           (Term_Rewriting.Term a b,
                             [(Term_Rewriting.Term a b,
                                Term_Rewriting.Term a b)]))))
                     Bool;
simplify_emp mu_incr emp =
  (case emp of {
    (d, (l, (c, t))) ->
      (case simplify_emp_main mu_incr (d, (l, (c, (t, [])))) [] of {
        Nothing -> Sum_Type.Inr False;
        Just Nothing -> Sum_Type.Inr True;
        Just (Just a) -> Sum_Type.Inl a;
      });
  });

ident_prob_of_emp ::
  forall a b.
    (Compare.Compare a, Eq a, Arith.Ceq b, Arith.Ccompare b, Compare.Compare b,
      Eq b) => Innermost_Loops.Subst_incr a b ->
                 (Term_Rewriting.Actxt a (Term_Rewriting.Term a b),
                   (Term_Rewriting.Term a b,
                     (Term_Rewriting.Actxt a (Term_Rewriting.Term a b),
                       Term_Rewriting.Term a b))) ->
                   Maybe [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
ident_prob_of_emp mu_incr emp =
  (case simplify_emp mu_incr emp of {
    Sum_Type.Inl semp ->
      Just (map eident_prob_to_ident_prob
              (Option_Util.option_to_list (eident_prob_of_semp semp)) ++
             ident_prob_of_semp semp);
    Sum_Type.Inr True -> Just [];
    Sum_Type.Inr False -> Nothing;
  });

}
