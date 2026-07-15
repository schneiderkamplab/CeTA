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
import qualified List;
import qualified HOL;
import qualified Set;
import qualified Arith;
import qualified Option_Util;
import qualified Product_Type;
import qualified Sum_Type;
import qualified Collection_Order;
import qualified Collection_Eq;
import qualified Compare;
import qualified Trs_Impl;
import qualified Option;
import qualified Map;
import qualified Innermost_Loops;
import qualified Subterm_and_Context;
import qualified Term;

ident_prob_of_semp ::
  forall a b.
    (Eq a,
      Eq b) => (Subterm_and_Context.Actxt a (Term.Term a b),
                 (Term.Term a b,
                   (Subterm_and_Context.Actxt a (Term.Term a b),
                     (Term.Term a b, [(Term.Term a b, Term.Term a b)])))) ->
                 [(Term.Term a b, Term.Term a b)];
ident_prob_of_semp (d, (l, (c, (t, mp)))) =
  Innermost_Loops.ident_prob_of_smp mp;

eident_prob_of_semp ::
  forall a b.
    (Eq a,
      Eq b) => (Subterm_and_Context.Actxt a (Term.Term a b),
                 (Term.Term a b,
                   (Subterm_and_Context.Actxt a (Term.Term a b),
                     (Term.Term a b, [(Term.Term a b, Term.Term a b)])))) ->
                 Maybe (Subterm_and_Context.Actxt a (Term.Term a b),
                         (Term.Term a b,
                           (Subterm_and_Context.Actxt a (Term.Term a b),
                             Term.Term a b)));
eident_prob_of_semp (d, (l, (c, (t, mp)))) =
  Option.bind (Map.map_of (Trs_Impl.reverse_rules mp) l)
    (\ si -> Just (d, (si, (c, t))));

eident_prob_to_ident_prob ::
  forall a b.
    (Subterm_and_Context.Actxt a (Term.Term a b),
      (Term.Term a b,
        (Subterm_and_Context.Actxt a (Term.Term a b), Term.Term a b))) ->
      (Term.Term a b, Term.Term a b);
eident_prob_to_ident_prob (d, (si, (c, t))) =
  (Subterm_and_Context.intp_actxt Term.Fun d t, si);

simplify_emp_main ::
  forall a b.
    (Compare.Compare a, Eq a, Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Compare.Compare b,
      Eq b) => Innermost_Loops.Subst_incr a b ->
                 (Subterm_and_Context.Actxt a (Term.Term a b),
                   (Term.Term a b,
                     (Subterm_and_Context.Actxt a (Term.Term a b),
                       (Term.Term a b, [(Term.Term a b, Term.Term a b)])))) ->
                   [(Term.Term a b, Term.Term a b)] ->
                     Maybe (Maybe (Subterm_and_Context.Actxt a (Term.Term a b),
                                    (Term.Term a b,
                                      (Subterm_and_Context.Actxt a
 (Term.Term a b),
(Term.Term a b, [(Term.Term a b, Term.Term a b)])))));
simplify_emp_main mu_incr (d, (l, (c, (t, (s, Term.Var x) : mp)))) solved =
  simplify_emp_main mu_incr (d, (l, (c, (t, mp)))) ((s, Term.Var x) : solved);
simplify_emp_main mu_incr
  (d, (l, (c, (t, (Term.Fun g ts, Term.Fun f ls) : mp)))) solved =
  Option.bind (Option_Monad.guard (f == g))
    (\ _ ->
      Option.bind (Option_Monad.zip_option ts ls)
        (\ pairs ->
          simplify_emp_main mu_incr (d, (l, (c, (t, pairs ++ mp)))) solved));
simplify_emp_main mu_incr (d, (l, (c, (t, (Term.Var x, Term.Fun f ls) : mp))))
  solved =
  Option.bind
    (Option_Monad.guard (Set.member x (Innermost_Loops.si_v_incr mu_incr)))
    (\ _ ->
      let {
        m = map (\ (s, a) ->
                  (Term.eval_term Term.Fun s (Innermost_Loops.si_subst mu_incr),
                    a));
      } in simplify_emp_main mu_incr
             (Subterm_and_Context.map_actxt (\ xa -> xa)
                (\ ta ->
                  Term.eval_term Term.Fun ta (Innermost_Loops.si_subst mu_incr))
                d,
               (l, (Subterm_and_Context.map_actxt (\ xa -> xa)
                      (\ ta ->
                        Term.eval_term Term.Fun ta
                          (Innermost_Loops.si_subst mu_incr))
                      c,
                     (Term.eval_term Term.Fun t
                        (Innermost_Loops.si_subst mu_incr),
                       m ((Term.Var x, Term.Fun f ls) : mp)))))
             (m solved));
simplify_emp_main mu_incr (d, (Term.Var x, (c, (t, [])))) solved =
  Just (Just (d, (Term.Var x, (c, (t, solved)))));
simplify_emp_main mu_incr
  (Subterm_and_Context.More f bef d aft, (Term.Fun g ls, (c, (t, [])))) solved =
  Option.bind (Option_Monad.guard (f == g))
    (\ _ ->
      Option.bind
        (Option_Monad.guard
          (Arith.equal_nat (List.size_list ls)
            (Arith.suc
              (Arith.plus_nat (List.size_list bef) (List.size_list aft)))))
        (\ _ ->
          let {
            pairs_bef = zip bef (List.take (List.size_list bef) ls);
            pairs_aft = zip aft (List.drop (Arith.suc (List.size_list bef)) ls);
          } in simplify_emp_main mu_incr
                 (d, (List.nth ls (List.size_list bef),
                       (c, (t, pairs_bef ++ pairs_aft))))
                 solved));
simplify_emp_main mu_incr
  (Subterm_and_Context.Hole, (Term.Fun g ls, (c, (t, [])))) solved =
  (if Innermost_Loops_Impl.gmatch_decision mu_incr ((t, Term.Fun g ls) : solved)
    then Just Nothing
    else (if Subterm_and_Context.equal_actxt c Subterm_and_Context.Hole
           then Nothing
           else simplify_emp_main mu_incr
                  (c, (Term.Fun g ls,
                        (Subterm_and_Context.map_actxt (\ x -> x)
                           (\ ta ->
                             Term.eval_term Term.Fun ta
                               (Innermost_Loops.si_subst mu_incr))
                           c,
                          (Term.eval_term Term.Fun t
                             (Innermost_Loops.si_subst mu_incr),
                            []))))
                  solved));

simplify_emp ::
  forall a b.
    (Compare.Compare a, Eq a, Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Compare.Compare b,
      Eq b) => Innermost_Loops.Subst_incr a b ->
                 (Subterm_and_Context.Actxt a (Term.Term a b),
                   (Term.Term a b,
                     (Subterm_and_Context.Actxt a (Term.Term a b),
                       Term.Term a b))) ->
                   Sum_Type.Sum
                     (Subterm_and_Context.Actxt a (Term.Term a b),
                       (Term.Term a b,
                         (Subterm_and_Context.Actxt a (Term.Term a b),
                           (Term.Term a b, [(Term.Term a b, Term.Term a b)]))))
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
    (Compare.Compare a, Eq a, Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Compare.Compare b,
      Eq b) => Innermost_Loops.Subst_incr a b ->
                 (Subterm_and_Context.Actxt a (Term.Term a b),
                   (Term.Term a b,
                     (Subterm_and_Context.Actxt a (Term.Term a b),
                       Term.Term a b))) ->
                   Maybe [(Term.Term a b, Term.Term a b)];
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
