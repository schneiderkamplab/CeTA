{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Innermost_Loops(Subst_incr(..), si_W, si_subst, si_v_incr, ident_prob_of_smp,
                   ident_solve, simplify_mp)
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
import qualified Utility;
import qualified Option_Monad;
import qualified HOL;
import qualified Phantom_Type;
import qualified Compare;
import qualified Term_Rewriting;
import qualified Arith;

newtype Subst_incr a b = Abs_subst_incr
  (b -> Term_Rewriting.Term a b, (Arith.Set b, Term_Rewriting.Term a b -> [b]));

rep_subst_incr ::
  forall a b.
    Subst_incr a b ->
      (b -> Term_Rewriting.Term a b,
        (Arith.Set b, Term_Rewriting.Term a b -> [b]));
rep_subst_incr (Abs_subst_incr x) = x;

si_W :: forall a b. Subst_incr a b -> Term_Rewriting.Term a b -> [b];
si_W xa = snd (snd (rep_subst_incr xa));

si_subst :: forall a b. Subst_incr a b -> b -> Term_Rewriting.Term a b;
si_subst xa = fst (rep_subst_incr xa);

si_v_incr :: forall a b. Subst_incr a b -> Arith.Set b;
si_v_incr xa = fst (snd (rep_subst_incr xa));

ident_prob_of_smp ::
  forall a b.
    (Eq a,
      Eq b) => [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
ident_prob_of_smp [] = [];
ident_prob_of_smp ((t, l) : other) =
  Arith.map_filter
    (\ x ->
      (if (case x of {
            (_, s) -> Term_Rewriting.equal_term s l;
          })
        then Just (case x of {
                    (s, _) -> (t, s);
                  })
        else Nothing))
    other ++
    ident_prob_of_smp other;

conflicts ::
  forall a b.
    (Eq a,
      Eq b) => (a -> Term_Rewriting.Term b a) ->
                 (Term_Rewriting.Term b a,
                   (Term_Rewriting.Term b a, Arith.Nat)) ->
                   [(Term_Rewriting.Term b a,
                      (Term_Rewriting.Term b a, Arith.Nat))];
conflicts mu (Term_Rewriting.Var x, (Term_Rewriting.Fun g ss, n)) =
  [(Term_Rewriting.Var x, (Term_Rewriting.Fun g ss, n))];
conflicts mu (Term_Rewriting.Fun f ts, (Term_Rewriting.Fun g ss, n)) =
  (if f == g && Arith.equal_nat (Arith.size_list ts) (Arith.size_list ss)
    then concatMap (\ (s, t) -> conflicts mu (s, (t, n))) (zip ts ss)
    else [(Term_Rewriting.Fun f ts, (Term_Rewriting.Fun g ss, n))]);
conflicts mu (Term_Rewriting.Var x, (Term_Rewriting.Var y, n)) =
  (if Arith.equal_nat n Arith.zero_nat
    then (if x == y then []
           else [(Term_Rewriting.Var x,
                   (Term_Rewriting.Var y, Arith.zero_nat))])
    else conflicts mu
           (Term_Rewriting.Var x, (mu y, Arith.minus_nat n Arith.one_nat)));
conflicts mu (Term_Rewriting.Fun f ts, (Term_Rewriting.Var y, n)) =
  (if Arith.equal_nat n Arith.zero_nat
    then [(Term_Rewriting.Var y, (Term_Rewriting.Fun f ts, Arith.zero_nat))]
    else conflicts mu
           (Term_Rewriting.Fun f ts, (mu y, Arith.minus_nat n Arith.one_nat)));

ident_solvea ::
  forall a b.
    (Compare.Compare a, Eq a, Compare.Compare b,
      Eq b) => Subst_incr a b ->
                 Arith.Set
                   (Term_Rewriting.Term a b,
                     (Term_Rewriting.Term a b, Arith.Nat)) ->
                   (Term_Rewriting.Term a b,
                     (Term_Rewriting.Term a b, Arith.Nat)) ->
                     Maybe Arith.Nat;
ident_solvea mu_incr cps st =
  let {
    cp = conflicts (si_subst mu_incr) st;
  } in (if any (\ (u, (_, _)) -> not (Term_Rewriting.is_Var u)) cp then Nothing
         else (if any (\ (u, (v, _)) ->
                        Arith.member (u, v)
                          (Arith.image (\ (ua, (va, _)) -> (ua, va)) cps))
                    cp
                then Nothing
                else Arith.bind
                       (Option_Monad.mapM
                         (\ (u, (v, m)) ->
                           ident_solvea mu_incr (Arith.insert (u, (v, m)) cps)
                             (Term_Rewriting.eval_term Term_Rewriting.Fun u
                                (si_subst mu_incr),
                               (v, Arith.suc m)))
                         (conflicts (si_subst mu_incr) st))
                       (\ is -> Just (Utility.max_list (map Arith.suc is)))));

ident_solve ::
  forall a b.
    (Compare.Compare a, Eq a, Compare.Compare b,
      Eq b) => Subst_incr a b ->
                 (Term_Rewriting.Term a b, Term_Rewriting.Term a b) ->
                   Maybe Arith.Nat;
ident_solve mu_incr =
  (\ (s, t) ->
    ident_solvea mu_incr
      (Arith.set_empty
        (Phantom_Type.of_phantom
          (Arith.set_impl_prod ::
            Phantom_Type.Phantom
              (Term_Rewriting.Term a b, (Term_Rewriting.Term a b, Arith.Nat))
              Arith.Set_impla)))
      (s, (t, Arith.zero_nat)));

simplify_mp ::
  forall a b.
    (Eq a, Arith.Ceq b,
      Arith.Ccompare b) => Subst_incr a b ->
                             [(Term_Rewriting.Term a b,
                                Term_Rewriting.Term a b)] ->
                               [(Term_Rewriting.Term a b,
                                  Term_Rewriting.Term a b)] ->
                                 Maybe ([(Term_Rewriting.Term a b,
   Term_Rewriting.Term a b)],
 Arith.Nat);
simplify_mp mu_incr [] solved = Just (solved, Arith.zero_nat);
simplify_mp mu_incr ((s, Term_Rewriting.Var x) : mp) solved =
  simplify_mp mu_incr mp ((s, Term_Rewriting.Var x) : solved);
simplify_mp mu_incr ((Term_Rewriting.Fun g ts, Term_Rewriting.Fun f ls) : mp)
  solved =
  Arith.bind (Option_Monad.guard (f == g))
    (\ _ ->
      Arith.bind (Option_Monad.zip_option ts ls)
        (\ pairs -> simplify_mp mu_incr (pairs ++ mp) solved));
simplify_mp mu_incr ((Term_Rewriting.Var x, Term_Rewriting.Fun f ls) : mp)
  solved =
  Arith.bind (Option_Monad.guard (Arith.member x (si_v_incr mu_incr)))
    (\ _ ->
      let {
        m = map (\ (s, a) ->
                  (Term_Rewriting.eval_term Term_Rewriting.Fun s
                     (si_subst mu_incr),
                    a));
      } in Arith.bind
             (simplify_mp mu_incr
               (m ((Term_Rewriting.Var x, Term_Rewriting.Fun f ls) : mp))
               (m solved))
             (\ (smp, i) -> Just (smp, Arith.suc i)));

}
