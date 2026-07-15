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
import qualified Option;
import qualified HOL;
import qualified Phantom_Type;
import qualified Compare;
import qualified Container_Setup;
import qualified Collection_Order;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Arith;
import qualified Product_Type;
import qualified List;
import qualified Term;
import qualified Set;

newtype Subst_incr a b = Abs_subst_incr
  (b -> Term.Term a b, (Set.Set b, Term.Term a b -> [b]));

rep_subst_incr ::
  forall a b.
    Subst_incr a b -> (b -> Term.Term a b, (Set.Set b, Term.Term a b -> [b]));
rep_subst_incr (Abs_subst_incr x) = x;

si_W :: forall a b. Subst_incr a b -> Term.Term a b -> [b];
si_W xa = snd (snd (rep_subst_incr xa));

si_subst :: forall a b. Subst_incr a b -> b -> Term.Term a b;
si_subst xa = fst (rep_subst_incr xa);

si_v_incr :: forall a b. Subst_incr a b -> Set.Set b;
si_v_incr xa = fst (snd (rep_subst_incr xa));

ident_prob_of_smp ::
  forall a b.
    (Eq a,
      Eq b) => [(Term.Term a b, Term.Term a b)] ->
                 [(Term.Term a b, Term.Term a b)];
ident_prob_of_smp [] = [];
ident_prob_of_smp ((t, l) : other) =
  List.map_filter
    (\ x ->
      (if (case x of {
            (_, s) -> Term.equal_term s l;
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
      Eq b) => (a -> Term.Term b a) ->
                 (Term.Term b a, (Term.Term b a, Arith.Nat)) ->
                   [(Term.Term b a, (Term.Term b a, Arith.Nat))];
conflicts mu (Term.Var x, (Term.Fun g ss, n)) =
  [(Term.Var x, (Term.Fun g ss, n))];
conflicts mu (Term.Fun f ts, (Term.Fun g ss, n)) =
  (if f == g && Arith.equal_nat (List.size_list ts) (List.size_list ss)
    then concatMap (\ (s, t) -> conflicts mu (s, (t, n))) (zip ts ss)
    else [(Term.Fun f ts, (Term.Fun g ss, n))]);
conflicts mu (Term.Var x, (Term.Var y, n)) =
  (if Arith.equal_nat n Arith.zero_nat
    then (if x == y then [] else [(Term.Var x, (Term.Var y, Arith.zero_nat))])
    else conflicts mu (Term.Var x, (mu y, Arith.minus_nat n Arith.one_nat)));
conflicts mu (Term.Fun f ts, (Term.Var y, n)) =
  (if Arith.equal_nat n Arith.zero_nat
    then [(Term.Var y, (Term.Fun f ts, Arith.zero_nat))]
    else conflicts mu (Term.Fun f ts, (mu y, Arith.minus_nat n Arith.one_nat)));

ident_solvea ::
  forall a b.
    (Compare.Compare a, Eq a, Compare.Compare b,
      Eq b) => Subst_incr a b ->
                 Set.Set (Term.Term a b, (Term.Term a b, Arith.Nat)) ->
                   (Term.Term a b, (Term.Term a b, Arith.Nat)) ->
                     Maybe Arith.Nat;
ident_solvea mu_incr cps st =
  let {
    cp = conflicts (si_subst mu_incr) st;
  } in (if any (\ (u, (_, _)) -> not (Term.is_Var u)) cp then Nothing
         else (if any (\ (u, (v, _)) ->
                        Set.member (u, v)
                          (Set.image (\ (ua, (va, _)) -> (ua, va)) cps))
                    cp
                then Nothing
                else Option.bind
                       (Option_Monad.mapM
                         (\ (u, (v, m)) ->
                           ident_solvea mu_incr (Set.insert (u, (v, m)) cps)
                             (Term.eval_term Term.Fun u (si_subst mu_incr),
                               (v, Arith.suc m)))
                         (conflicts (si_subst mu_incr) st))
                       (\ is -> Just (Utility.max_list (map Arith.suc is)))));

ident_solve ::
  forall a b.
    (Compare.Compare a, Eq a, Compare.Compare b,
      Eq b) => Subst_incr a b ->
                 (Term.Term a b, Term.Term a b) -> Maybe Arith.Nat;
ident_solve mu_incr =
  (\ (s, t) ->
    ident_solvea mu_incr
      (Set_Impl.set_empty
        (Phantom_Type.of_phantom
          (Set_Impl.set_impl_prod ::
            Phantom_Type.Phantom (Term.Term a b, (Term.Term a b, Arith.Nat))
              Set_Impl.Set_impla)))
      (s, (t, Arith.zero_nat)));

simplify_mp ::
  forall a b.
    (Eq a, Collection_Eq.Ceq b,
      Collection_Order.Ccompare b) => Subst_incr a b ->
[(Term.Term a b, Term.Term a b)] ->
  [(Term.Term a b, Term.Term a b)] ->
    Maybe ([(Term.Term a b, Term.Term a b)], Arith.Nat);
simplify_mp mu_incr [] solved = Just (solved, Arith.zero_nat);
simplify_mp mu_incr ((s, Term.Var x) : mp) solved =
  simplify_mp mu_incr mp ((s, Term.Var x) : solved);
simplify_mp mu_incr ((Term.Fun g ts, Term.Fun f ls) : mp) solved =
  Option.bind (Option_Monad.guard (f == g))
    (\ _ ->
      Option.bind (Option_Monad.zip_option ts ls)
        (\ pairs -> simplify_mp mu_incr (pairs ++ mp) solved));
simplify_mp mu_incr ((Term.Var x, Term.Fun f ls) : mp) solved =
  Option.bind (Option_Monad.guard (Set.member x (si_v_incr mu_incr)))
    (\ _ ->
      let {
        m = map (\ (s, a) -> (Term.eval_term Term.Fun s (si_subst mu_incr), a));
      } in Option.bind
             (simplify_mp mu_incr (m ((Term.Var x, Term.Fun f ls) : mp))
               (m solved))
             (\ (smp, i) -> Just (smp, Arith.suc i)));

}
