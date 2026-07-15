{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Bounded_Increase(normalize_cc, vars_cc_list, cc_subst_apply, normalize_alpha,
                    cc_rule_constraint)
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
import qualified Fun;
import qualified Arith;
import qualified HOL;
import qualified Term_Rewriting;
import qualified Generalized_Usable_Rules;

cc_bound ::
  forall a b.
    [a] ->
      Generalized_Usable_Rules.Cond_constraint b a ->
        Generalized_Usable_Rules.Cond_constraint b a;
cc_bound [] c = c;
cc_bound (x : xs) c = Generalized_Usable_Rules.CC_all x (cc_bound xs c);

concl_of ::
  forall a b.
    Generalized_Usable_Rules.Cond_constraint a b ->
      Generalized_Usable_Rules.Cond_constraint a b;
concl_of (Generalized_Usable_Rules.CC_impl c1 c2) = c2;
concl_of (Generalized_Usable_Rules.CC_cond v va) =
  Generalized_Usable_Rules.CC_cond v va;
concl_of (Generalized_Usable_Rules.CC_rewr v va) =
  Generalized_Usable_Rules.CC_rewr v va;
concl_of (Generalized_Usable_Rules.CC_all v va) =
  Generalized_Usable_Rules.CC_all v va;

prems_of ::
  forall a b.
    Generalized_Usable_Rules.Cond_constraint a b ->
      [Generalized_Usable_Rules.Cond_constraint a b];
prems_of (Generalized_Usable_Rules.CC_impl c1 c2) = c1;
prems_of (Generalized_Usable_Rules.CC_cond v va) = [];
prems_of (Generalized_Usable_Rules.CC_rewr v va) = [];
prems_of (Generalized_Usable_Rules.CC_all v va) = [];

normalize_cc ::
  forall a b.
    Generalized_Usable_Rules.Cond_constraint a b ->
      Generalized_Usable_Rules.Cond_constraint a b;
normalize_cc c = Generalized_Usable_Rules.CC_impl (prems_of c) (concl_of c);

vars_cc_list ::
  forall a b. (Eq b) => Generalized_Usable_Rules.Cond_constraint a b -> [b];
vars_cc_list (Generalized_Usable_Rules.CC_cond ct (s, t)) =
  Term_Rewriting.vars_term_list s ++ Term_Rewriting.vars_term_list t;
vars_cc_list (Generalized_Usable_Rules.CC_rewr s t) =
  Term_Rewriting.vars_term_list s ++ Term_Rewriting.vars_term_list t;
vars_cc_list (Generalized_Usable_Rules.CC_impl c1 c2) =
  concatMap vars_cc_list c1 ++ vars_cc_list c2;
vars_cc_list (Generalized_Usable_Rules.CC_all x c) =
  concatMap (\ y -> (if not (y == x) then [y] else [])) (vars_cc_list c);

cc_subst_apply ::
  forall a b.
    (Eq a) => ([a] -> a) ->
                Generalized_Usable_Rules.Cond_constraint b a ->
                  (a -> Term_Rewriting.Term b a, [a]) ->
                    Generalized_Usable_Rules.Cond_constraint b a;
cc_subst_apply fresh (Generalized_Usable_Rules.CC_cond ct (s, t)) (sigma, uu) =
  Generalized_Usable_Rules.CC_cond ct
    (Term_Rewriting.eval_term Term_Rewriting.Fun s sigma,
      Term_Rewriting.eval_term Term_Rewriting.Fun t sigma);
cc_subst_apply fresh (Generalized_Usable_Rules.CC_rewr s t) (sigma, uv) =
  Generalized_Usable_Rules.CC_rewr
    (Term_Rewriting.eval_term Term_Rewriting.Fun s sigma)
    (Term_Rewriting.eval_term Term_Rewriting.Fun t sigma);
cc_subst_apply fresh (Generalized_Usable_Rules.CC_impl c1 c2) sigma =
  Generalized_Usable_Rules.CC_impl
    (map (\ c -> cc_subst_apply fresh c sigma) c1)
    (cc_subst_apply fresh c2 sigma);
cc_subst_apply fresh (Generalized_Usable_Rules.CC_all x c) (sigma, vs) =
  let {
    y = fresh (vs ++ vars_cc_list (Generalized_Usable_Rules.CC_all x c));
  } in Generalized_Usable_Rules.CC_all y
         (cc_subst_apply fresh c
           (Fun.fun_upd sigma x (Term_Rewriting.Var y), y : vs));

cc_ih_prems ::
  forall a b.
    (Eq a,
      Eq b) => ([a] -> a) ->
                 b -> Term_Rewriting.Term b a ->
                        [a] ->
                          [Generalized_Usable_Rules.Cond_constraint b a] ->
                            Generalized_Usable_Rules.Cond_constraint b a ->
                              [(Term_Rewriting.Term b a, [a])] ->
                                [Generalized_Usable_Rules.Cond_constraint b a];
cc_ih_prems fresh f q xs phi psi rs_ys_list =
  map (\ (r, ys) ->
        let {
          rs = Term_Rewriting.args r;
          mu = Term_Rewriting.mk_subst Term_Rewriting.Var (zip xs rs);
          vs = Term_Rewriting.range_vars_impl (zip xs rs);
          mua = (\ c -> cc_subst_apply fresh c (mu, vs));
          a = Generalized_Usable_Rules.CC_impl
                (Generalized_Usable_Rules.CC_rewr r
                   (Term_Rewriting.eval_term Term_Rewriting.Fun q mu) :
                  map mua phi)
                (mua psi);
        } in cc_bound ys a)
    rs_ys_list;

normalize_alpha ::
  forall a b.
    (Eq a) => ([a] -> a) ->
                Generalized_Usable_Rules.Cond_constraint b a ->
                  Generalized_Usable_Rules.Cond_constraint b a;
normalize_alpha fresh c = cc_subst_apply fresh c (Term_Rewriting.Var, []);

cc_rule_constraint ::
  forall a b.
    (Eq a,
      Eq b) => ([a] -> a) ->
                 b -> [Term_Rewriting.Term b a] ->
                        Term_Rewriting.Term b a ->
                          Term_Rewriting.Term b a ->
                            [a] ->
                              [Generalized_Usable_Rules.Cond_constraint b a] ->
                                Generalized_Usable_Rules.Cond_constraint b a ->
                                  [(Term_Rewriting.Term b a, [a])] ->
                                    Generalized_Usable_Rules.Cond_constraint b
                                      a;
cc_rule_constraint fresh f ls r q xs phi psi rs_ys_list =
  let {
    sigma = Term_Rewriting.mk_subst Term_Rewriting.Var (zip xs ls);
    vs = Term_Rewriting.range_vars_impl (zip xs ls);
    rew = Generalized_Usable_Rules.CC_rewr r
            (Term_Rewriting.eval_term Term_Rewriting.Fun q sigma);
    phi_sig = map (\ c -> cc_subst_apply fresh c (sigma, vs)) phi;
    psi_sig = cc_subst_apply fresh psi (sigma, vs);
    ihs = cc_ih_prems fresh f q xs phi psi rs_ys_list;
  } in Generalized_Usable_Rules.CC_impl (rew : phi_sig ++ ihs) psi_sig;

}
