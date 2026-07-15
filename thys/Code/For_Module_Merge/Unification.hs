{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Unification(subst_of, subst_list, decompose, unify, mgu,
               mgu_var_disjoint_generic, mgu_vd)
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
import qualified Option_Monad;
import qualified Product_Type;
import qualified List;
import qualified Renaming2;
import qualified Fresh;
import qualified Term_Impl;
import qualified Option;
import qualified Term;

subst_of :: forall a b. (Eq a) => [(a, Term.Term b a)] -> a -> Term.Term b a;
subst_of ss =
  List.foldr (\ (x, t) sigma -> Term.eval_subst Term.Fun sigma (Term.subst x t))
    ss Term.Var;

subst_list ::
  forall a b.
    (a -> Term.Term b a) ->
      [(Term.Term b a, Term.Term b a)] -> [(Term.Term b a, Term.Term b a)];
subst_list sigma ys =
  map (\ p ->
        (Term.eval_term Term.Fun (fst p) sigma,
          Term.eval_term Term.Fun (snd p) sigma))
    ys;

decompose ::
  forall a b c.
    (Eq a) => Term.Term a b ->
                Term.Term a c -> Maybe [(Term.Term a b, Term.Term a c)];
decompose s t =
  (case (s, t) of {
    (Term.Var _, _) -> Nothing;
    (Term.Fun _ _, Term.Var _) -> Nothing;
    (Term.Fun f ss, Term.Fun g ts) ->
      (if f == g then Option_Monad.zip_option ss ts else Nothing);
  });

unify ::
  forall a b.
    (Eq a,
      Eq b) => [(Term.Term a b, Term.Term a b)] ->
                 [(b, Term.Term a b)] -> Maybe [(b, Term.Term a b)];
unify [] bs = Just bs;
unify ((Term.Fun f ss, Term.Fun g ts) : e) bs =
  (case decompose (Term.Fun f ss) (Term.Fun g ts) of {
    Nothing -> Nothing;
    Just us -> unify (us ++ e) bs;
  });
unify ((Term.Var x, t) : e) bs =
  (if Term.equal_term t (Term.Var x) then unify e bs
    else (if Term_Impl.contains_var_term x t then Nothing
           else unify (subst_list (Term.subst x t) e) ((x, t) : bs)));
unify ((Term.Fun v va, Term.Var x) : e) bs =
  (if Term_Impl.contains_var_term x (Term.Fun v va) then Nothing
    else unify (subst_list (Term.subst x (Term.Fun v va)) e)
           ((x, Term.Fun v va) : bs));

mgu ::
  forall a b.
    (Eq a,
      Eq b) => Term.Term a b -> Term.Term a b -> Maybe (b -> Term.Term a b);
mgu s t = (case unify [(s, t)] [] of {
            Nothing -> Nothing;
            Just res -> Just (subst_of res);
          });

mgu_var_disjoint_generic ::
  forall a b c d.
    (Eq b,
      Eq d) => (a -> b) ->
                 (c -> b) ->
                   Term.Term d a ->
                     Term.Term d c ->
                       Maybe (a -> Term.Term d b, c -> Term.Term d b);
mgu_var_disjoint_generic vu wu s t =
  (case mgu (Term.map_term (\ x -> x) vu s) (Term.map_term (\ x -> x) wu t) of {
    Nothing -> Nothing;
    Just gamma -> Just (gamma . vu, gamma . wu);
  });

mgu_vd ::
  forall a b.
    (Fresh.Infinite a, Eq a,
      Eq b) => Renaming2.Renaming2 a ->
                 Term.Term b a ->
                   Term.Term b a ->
                     Maybe (a -> Term.Term b a, a -> Term.Term b a);
mgu_vd r =
  mgu_var_disjoint_generic (Renaming2.rename_1 r) (Renaming2.rename_2 r);

}
