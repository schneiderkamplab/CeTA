{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Mgu_generic(rename_many, mgu_vd_list) where {

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
import qualified Product_Type;
import qualified Option;
import qualified Unification;
import qualified List;
import qualified HOL;
import qualified RenamingN;
import qualified Term;
import qualified Arith;
import qualified Fresh;

mgu_var_disjoint_list_generic ::
  forall a b.
    (Eq a,
      Eq b) => (Arith.Nat -> a -> a) ->
                 (a -> a) ->
                   [(Term.Term b a, Term.Term b a)] ->
                     Maybe ([a -> Term.Term b a], a -> Term.Term b a);
mgu_var_disjoint_list_generic rename_many ren_l sls =
  let {
    pairs =
      map (\ (i, (si, li)) ->
            (Term.map_term (\ x -> x) (rename_many i) si,
              Term.map_term (\ x -> x) ren_l li))
        (zip (List.upt Arith.zero_nat (List.size_list sls)) sls);
  } in (case Unification.unify pairs [] of {
         Nothing -> Nothing;
         Just gamma_list ->
           let {
             gamma = Unification.subst_of gamma_list;
           } in Just (map (\ i -> gamma . rename_many i)
                        (List.upt Arith.zero_nat (List.size_list sls)),
                       gamma . ren_l);
       });

rename_many ::
  forall a. (Fresh.Infinite a) => RenamingN.RenamingN a -> Arith.Nat -> a -> a;
rename_many ren i = (\ v -> RenamingN.rename_many ren (i, v));

mgu_vd_list ::
  forall a b.
    (Fresh.Infinite a, Eq a,
      Eq b) => RenamingN.RenamingN a ->
                 [(Term.Term b a, Term.Term b a)] ->
                   Maybe ([a -> Term.Term b a], a -> Term.Term b a);
mgu_vd_list ren =
  mgu_var_disjoint_list_generic (rename_many ren) (RenamingN.rename_single ren);

}
