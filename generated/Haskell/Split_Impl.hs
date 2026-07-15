{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Split_Impl(split_tt, split_proc) where {

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
import qualified Dependency_Pair_Problem_Spec;
import qualified Arith;
import qualified HOL;
import qualified Termination_Problem_Spec;
import qualified Term_Rewriting;

split_tt ::
  forall a b c.
    (Term_Rewriting.Showl b,
      Term_Rewriting.Showl c) => Termination_Problem_Spec.Tp_ops_ext a b c () ->
                                   a -> [(Term_Rewriting.Term b c,
   Term_Rewriting.Term b c)] ->
  (a, a);
split_tt i tp r_remove =
  (case Termination_Problem_Spec.split_rules i tp r_remove of {
    (r, rw) ->
      let {
        tp1 = Termination_Problem_Spec.mk i (Termination_Problem_Spec.nfs i tp)
                (Termination_Problem_Spec.q i tp) r rw;
        a = Termination_Problem_Spec.delete_R_Rw i tp r_remove r_remove;
      } in (tp1, a);
  });

split_proc ::
  forall a b c.
    (Term_Rewriting.Showl b,
      Term_Rewriting.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b c
                                   () ->
                                   a -> [(Term_Rewriting.Term b c,
   Term_Rewriting.Term b c)] ->
  [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] -> (a, a);
split_proc i d p_remove r_remove =
  (case Dependency_Pair_Problem_Spec.split_pairs i d p_remove of {
    (p, pw) ->
      (case Dependency_Pair_Problem_Spec.split_rules i d r_remove of {
        (r, rw) ->
          let {
            dpp1 =
              Dependency_Pair_Problem_Spec.mk i
                (Dependency_Pair_Problem_Spec.nfs i d)
                (Dependency_Pair_Problem_Spec.minimal i d) p pw
                (Dependency_Pair_Problem_Spec.q i d) r rw;
            a = Dependency_Pair_Problem_Spec.delete_R_Rw i
                  (Dependency_Pair_Problem_Spec.delete_P_Pw i d p_remove
                    p_remove)
                  r_remove r_remove;
          } in (dpp1, a);
      });
  });

}
