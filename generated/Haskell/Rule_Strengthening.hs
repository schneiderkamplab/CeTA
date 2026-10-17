{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Rule_Strengthening(rule_strengthening_tt) where {

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
import qualified Termination_Problem_Spec;
import qualified Sum_Type;
import qualified Mapping;
import qualified Arith;
import qualified Term_Rewriting;

rule_strengthens ::
  forall a b.
    (Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => [(Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b)] ->
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)] ->
                                     Bool;
rule_strengthens r s =
  all (\ (l, a) -> Arith.membera (Term_Rewriting.rewrite s l) a) r;

rule_strengthening_tt ::
  forall a b c.
    (Eq b, Term_Rewriting.Showl b, Arith.Ccompare c, Eq c,
      Mapping.Mapping_impl c,
      Term_Rewriting.Showl c) => Termination_Problem_Spec.Tp_ops_ext a b c () ->
                                   [(Term_Rewriting.Term b c,
                                      Term_Rewriting.Term b c)] ->
                                     a -> Sum_Type.Sum (String -> String) a;
rule_strengthening_tt i s tp =
  (case Error_Monad.bind
          (Check_Monad.check (null (Termination_Problem_Spec.q i tp))
            (Term_Rewriting.showsl_lit "rule strengthening requires empty Q"))
          (\ _ ->
            Error_Monad.bind
              (Check_Monad.check (null (Termination_Problem_Spec.rw i tp))
                (Term_Rewriting.showsl_lit
                  "rule strengthening requires no weak rules"))
              (\ _ ->
                Check_Monad.check
                  (rule_strengthens (Termination_Problem_Spec.r i tp) s)
                  (Term_Rewriting.showsl_lit
                    "an original rule is not a rewrite step of the stronger system")))
    of {
    Sum_Type.Inl a -> Sum_Type.Inl a;
    Sum_Type.Inr _ ->
      Sum_Type.Inr (Termination_Problem_Spec.mk i False [] s []);
  });

}
