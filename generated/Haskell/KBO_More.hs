{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module KBO_More(kbo_closure) where {

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
import qualified Lexicographic_Extension;
import qualified KBO;
import qualified Multiset;
import qualified Compare;
import qualified Arith;
import qualified Term_Rewriting;

kbo_closure ::
  forall a b.
    (Compare.Compare a, Eq a, Compare.Compare b,
      Eq b) => ((a, Arith.Nat) -> Arith.Nat) ->
                 Arith.Nat ->
                   ((a, Arith.Nat) -> Arith.Nat -> Arith.Nat) ->
                     (a -> Bool) ->
                       ((a, Arith.Nat) -> (a, Arith.Nat) -> Bool) ->
                         ((a, Arith.Nat) -> (a, Arith.Nat) -> Bool) ->
                           Arith.Set
                             (Term_Rewriting.Term a b,
                               Term_Rewriting.Term a b) ->
                             Term_Rewriting.Term a b ->
                               Term_Rewriting.Term a b -> (Bool, Bool);
kbo_closure w w0 scf least pr_strict pr_weak gt s t =
  (if Arith.member (s, t) gt then (True, True)
    else (if Multiset.subseteq_mset
               (Term_Rewriting.vars_term_ms (KBO.scf_term scf t))
               (Term_Rewriting.vars_term_ms (KBO.scf_term scf s)) &&
               Arith.less_eq_nat (KBO.weight w w0 scf t) (KBO.weight w w0 scf s)
           then (if Arith.less_nat (KBO.weight w w0 scf t)
                      (KBO.weight w w0 scf s)
                  then (True, True)
                  else (case s of {
                         Term_Rewriting.Var y ->
                           (False,
                             (case t of {
                               Term_Rewriting.Var x -> x == y;
                               Term_Rewriting.Fun g ts -> null ts && least g;
                             }));
                         Term_Rewriting.Fun f ss ->
                           (case t of {
                             Term_Rewriting.Var _ -> (True, True);
                             Term_Rewriting.Fun g ts ->
                               (if pr_strict (f, Arith.size_list ss)
                                     (g, Arith.size_list ts)
                                 then (True, True)
                                 else (if pr_weak (f, Arith.size_list ss)
    (g, Arith.size_list ts)
then Lexicographic_Extension.lex_ext_unbounded
       (kbo_closure w w0 scf least pr_strict pr_weak gt) ss ts
else (False, False)));
                           });
                       }))
           else (False, False)));

}
