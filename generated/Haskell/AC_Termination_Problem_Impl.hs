{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module AC_Termination_Problem_Impl(ac_tp_list_impl) where {

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
import qualified Missing_List;
import qualified AC_Termination_Problem_Spec;
import qualified Compare;
import qualified HOL;
import qualified Arith;
import qualified Term_Rewriting;

a_trs_impl ::
  forall a.
    [a] ->
      [(Term_Rewriting.Term a [Arith.Char],
         Term_Rewriting.Term a [Arith.Char])];
a_trs_impl a =
  let {
    x = Term_Rewriting.Var [Arith.char_0x78];
    y = Term_Rewriting.Var [Arith.char_0x79];
    z = Term_Rewriting.Var [Arith.char_0x7A];
  } in map (\ f ->
             (Term_Rewriting.Fun f [Term_Rewriting.Fun f [x, y], z],
               Term_Rewriting.Fun f [x, Term_Rewriting.Fun f [y, z]]))
         a ++
         map (\ f ->
               (Term_Rewriting.Fun f [x, Term_Rewriting.Fun f [y, z]],
                 Term_Rewriting.Fun f [Term_Rewriting.Fun f [x, y], z]))
           a;

c_rules_impl ::
  forall a.
    [a] ->
      [(Term_Rewriting.Term a [Arith.Char],
         Term_Rewriting.Term a [Arith.Char])];
c_rules_impl c =
  let {
    x = Term_Rewriting.Var [Arith.char_0x78];
    y = Term_Rewriting.Var [Arith.char_0x79];
  } in map (\ f -> (Term_Rewriting.Fun f [x, y], Term_Rewriting.Fun f [y, x]))
         c;

aC_trs_impl ::
  forall a.
    [a] ->
      [a] ->
        [(Term_Rewriting.Term a [Arith.Char],
           Term_Rewriting.Term a [Arith.Char])];
aC_trs_impl a c = a_trs_impl a ++ c_rules_impl c;

ac_tp_list_impl ::
  forall a.
    (Arith.Ceq a, Arith.Ccompare a, Compare.Compare a, Eq a,
      Arith.Set_impl a) => AC_Termination_Problem_Spec.Ac_tp_ops_ext
                             ([(Term_Rewriting.Term a [Arith.Char],
                                 Term_Rewriting.Term a [Arith.Char])],
                               ([a], [a]))
                             a [Arith.Char] ();
ac_tp_list_impl =
  AC_Termination_Problem_Spec.Ac_tp_ops_ext
    (\ (r, (a, c)) -> (Arith.set r, (Arith.set a, Arith.set c)))
    (\ (r, (_, _)) -> r) (\ (_, (a, _)) -> a) (\ (_, (_, c)) -> c)
    (\ r a c -> (r, (a, c)))
    (\ (r, (a, c)) dr -> (Missing_List.list_diff r dr, (a, c)))
    (\ (_, (a, b)) -> aC_trs_impl a b) ();

}
