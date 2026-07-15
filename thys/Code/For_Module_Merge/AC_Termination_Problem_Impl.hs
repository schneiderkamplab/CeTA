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
import qualified Product_Type;
import qualified Missing_List;
import qualified List;
import qualified AC_Termination_Problem_Spec;
import qualified Set;
import qualified Compare;
import qualified Collection_Order;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Container_Setup;
import qualified Compare_Instances;
import qualified HOL;
import qualified Str;
import qualified Term;

a_trs_impl ::
  forall a. [a] -> [(Term.Term a [Str.Char], Term.Term a [Str.Char])];
a_trs_impl a =
  let {
    x = Term.Var [Str.char_0x78];
    y = Term.Var [Str.char_0x79];
    z = Term.Var [Str.char_0x7A];
  } in map (\ f ->
             (Term.Fun f [Term.Fun f [x, y], z],
               Term.Fun f [x, Term.Fun f [y, z]]))
         a ++
         map (\ f ->
               (Term.Fun f [x, Term.Fun f [y, z]],
                 Term.Fun f [Term.Fun f [x, y], z]))
           a;

c_rules_impl ::
  forall a. [a] -> [(Term.Term a [Str.Char], Term.Term a [Str.Char])];
c_rules_impl c = let {
                   x = Term.Var [Str.char_0x78];
                   y = Term.Var [Str.char_0x79];
                 } in map (\ f -> (Term.Fun f [x, y], Term.Fun f [y, x])) c;

aC_trs_impl ::
  forall a. [a] -> [a] -> [(Term.Term a [Str.Char], Term.Term a [Str.Char])];
aC_trs_impl a c = a_trs_impl a ++ c_rules_impl c;

ac_tp_list_impl ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Compare.Compare a, Eq a,
      Set_Impl.Set_impl a) => AC_Termination_Problem_Spec.Ac_tp_ops_ext
                                ([(Term.Term a [Str.Char],
                                    Term.Term a [Str.Char])],
                                  ([a], [a]))
                                a [Str.Char] ();
ac_tp_list_impl =
  AC_Termination_Problem_Spec.Ac_tp_ops_ext
    (\ (r, (a, c)) -> (List.set r, (List.set a, List.set c)))
    (\ (r, (_, _)) -> r) (\ (_, (a, _)) -> a) (\ (_, (_, c)) -> c)
    (\ r a c -> (r, (a, c)))
    (\ (r, (a, c)) dr -> (Missing_List.list_diff r dr, (a, c)))
    (\ (_, (a, b)) -> aC_trs_impl a b) ();

}
