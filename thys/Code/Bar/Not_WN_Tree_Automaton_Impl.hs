{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Not_WN_Tree_Automaton_Impl(Not_wn_ta_prf(..), check_not_wn_ta_prf)
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
import qualified Termination_Problem_Spec;
import qualified Tree_Automata_NF;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Shows_Literal;
import qualified HOL;
import qualified Compare;
import qualified Arith;
import qualified Term_Rewriting;
import qualified Tree_Automata_Impl;

data Not_wn_ta_prf a b =
  Not_wn_ta_prf (Tree_Automata_Impl.Tree_automaton b a)
    (Tree_Automata_Impl.Ta_relation b);

check_trs_not_wn ::
  forall a b c.
    (Arith.Finite_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Compare.Compare_order a, HOL.Default a, Eq a, Arith.Set_impl a,
      Shows_Literal.Showl a, Arith.Ceq b, Arith.Ccompare b,
      Compare.Compare_order b, Eq b, Arith.Set_impl b, Shows_Literal.Showl b,
      Arith.Card_UNIV c, Arith.Cenum c, Arith.Ceq c, Arith.Cproper_interval c,
      Compare.Compare_order c, Eq c, Arith.Set_impl c,
      Shows_Literal.Showl c) => [(Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b)] ->
                                  Not_wn_ta_prf a c ->
                                    Sum_Type.Sum (String -> String) ();
check_trs_not_wn r (Not_wn_ta_prf ta rel) =
  Error_Monad.bind (Term_Rewriting.check_varcond_subset r)
    (\ _ ->
      Error_Monad.bind (Term_Rewriting.check_left_linear_trs r)
        (\ _ ->
          let {
            tA_trim = Term_Rewriting.trim_ta (Tree_Automata_Impl.ta_of_ta ta);
          } in Error_Monad.bind
                 (Check_Monad.check (not (Term_Rewriting.ta_empty tA_trim))
                   (Shows_Literal.showsl_lit "TA is empty"))
                 (\ _ ->
                   Error_Monad.bind
                     (Tree_Automata_Impl.tree_aut_trs_closed ta rel r)
                     (\ _ ->
                       Check_Monad.check
                         (not (Tree_Automata_NF.ta_contains_nf tA_trim
                                (Arith.set r)))
                         (Shows_Literal.showsl_lit
                           "TA accepts some normal form")))));

check_not_wn_ta_prf ::
  forall a b c d e.
    (Arith.Finite_UNIV b, Arith.Cenum b, Arith.Ceq b, Arith.Cproper_interval b,
      Compare.Compare_order b, HOL.Default b, Eq b, Arith.Set_impl b,
      Shows_Literal.Showl b, Arith.Ceq c, Arith.Ccompare c,
      Compare.Compare_order c, Eq c, Arith.Set_impl c, Shows_Literal.Showl c,
      Arith.Card_UNIV e, Arith.Cenum e, Arith.Ceq e, Arith.Cproper_interval e,
      Compare.Compare_order e, Eq e, Arith.Set_impl e,
      Shows_Literal.Showl e) => Termination_Problem_Spec.Tp_ops_ext a b c d ->
                                  a -> Not_wn_ta_prf b e ->
 Sum_Type.Sum (String -> String) ();
check_not_wn_ta_prf i tp prf =
  let {
    r = Termination_Problem_Spec.rules i tp;
  } in Error_Monad.bind
         (Check_Monad.check (null (Termination_Problem_Spec.q i tp))
           (Shows_Literal.showsl_lit
             "strategy is unsupported for tree automata based nontermination"))
         (\ _ -> check_trs_not_wn r prf);

}
