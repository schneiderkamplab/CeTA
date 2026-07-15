{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Tree_Automata_Det(ps_ta) where {

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
import qualified Tree_Automata_Det_Impl;
import qualified While_Combinator;
import qualified HOL;
import qualified Phantom_Type;
import qualified Term_Rewriting;
import qualified Arith;

ps_ta ::
  forall a b.
    (Arith.Card_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Eq a, Arith.Set_impl a, Arith.Ceq b, Arith.Ccompare b, Eq b,
      Arith.Set_impl b) => Term_Rewriting.Ta_ext a b () ->
                             Term_Rewriting.Ta_ext (Arith.Set a) b ();
ps_ta ta =
  let {
    eps = Term_Rewriting.ta_eps ta;
    rules = Term_Rewriting.ta_rules ta;
  } in (if Arith.finite eps && Arith.finite rules
         then let {
                meps = Term_Rewriting.memo_rtrancl eps;
                parts =
                  Tree_Automata_Det_Impl.sym_parts
                    (Arith.filtera
                      (\ r -> not (null (Term_Rewriting.r_lhs_states r)))
                      rules);
                qinit = Tree_Automata_Det_Impl.ps_states_nil_impl meps rules;
                q = fst (While_Combinator.while
                          (\ (qold, qnew) -> not (Arith.less_eq_set qnew qold))
                          (\ (_, qnew) ->
                            (qnew,
                              Arith.sup_set qinit
                                (Tree_Automata_Det_Impl.ps_states_cons_impl meps
                                  parts rules qnew)))
                          (Arith.set_empty
                             (Phantom_Type.of_phantom Arith.set_impl_set),
                            qinit));
                final =
                  Arith.filtera
                    (\ qa ->
                      not (Arith.is_empty
                            (Arith.inf_set qa (Term_Rewriting.ta_final ta))))
                    q;
                rulesa =
                  Arith.sup_set
                    (Tree_Automata_Det_Impl.ps_rules_nil_impl meps rules)
                    (Tree_Automata_Det_Impl.ps_rules_cons_impl meps parts rules
                      q);
              } in Term_Rewriting.Ta_ext final rulesa
                     (Arith.set_empty
                       (Phantom_Type.of_phantom
                         (Arith.set_impl_prod ::
                           Phantom_Type.Phantom (Arith.Set a, Arith.Set a)
                             Arith.Set_impla)))
                     ()
         else ps_ta ta);

}
