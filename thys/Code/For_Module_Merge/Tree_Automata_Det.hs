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
import qualified Tree_Automata_Autoref_Setup;
import qualified Tree_Automata_Det_Impl;
import qualified Product_Type;
import qualified While_Combinator;
import qualified Finite_Set;
import qualified HOL;
import qualified Tree_Automata;
import qualified Phantom_Type;
import qualified Arith;
import qualified Container_Setup;
import qualified Cardinality;
import qualified Collection_Order;
import qualified Collection_Enum;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Set;

ps_ta ::
  forall a b.
    (Cardinality.Card_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Eq a, Set_Impl.Set_impl a,
      Collection_Eq.Ceq b, Collection_Order.Ccompare b, Eq b,
      Set_Impl.Set_impl b) => Tree_Automata.Ta_ext a b () ->
                                Tree_Automata.Ta_ext (Set.Set a) b ();
ps_ta ta =
  let {
    eps = Tree_Automata.ta_eps ta;
    rules = Tree_Automata.ta_rules ta;
  } in (if Finite_Set.finite eps && Finite_Set.finite rules
         then let {
                meps = Tree_Automata_Autoref_Setup.memo_rtrancl eps;
                parts =
                  Tree_Automata_Det_Impl.sym_parts
                    (Set.filtera
                      (\ r -> not (null (Tree_Automata.r_lhs_states r))) rules);
                qinit = Tree_Automata_Det_Impl.ps_states_nil_impl meps rules;
                q = fst (While_Combinator.while
                          (\ (qold, qnew) -> not (Set.less_eq_set qnew qold))
                          (\ (_, qnew) ->
                            (qnew,
                              Set.sup_set qinit
                                (Tree_Automata_Det_Impl.ps_states_cons_impl meps
                                  parts rules qnew)))
                          (Set_Impl.set_empty
                             (Phantom_Type.of_phantom Set_Impl.set_impl_set),
                            qinit));
                final =
                  Set.filtera
                    (\ qa ->
                      not (Set.is_empty
                            (Set.inf_set qa (Tree_Automata.ta_final ta))))
                    q;
                rulesa =
                  Set.sup_set
                    (Tree_Automata_Det_Impl.ps_rules_nil_impl meps rules)
                    (Tree_Automata_Det_Impl.ps_rules_cons_impl meps parts rules
                      q);
              } in Tree_Automata.Ta_ext final rulesa
                     (Set_Impl.set_empty
                       (Phantom_Type.of_phantom
                         (Set_Impl.set_impl_prod ::
                           Phantom_Type.Phantom (Set.Set a, Set.Set a)
                             Set_Impl.Set_impla)))
                     ()
         else ps_ta ta);

}
