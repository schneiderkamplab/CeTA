{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Usable_Rules_NJ_Impl(usable_rules_reach_impl) where {

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
import qualified Inductive_Set_Impl;
import qualified Tcap_Impl;
import qualified Term_Impl;
import qualified Product_Type;
import qualified HOL;
import qualified Term;
import qualified Set;
import qualified Collection_Order;
import qualified Collection_Enum;
import qualified Set_Impl;
import qualified Collection_Eq;

usable_rules_reach_U0_impl ::
  forall a b.
    (Eq a,
      Eq b) => [(Term.Term a b, Term.Term a b)] ->
                 Term.Term a b -> [(Term.Term a b, Term.Term a b)];
usable_rules_reach_U0_impl r t =
  Inductive_Set_Impl.inductive_set_impl r
    (\ ta (l, _) ->
      Term.is_Var l ||
        any (\ u ->
              not (Term.is_Var u) && Tcap_Impl.match_tcap_below_impl l r u)
          (Term_Impl.supteq_list ta))
    (\ lr -> [snd lr]) [t];

usable_rules_reach_impl ::
  forall a b.
    (Eq a, Collection_Enum.Cenum b, Collection_Eq.Ceq b,
      Collection_Order.Ccompare b, Eq b,
      Set_Impl.Set_impl b) => [(Term.Term a b, Term.Term a b)] ->
                                Term.Term a b ->
                                  [(Term.Term a b, Term.Term a b)];
usable_rules_reach_impl r t =
  let {
    u0t = usable_rules_reach_U0_impl r t;
  } in (if all (\ (l, ra) ->
                 Set.less_eq_set (Term.vars_term ra) (Term.vars_term l))
             u0t
         then u0t else r);

}
