{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Tcap_Dpp_Impl(tcapRM_dpp, tcapRM_ac_dpp, reverse_tcapRM_dpp,
                 reverse_tcapRM_ac_dpp)
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
import qualified AC_Dependency_Pair_Problem_Spec;
import qualified Tcap_Impl;
import qualified Dependency_Pair_Problem_Spec;
import qualified Ground_Context;
import qualified Term;
import qualified Arith;

tcapRM_dpp ::
  forall a b c.
    (Eq b,
      Eq c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b c () ->
                 a -> Term.Term b c -> Ground_Context.Gctxt b c;
tcapRM_dpp i dpp =
  Tcap_Impl.tcapRM (Dependency_Pair_Problem_Spec.rules_no_left_var i dpp)
    (Dependency_Pair_Problem_Spec.rules_map i dpp);

tcapRM_ac_dpp ::
  forall a b c.
    (Eq b,
      Eq c) => AC_Dependency_Pair_Problem_Spec.Ac_dpp_ops_ext a b c () ->
                 a -> Term.Term b c -> Ground_Context.Gctxt b c;
tcapRM_ac_dpp i dpp =
  Tcap_Impl.tcapRM (AC_Dependency_Pair_Problem_Spec.eq_rules_no_left_var i dpp)
    (AC_Dependency_Pair_Problem_Spec.eq_rules_map i dpp);

reverse_tcapRM_dpp ::
  forall a b c.
    (Eq b,
      Eq c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b c () ->
                 a -> Term.Term b c -> Ground_Context.Gctxt b c;
reverse_tcapRM_dpp i dpp =
  Tcap_Impl.tcapRM (Dependency_Pair_Problem_Spec.rules_non_collapsing i dpp)
    (Dependency_Pair_Problem_Spec.reverse_rules_map i dpp);

reverse_tcapRM_ac_dpp ::
  forall a b c.
    (Eq b,
      Eq c) => AC_Dependency_Pair_Problem_Spec.Ac_dpp_ops_ext a b c () ->
                 a -> Term.Term b c -> Ground_Context.Gctxt b c;
reverse_tcapRM_ac_dpp i dpp =
  Tcap_Impl.tcapRM
    (AC_Dependency_Pair_Problem_Spec.eq_rules_non_collapsing i dpp)
    (AC_Dependency_Pair_Problem_Spec.reverse_eq_rules_map i dpp);

}
