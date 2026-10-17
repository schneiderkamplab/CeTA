{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Ceta(bind2, certify_proof) where {

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
import qualified AC_Termination_Problem_Impl;
import qualified CPF_Parser;
import qualified AC_Dependency_Pair_Problem_Spec;
import qualified AC_Termination_Problem_Spec;
import qualified Dependency_Pair_Problem_Spec;
import qualified Termination_Problem_Spec;
import qualified AC_Dependency_Pair_Problem_Impl;
import qualified Dependency_Pair_Problem_Impl;
import qualified Termination_Problem_Impl;
import qualified Ceta_Problem_Spec;
import qualified Labelings;
import qualified Mapping;
import qualified Compare_Order_Instances;
import qualified Term_Rewriting;
import qualified Countable;
import qualified Check_Termination_Common;
import qualified Arith;
import qualified Proof_Checker;
import qualified Strict_Sum;
import qualified Sum_Type;

bind2 ::
  forall a b.
    Strict_Sum.Sum_bot a b ->
      (a -> Proof_Checker.Cert_result) ->
        (b -> Proof_Checker.Cert_result) -> Proof_Checker.Cert_result;
bind2 (Strict_Sum.Sumbot a) f g = (case a of {
                                    Sum_Type.Inl aa -> f aa;
                                    Sum_Type.Inr aa -> g aa;
                                  });

certify_proof ::
  Bool ->
    Maybe [Arith.Char] ->
      Maybe [Arith.Char] ->
        Maybe [Arith.Char] -> [Arith.Char] -> Proof_Checker.Cert_result;
certify_proof a inp_o prop_o answ_o prfs =
  bind2 (CPF_Parser.parse_combined_cert_problem inp_o prop_o answ_o prfs)
    Proof_Checker.Unsupported
    (\ (inp, (prop, (b, c))) ->
      Proof_Checker.certify_cert_problem Termination_Problem_Impl.tp_rbt_impl
        Dependency_Pair_Problem_Impl.dpp_rbt_impl
        AC_Termination_Problem_Impl.ac_tp_list_impl
        AC_Dependency_Pair_Problem_Impl.ac_dpp_rbt_impl a inp prop b c);

}
