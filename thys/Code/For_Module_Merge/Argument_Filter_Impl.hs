{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Argument_Filter_Impl(argument_filter_tt) where {

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
import qualified Option;
import qualified Shows_Literal;
import qualified Defaults;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified HOL;
import qualified Termination_Problem_Spec;
import qualified Argument_Filter;
import qualified Sum_Type;
import qualified Term;
import qualified Arith;
import qualified Collection_Order;
import qualified Compare;
import qualified Set_Impl;
import qualified Collection_Eq;

argument_filter_tt ::
  forall a b c.
    (Collection_Eq.Ceq b, Collection_Order.Ccompare b, Compare.Compare_order b,
      Set_Impl.Set_impl b) => Termination_Problem_Spec.Tp_ops_ext a b c () ->
                                [((b, Arith.Nat), Argument_Filter.Af_entry)] ->
                                  a -> Sum_Type.Sum (String -> String) a;
argument_filter_tt i pi tp =
  (case Argument_Filter.afs_of pi of {
    Nothing ->
      Sum_Type.Inl (Shows_Literal.showsl_lit "invalid argument filter");
    Just af ->
      Error_Monad.bind
        (Check_Monad.check (Argument_Filter.permutation_afs af)
          (Shows_Literal.showsl_lit "argument filter is not a permutation"))
        (\ _ ->
          let {
            pia = Argument_Filter.af_rules af;
          } in Sum_Type.Inr
                 (Termination_Problem_Spec.mk i Defaults.default_nfs_trs []
                   (pia (Termination_Problem_Spec.r i tp))
                   (pia (Termination_Problem_Spec.rw i tp))));
  });

}
