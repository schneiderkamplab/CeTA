{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Icap_Impl(icap_impl, icap_impl_tp, icap_impl_dpp, icap_impl_dpp_mv)
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
import qualified Icap;
import qualified Dependency_Pair_Problem_Spec;
import qualified Termination_Problem_Spec;
import qualified Q_Restricted_Rewriting_Impl;
import qualified Map_Choice;
import qualified HOL;
import qualified Sum_Type;
import qualified Term_Rewriting;
import qualified Arith;
import qualified Compare_Order_Instances;

icap_impl_gen ::
  forall a.
    (Eq a) => Bool ->
                (Term_Rewriting.Term a [Arith.Char] -> Bool) ->
                  [Term_Rewriting.Term a [Arith.Char]] ->
                    [Term_Rewriting.Term a [Arith.Char]] ->
                      ([Arith.Char] -> Bool) ->
                        Term_Rewriting.Term a [Arith.Char] ->
                          Term_Rewriting.Term a (Sum_Type.Sum () [Arith.Char]);
icap_impl_gen nf isQnf ls s sx (Term_Rewriting.Var x) =
  (if nf && sx x then Term_Rewriting.Var (Sum_Type.Inr x)
    else Term_Rewriting.Var (Sum_Type.Inl ()));
icap_impl_gen nf isQnf ls s sx (Term_Rewriting.Fun f ts) =
  let {
    t = Term_Rewriting.Fun f (map (icap_impl_gen nf isQnf ls s sx) ts);
  } in (if any (\ l ->
                 (case Icap.mgu_class t l of {
                   Nothing -> False;
                   Just mu ->
                     all (\ u ->
                           isQnf (Term_Rewriting.eval_term Term_Rewriting.Fun
                                   (Term_Rewriting.map_term (\ x -> x)
                                     (\ a -> Arith.char_0x79 : a) u)
                                   mu))
                       (Term_Rewriting.args l) &&
                       all (\ u ->
                             isQnf (Term_Rewriting.eval_term Term_Rewriting.Fun
                                     u mu))
                         s;
                 }))
             ls
         then Term_Rewriting.Var (Sum_Type.Inl ()) else t);

icap_impl ::
  forall a.
    (Eq a) => (Term_Rewriting.Term a [Arith.Char] -> Bool) ->
                [(Term_Rewriting.Term a [Arith.Char],
                   Term_Rewriting.Term a [Arith.Char])] ->
                  [Term_Rewriting.Term a [Arith.Char]] ->
                    Term_Rewriting.Term a [Arith.Char] ->
                      Term_Rewriting.Term a (Sum_Type.Sum () [Arith.Char]);
icap_impl isnf r =
  let {
    ls = map fst r;
    nf = Q_Restricted_Rewriting_Impl.is_NF_subset isnf ls;
    ic = icap_impl_gen nf isnf ls;
  } in (\ s ->
         let {
           sa = map (Term_Rewriting.map_term (\ x -> x)
                      (\ a -> Arith.char_0x78 : a))
                  s;
           sx = Map_Choice.ceta_set_of
                  (concatMap Term_Rewriting.vars_term_list sa);
         } in (\ t ->
                ic sa sx
                  (Term_Rewriting.map_term (\ x -> x)
                    (\ a -> Arith.char_0x78 : a) t)));

icap_impl_tp ::
  forall a b.
    (Eq b) => Termination_Problem_Spec.Tp_ops_ext a b [Arith.Char] () ->
                a -> [Term_Rewriting.Term b [Arith.Char]] ->
                       Term_Rewriting.Term b [Arith.Char] ->
                         Term_Rewriting.Term b (Sum_Type.Sum () [Arith.Char]);
icap_impl_tp i d =
  let {
    qr = Termination_Problem_Spec.nFQ_subset_NF_rules i d;
    qnf = Termination_Problem_Spec.is_QNF i d;
    r = Termination_Problem_Spec.rules i d;
    ic = icap_impl_gen qr qnf (map fst r);
  } in (\ s ->
         let {
           a = Map_Choice.ceta_set_of
                 (concatMap Term_Rewriting.vars_term_list s);
         } in ic s a);

icap_impl_dpp ::
  forall a b.
    (Eq b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b [Arith.Char] () ->
                a -> [Term_Rewriting.Term b [Arith.Char]] ->
                       Term_Rewriting.Term b [Arith.Char] ->
                         Term_Rewriting.Term b (Sum_Type.Sum () [Arith.Char]);
icap_impl_dpp i d =
  let {
    qr = Dependency_Pair_Problem_Spec.nFQ_subset_NF_rules i d;
    qnf = Dependency_Pair_Problem_Spec.is_QNF i d;
    r = Dependency_Pair_Problem_Spec.rules i d;
    ic = icap_impl_gen qr qnf (map fst r);
  } in (\ s ->
         let {
           a = Map_Choice.ceta_set_of
                 (concatMap Term_Rewriting.vars_term_list s);
         } in ic s a);

icap_impl_dpp_mv ::
  forall a b.
    (Eq b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b [Arith.Char] () ->
                a -> [Term_Rewriting.Term b [Arith.Char]] ->
                       Term_Rewriting.Term b [Arith.Char] ->
                         Term_Rewriting.Term b (Sum_Type.Sum () [Arith.Char]);
icap_impl_dpp_mv i d =
  let {
    qr = Dependency_Pair_Problem_Spec.nFQ_subset_NF_rules i d;
    qnf = Dependency_Pair_Problem_Spec.is_QNF i d;
    r = Dependency_Pair_Problem_Spec.rules i d;
    ic = icap_impl_gen qr qnf (map fst r);
  } in (\ s ->
         let {
           sa = map (Term_Rewriting.map_term (\ x -> x)
                      (\ a -> Arith.char_0x78 : a))
                  s;
           sx = Map_Choice.ceta_set_of
                  (concatMap Term_Rewriting.vars_term_list sa);
         } in (\ t ->
                ic sa sx
                  (Term_Rewriting.map_term (\ x -> x)
                    (\ a -> Arith.char_0x78 : a) t)));

}
