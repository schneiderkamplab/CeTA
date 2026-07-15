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
import qualified Option;
import qualified Icap;
import qualified Dependency_Pair_Problem_Spec;
import qualified Termination_Problem_Spec;
import qualified Q_Restricted_Rewriting_Impl;
import qualified Term_More;
import qualified Map_Choice;
import qualified HOL;
import qualified Sum_Type;
import qualified Term;
import qualified Compare_Instances;
import qualified Str;
import qualified Compare_Order_Instances;

icap_impl_gen ::
  forall a.
    (Eq a) => Bool ->
                (Term.Term a [Str.Char] -> Bool) ->
                  [Term.Term a [Str.Char]] ->
                    [Term.Term a [Str.Char]] ->
                      ([Str.Char] -> Bool) ->
                        Term.Term a [Str.Char] ->
                          Term.Term a (Sum_Type.Sum () [Str.Char]);
icap_impl_gen nf isQnf ls s sx (Term.Var x) =
  (if nf && sx x then Term.Var (Sum_Type.Inr x)
    else Term.Var (Sum_Type.Inl ()));
icap_impl_gen nf isQnf ls s sx (Term.Fun f ts) =
  let {
    t = Term.Fun f (map (icap_impl_gen nf isQnf ls s sx) ts);
  } in (if any (\ l ->
                 (case Icap.mgu_class t l of {
                   Nothing -> False;
                   Just mu ->
                     all (\ u ->
                           isQnf (Term.eval_term Term.Fun
                                   (Term.map_term (\ x -> x)
                                     (\ a -> Str.char_0x79 : a) u)
                                   mu))
                       (Term.args l) &&
                       all (\ u -> isQnf (Term.eval_term Term.Fun u mu)) s;
                 }))
             ls
         then Term.Var (Sum_Type.Inl ()) else t);

icap_impl ::
  forall a.
    (Eq a) => (Term.Term a [Str.Char] -> Bool) ->
                [(Term.Term a [Str.Char], Term.Term a [Str.Char])] ->
                  [Term.Term a [Str.Char]] ->
                    Term.Term a [Str.Char] ->
                      Term.Term a (Sum_Type.Sum () [Str.Char]);
icap_impl isnf r =
  let {
    ls = map fst r;
    nf = Q_Restricted_Rewriting_Impl.is_NF_subset isnf ls;
    ic = icap_impl_gen nf isnf ls;
  } in (\ s ->
         let {
           sa = map (Term.map_term (\ x -> x) (\ a -> Str.char_0x78 : a)) s;
           sx = Map_Choice.ceta_set_of (concatMap Term_More.vars_term_list sa);
         } in (\ t ->
                ic sa sx
                  (Term.map_term (\ x -> x) (\ a -> Str.char_0x78 : a) t)));

icap_impl_tp ::
  forall a b.
    (Eq b) => Termination_Problem_Spec.Tp_ops_ext a b [Str.Char] () ->
                a -> [Term.Term b [Str.Char]] ->
                       Term.Term b [Str.Char] ->
                         Term.Term b (Sum_Type.Sum () [Str.Char]);
icap_impl_tp i d =
  let {
    qr = Termination_Problem_Spec.nFQ_subset_NF_rules i d;
    qnf = Termination_Problem_Spec.is_QNF i d;
    r = Termination_Problem_Spec.rules i d;
    ic = icap_impl_gen qr qnf (map fst r);
  } in (\ s ->
         let {
           a = Map_Choice.ceta_set_of (concatMap Term_More.vars_term_list s);
         } in ic s a);

icap_impl_dpp ::
  forall a b.
    (Eq b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b [Str.Char] () ->
                a -> [Term.Term b [Str.Char]] ->
                       Term.Term b [Str.Char] ->
                         Term.Term b (Sum_Type.Sum () [Str.Char]);
icap_impl_dpp i d =
  let {
    qr = Dependency_Pair_Problem_Spec.nFQ_subset_NF_rules i d;
    qnf = Dependency_Pair_Problem_Spec.is_QNF i d;
    r = Dependency_Pair_Problem_Spec.rules i d;
    ic = icap_impl_gen qr qnf (map fst r);
  } in (\ s ->
         let {
           a = Map_Choice.ceta_set_of (concatMap Term_More.vars_term_list s);
         } in ic s a);

icap_impl_dpp_mv ::
  forall a b.
    (Eq b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b [Str.Char] () ->
                a -> [Term.Term b [Str.Char]] ->
                       Term.Term b [Str.Char] ->
                         Term.Term b (Sum_Type.Sum () [Str.Char]);
icap_impl_dpp_mv i d =
  let {
    qr = Dependency_Pair_Problem_Spec.nFQ_subset_NF_rules i d;
    qnf = Dependency_Pair_Problem_Spec.is_QNF i d;
    r = Dependency_Pair_Problem_Spec.rules i d;
    ic = icap_impl_gen qr qnf (map fst r);
  } in (\ s ->
         let {
           sa = map (Term.map_term (\ x -> x) (\ a -> Str.char_0x78 : a)) s;
           sx = Map_Choice.ceta_set_of (concatMap Term_More.vars_term_list sa);
         } in (\ t ->
                ic sa sx
                  (Term.map_term (\ x -> x) (\ a -> Str.char_0x78 : a) t)));

}
