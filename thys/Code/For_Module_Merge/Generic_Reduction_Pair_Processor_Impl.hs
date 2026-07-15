{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Generic_Reduction_Pair_Processor_Impl(generic_mono_ur_redpair_proc,
 generic_ur_af_redtriple_proc, generic_ur_af_root_redtriple_proc)
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
import qualified Q_Restricted_Rewriting_Impl;
import qualified Term_Impl;
import qualified Generic_Usable_Rules_Impl;
import qualified Product_Type;
import qualified Innermost_Usable_Rules_Impl;
import qualified Usable_Rules_Impl;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Dependency_Pair_Problem_Spec;
import qualified Term_Order_Impl;
import qualified Sum_Type;
import qualified Set_Impl;
import qualified Compare;
import qualified Str;
import qualified Shows_Literal;
import qualified Compare_Instances;
import qualified Option;
import qualified List;
import qualified HOL;
import qualified Term;
import qualified Set;
import qualified Arith;
import qualified Collection_Order;
import qualified Collection_Eq;

root_aft_to_entry ::
  forall a b c.
    a -> Term.Term b c ->
           ((b, Arith.Nat) -> Set.Set Arith.Nat) -> [(a, Term.Term b c)];
root_aft_to_entry s t pi =
  let {
    rt = Option.the (Term.root t);
    pi_t = pi rt;
    ts = Term.args t;
  } in List.map_filter
         (\ x ->
           (if Set.member x pi_t then Just (s, List.nth ts x) else Nothing))
         (List.upt Arith.zero_nat (snd rt));

generic_mono_ur_redpair_proc ::
  forall a b.
    (Collection_Eq.Ceq b, Collection_Order.Ccompare b, Compare.Compare_order b,
      Eq b, Set_Impl.Set_impl b,
      Shows_Literal.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b
                                  [Str.Char] () ->
                                  Term_Order_Impl.Rel_impl_ext b [Str.Char]
                                    () ->
                                    [(Term.Term b [Str.Char],
                                       Term.Term b [Str.Char])] ->
                                      [(Term.Term b [Str.Char],
 Term.Term b [Str.Char])] ->
[(Term.Term b [Str.Char], Term.Term b [Str.Char])] ->
  a -> Sum_Type.Sum (String -> String) a;
generic_mono_ur_redpair_proc i rp premove rremove ur dpp =
  (if Dependency_Pair_Problem_Spec.nFQ_subset_NF_rules i dpp
    then Innermost_Usable_Rules_Impl.mono_inn_usable_rules_ce_proc i rp premove
           rremove ur dpp
    else Error_Monad.bind
           (Check_Monad.check (Dependency_Pair_Problem_Spec.minimal i dpp)
             (Shows_Literal.showsl_lit
               "minimality or innermost required for mon. red. pair proc. with usable rules"))
           (\ _ ->
             Usable_Rules_Impl.mono_ur_redpair_proc i rp premove rremove ur
               dpp));

generic_ur_af_redtriple_proc ::
  forall a b.
    (Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b
                                  [Str.Char] () ->
                                  Term_Order_Impl.Rel_impl_ext b [Str.Char]
                                    () ->
                                    Maybe [(Term.Term b [Str.Char],
     Term.Term b [Str.Char])] ->
                                      [(Term.Term b [Str.Char],
 Term.Term b [Str.Char])] ->
a -> Sum_Type.Sum (String -> String) a;
generic_ur_af_redtriple_proc i rp u_opt premove dpp =
  (case Error_Monad.catch_error
          (Error_Monad.bind (Term_Order_Impl.rel_impl_redtriple rp)
            (\ _ ->
              (case Dependency_Pair_Problem_Spec.split_pairs i dpp premove of {
                (ps, pns) ->
                  let {
                    p = Dependency_Pair_Problem_Spec.pairs i dpp;
                  } in Error_Monad.bind
                         (Generic_Usable_Rules_Impl.smart_usable_rules_checker_impl
                           i dpp
                           (Error_Monad.isOK (Term_Order_Impl.ce_compat rp))
                           (Term_Order_Impl.af rp) u_opt p)
                         (\ u ->
                           Error_Monad.bind
                             (Error_Monad.catch_error
                               (Term_Order_Impl.rel_impl_ns rp u)
                               (\ x ->
                                 Sum_Type.Inl
                                   (Shows_Literal.showsl_lit
                                      "problem when orienting (usable) rules\n" .
                                     x)))
                             (\ _ ->
                               Error_Monad.bind
                                 (Error_Monad.catch_error
                                   (Term_Order_Impl.rel_impl_nst rp pns)
                                   (\ x ->
                                     Sum_Type.Inl
                                       (Shows_Literal.showsl_lit
  "problem when orienting DPs\n" .
 x)))
                                 (\ _ ->
                                   Error_Monad.catch_error
                                     (Term_Order_Impl.rel_impl_s rp ps)
                                     (\ x ->
                                       Sum_Type.Inl
 (Shows_Literal.showsl_lit "problem when orienting DPs\n" . x)))));
              })))
          (\ x ->
            Sum_Type.Inl
              (((Shows_Literal.showsl_lit
                   "could not apply the generic reduction pair processor with the following\n" .
                  Term_Order_Impl.desc rp) .
                 Shows_Literal.showsl_literal "\n") .
                x))
    of {
    Sum_Type.Inl a -> Sum_Type.Inl a;
    Sum_Type.Inr _ ->
      Sum_Type.Inr
        (Dependency_Pair_Problem_Spec.delete_P_Pw i dpp premove premove);
  });

generic_ur_af_root_redtriple_proc ::
  forall a b.
    (Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b
                                  [Str.Char] () ->
                                  Term_Order_Impl.Rel_impl_ext b [Str.Char]
                                    () ->
                                    Maybe [(Term.Term b [Str.Char],
     Term.Term b [Str.Char])] ->
                                      [(Term.Term b [Str.Char],
 Term.Term b [Str.Char])] ->
a -> Sum_Type.Sum (String -> String) a;
generic_ur_af_root_redtriple_proc i rp u_opt premove dpp =
  (case Error_Monad.catch_error
          (Error_Monad.bind (Term_Order_Impl.rel_impl_root_redtriple rp)
            (\ _ ->
              (case Dependency_Pair_Problem_Spec.split_pairs i dpp premove of {
                (ps, pns) ->
                  let {
                    p = Dependency_Pair_Problem_Spec.pairs i dpp;
                    pi = Term_Order_Impl.af rp;
                    pia = Term_Order_Impl.top_af rp;
                    is_def =
                      (\ fn ->
                        not (null (Dependency_Pair_Problem_Spec.rules_map i dpp
                                    fn)));
                  } in Error_Monad.bind
                         (Error_Monad.catch_error
                           (Error_Monad.forallM
                             (\ (l, r) ->
                               Error_Monad.bind (Term_Impl.check_no_var l)
                                 (\ _ ->
                                   Error_Monad.bind (Term_Impl.check_no_var r)
                                     (\ _ ->
                                       Q_Restricted_Rewriting_Impl.check_no_defined_root
 is_def r)))
                             p)
                           (\ x -> Sum_Type.Inl (snd x)))
                         (\ _ ->
                           Error_Monad.bind
                             (Error_Monad.catch_error
                               (Error_Monad.forallM
                                 (\ (l, _) -> Term_Impl.check_no_var l)
                                 (Dependency_Pair_Problem_Spec.rules i dpp))
                               (\ x -> Sum_Type.Inl (snd x)))
                             (\ _ ->
                               Error_Monad.bind
                                 (Generic_Usable_Rules_Impl.smart_usable_rules_checker_impl
                                   i dpp
                                   (Error_Monad.isOK
                                     (Term_Order_Impl.ce_compat rp))
                                   pi u_opt
                                   (concatMap
                                     (\ (s, t) -> root_aft_to_entry s t pia) p))
                                 (\ u ->
                                   Error_Monad.bind
                                     (Error_Monad.catch_error
                                       (Term_Order_Impl.rel_impl_ns rp u)
                                       (\ x ->
 Sum_Type.Inl
   (Shows_Literal.showsl_lit "problem when orienting (usable) rules\n" . x)))
                                     (\ _ ->
                                       Error_Monad.bind
 (Error_Monad.catch_error (Term_Order_Impl.rel_impl_nst rp pns)
   (\ x ->
     Sum_Type.Inl
       (Shows_Literal.showsl_lit "problem when orienting DPs\n" . x)))
 (\ _ ->
   Error_Monad.catch_error (Term_Order_Impl.rel_impl_s rp ps)
     (\ x ->
       Sum_Type.Inl
         (Shows_Literal.showsl_lit "problem when orienting DPs\n" . x)))))));
              })))
          (\ x ->
            Sum_Type.Inl
              (((Shows_Literal.showsl_lit
                   "could not apply the generic root reduction pair processor with the following\n" .
                  Term_Order_Impl.desc rp) .
                 Shows_Literal.showsl_literal "\n") .
                x))
    of {
    Sum_Type.Inl a -> Sum_Type.Inl a;
    Sum_Type.Inr _ ->
      Sum_Type.Inr
        (Dependency_Pair_Problem_Spec.delete_P_Pw i dpp premove premove);
  });

}
