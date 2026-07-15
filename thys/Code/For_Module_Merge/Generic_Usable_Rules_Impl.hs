{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Generic_Usable_Rules_Impl(smart_usable_rules_checker_impl) where {

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
import qualified Innermost_Usable_Rules_Impl;
import qualified Usable_Rules_Impl;
import qualified Term_More;
import qualified Trs_Impl;
import qualified Product_Type;
import qualified Option;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified HOL;
import qualified Dependency_Pair_Problem_Spec;
import qualified Sum_Type;
import qualified Term;
import qualified Set;
import qualified Arith;
import qualified Compare;
import qualified Str;
import qualified Shows_Literal;

smart_usable_rules_checker_impl ::
  forall a b.
    (Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b
                                  [Str.Char] () ->
                                  a -> Bool ->
 ((b, Arith.Nat) -> Set.Set Arith.Nat) ->
   Maybe [(Term.Term b [Str.Char], Term.Term b [Str.Char])] ->
     [(Term.Term b [Str.Char], Term.Term b [Str.Char])] ->
       Sum_Type.Sum (String -> String)
         [(Term.Term b [Str.Char], Term.Term b [Str.Char])];
smart_usable_rules_checker_impl i d ce pi u_opt sts =
  let {
    nfs = Dependency_Pair_Problem_Spec.nfs i d;
    m = Dependency_Pair_Problem_Spec.minimal i d;
    wwf = Dependency_Pair_Problem_Spec.wwf_rules i d;
    qempty = Dependency_Pair_Problem_Spec.q_empty i d;
  } in (case u_opt of {
         Nothing -> Sum_Type.Inr (Dependency_Pair_Problem_Spec.rules i d);
         Just u ->
           (if Dependency_Pair_Problem_Spec.nFQ_subset_NF_rules i d &&
                 (nfs ||
                   Error_Monad.isOK (Trs_Impl.check_varcond_subset sts)) &&
                   (nfs || (m || wwf))
             then let {
                    urc = Innermost_Usable_Rules_Impl.is_ur_closed_af_impl_dpp_mv
                            i d pi u;
                    check_urc =
                      (\ s t ->
                        Check_Monad.check (urc s t)
                          ((Shows_Literal.showsl_lit "term " .
                             Term_More.showsl_terma t) .
                            Shows_Literal.showsl_lit
                              " is not closed under usable rules"));
                  } in Error_Monad.bind
                         (Error_Monad.catch_error
                           (Error_Monad.forallM (\ (s, a) -> check_urc [s] a)
                             sts)
                           (\ x -> Sum_Type.Inl (snd x)))
                         (\ _ ->
                           Error_Monad.bind
                             (Error_Monad.catch_error
                               (Error_Monad.forallM
                                 (\ (l, a) -> check_urc (Term.args l) a) u)
                               (\ x -> Sum_Type.Inl (snd x)))
                             (\ _ -> Sum_Type.Inr u))
             else Error_Monad.bind
                    (Check_Monad.check
                      (m && ce && (if nfs then qempty || wwf else True))
                      (Shows_Literal.showsl_lit
                        "minimality and ce-compatibility and well formedness required"))
                    (\ _ ->
                      Error_Monad.bind
                        (Error_Monad.catch_error
                          (Error_Monad.forallM
                            (\ (l, _) ->
                              Check_Monad.check (not (Term.is_Var l))
                                (Shows_Literal.showsl_lit
                                  "variables as lhss not allowed"))
                            (Dependency_Pair_Problem_Spec.rules i d))
                          (\ x -> Sum_Type.Inl (snd x)))
                        (\ _ ->
                          let {
                            rm = Dependency_Pair_Problem_Spec.rules_map i d;
                          } in Error_Monad.bind
                                 (Usable_Rules_Impl.check_ur_P_closed_rm_af rm u
                                   pi sts)
                                 (\ _ -> Sum_Type.Inr u))));
       });

}
