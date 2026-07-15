{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Critical_Pair_Closure_Impl(check_critical_pair_closing) where {

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
import qualified Rewrite_Relations_Impl;
import qualified Option;
import qualified List;
import qualified Critical_Pairs_Impl;
import qualified Term_More;
import qualified Product_Type;
import qualified Trs_Impl;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Renaming2;
import qualified Sum_Type;
import qualified Arith;
import qualified Mapping_Impl;
import qualified Collection_Order;
import qualified Shows_Literal;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Compare;
import qualified Fresh;
import qualified Term;

is_critical_pair_closing_cp ::
  forall a b.
    (Compare.Compare a, Eq a, Collection_Order.Ccompare b, Compare.Compare b,
      Eq b,
      Mapping_Impl.Mapping_impl b) => [(Term.Term a b, Term.Term a b)] ->
Arith.Nat -> (Bool, (Term.Term a b, Term.Term a b)) -> Bool;
is_critical_pair_closing_cp c n (False, (s, t)) =
  not (Option.is_none
        (List.find (Rewrite_Relations_Impl.is_par_rstep c s)
          (Trs_Impl.reachable_terms c t n)));
is_critical_pair_closing_cp c n (True, (s, t)) =
  not (Option.is_none
        (List.find (List.member (Trs_Impl.reachable_terms c t n))
          (Trs_Impl.reachable_terms c s n)));

check_critical_pair_closing ::
  forall a b.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Compare.Compare a,
      Fresh.Infinite a, Eq a, Mapping_Impl.Mapping_impl a, Set_Impl.Set_impl a,
      Shows_Literal.Showl a, Compare.Compare b, Eq b,
      Shows_Literal.Showl b) => Renaming2.Renaming2 a ->
                                  [(Term.Term b a, Term.Term b a)] ->
                                    [(Term.Term b a, Term.Term b a)] ->
                                      Arith.Nat ->
Sum_Type.Sum (String -> String) ();
check_critical_pair_closing ren r c n =
  Error_Monad.catch_error
    (Error_Monad.bind (Trs_Impl.check_left_linear_trs r)
      (\ _ ->
        Error_Monad.bind
          (Error_Monad.catch_error (Check_Monad.check_subseteq c r)
            (\ _ ->
              Sum_Type.Inl (Shows_Literal.showsl_lit "C not a subsystem of R")))
          (\ _ ->
            Error_Monad.catch_error
              (Error_Monad.forallM
                (\ (b, (s, t)) ->
                  Check_Monad.check
                    (is_critical_pair_closing_cp c n (b, (s, t)))
                    ((((((Shows_Literal.showsl_lit "the critical pair " .
                           Term_More.showsl_terma s) .
                          Shows_Literal.showsl_lit " <- . -> ") .
                         Term_More.showsl_terma t) .
                        Shows_Literal.showsl_lit " is not closed within ") .
                       Shows_Literal.showsl_nat n) .
                      Shows_Literal.showsl_lit " steps."))
                (Critical_Pairs_Impl.critical_pairs_impl ren r r))
              (\ x -> Sum_Type.Inl (snd x)))))
    (\ x ->
      Sum_Type.Inl
        ((x . Shows_Literal.showsl_lit
                "\nhence the following TRS is not critical pair closing\n") .
          Trs_Impl.showsl_trs r));

}
