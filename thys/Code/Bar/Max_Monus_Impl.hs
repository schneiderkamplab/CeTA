{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Max_Monus_Impl(Max_monus_impl(..), max_monus_rel_impl) where {

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
import qualified Set_Interval;
import qualified Term_Order;
import qualified Complexity;
import qualified Ordered_Algebra_Impl;
import qualified F_Algebra;
import qualified Sum_Type;
import qualified Mapping;
import qualified Shows_Literal;
import qualified Quasi_Order;
import qualified Max_Monus;
import qualified IA_Checker;
import qualified Term_Rewriting;
import qualified Arith;

data Max_monus_impl a =
  Max_Monus_Impl IA_Checker.La_solver_type
    [((a, Arith.Nat), Term_Rewriting.Term Max_Monus.Sig Arith.Nat)];

simplified_alist ::
  forall a.
    (Shows_Literal.Showl a) => [((a, Arith.Nat),
                                  Term_Rewriting.Term Max_Monus.Sig
                                    Arith.Nat)] ->
                                 [((a, Arith.Nat),
                                    Term_Rewriting.Term Max_Monus.Sig
                                      Arith.Nat)];
simplified_alist alist = map (Arith.map_prod id Max_Monus.simplify) alist;

check_less_eq_term ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b, Quasi_Order.Linorder b,
      Shows_Literal.Showl b) => [((a, Arith.Nat),
                                   Term_Rewriting.Term Max_Monus.Sig
                                     Arith.Nat)] ->
                                  IA_Checker.La_solver_type ->
                                    Term_Rewriting.Term a b ->
                                      Term_Rewriting.Term a b ->
Sum_Type.Sum (String -> String) ();
check_less_eq_term alist solver s t =
  Term_Rewriting.check_valid_formula Term_Rewriting.showsl_IA_exp
    IA_Checker.check_clause IA_Checker.lit_normalize solver
    (Max_Monus.le_via_IA
      (F_Algebra.eval
        (\ f ss ->
          Term_Rewriting.eval_term Term_Rewriting.Fun
            (Ordered_Algebra_Impl.e (simplified_alist alist)
              (\ _ -> Max_Monus.MaxF) f (Arith.size_list ss))
            (Arith.nth ss))
        s Term_Rewriting.Var)
      (F_Algebra.eval
        (\ f ss ->
          Term_Rewriting.eval_term Term_Rewriting.Fun
            (Ordered_Algebra_Impl.e (simplified_alist alist)
              (\ _ -> Max_Monus.MaxF) f (Arith.size_list ss))
            (Arith.nth ss))
        t Term_Rewriting.Var));

check_less_term ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b, Quasi_Order.Linorder b,
      Shows_Literal.Showl b) => [((a, Arith.Nat),
                                   Term_Rewriting.Term Max_Monus.Sig
                                     Arith.Nat)] ->
                                  IA_Checker.La_solver_type ->
                                    Term_Rewriting.Term a b ->
                                      Term_Rewriting.Term a b ->
Sum_Type.Sum (String -> String) ();
check_less_term alist solver s t =
  Term_Rewriting.check_valid_formula Term_Rewriting.showsl_IA_exp
    IA_Checker.check_clause IA_Checker.lit_normalize solver
    (Max_Monus.less_via_IA
      (F_Algebra.eval
        (\ f ss ->
          Term_Rewriting.eval_term Term_Rewriting.Fun
            (Ordered_Algebra_Impl.e (simplified_alist alist)
              (\ _ -> Max_Monus.MaxF) f (Arith.size_list ss))
            (Arith.nth ss))
        s Term_Rewriting.Var)
      (F_Algebra.eval
        (\ f ss ->
          Term_Rewriting.eval_term Term_Rewriting.Fun
            (Ordered_Algebra_Impl.e (simplified_alist alist)
              (\ _ -> Max_Monus.MaxF) f (Arith.size_list ss))
            (Arith.nth ss))
        t Term_Rewriting.Var));

create_max_monus_rel_impl ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b, Quasi_Order.Linorder b,
      Shows_Literal.Showl b) => [((a, Arith.Nat),
                                   Term_Rewriting.Term Max_Monus.Sig
                                     Arith.Nat)] ->
                                  IA_Checker.La_solver_type ->
                                    Term_Rewriting.Rel_impl_ext a b ();
create_max_monus_rel_impl alist solver =
  Term_Rewriting.Rel_impl_ext
    (Ordered_Algebra_Impl.check_encoding (simplified_alist alist))
    (Sum_Type.Inr ())
    ((Shows_Literal.showsl_lit "max-monus interpretations:" .
       Shows_Literal.showsl_literal "\n") .
      Ordered_Algebra_Impl.showsl_encoding (simplified_alist alist))
    (\ (s, t) -> check_less_term alist solver t s)
    (\ (s, t) -> check_less_eq_term alist solver t s)
    (\ (s, t) -> check_less_eq_term alist solver t s)
    (\ (f, n) ->
      Arith.minus_set (Set_Interval.atLeastLessThan Arith.zero_nat n)
        (Arith.set
          (F_Algebra.constant_positions
            (Ordered_Algebra_Impl.e (simplified_alist alist)
              (\ _ -> Max_Monus.MaxF))
            f n)))
    (\ (f, n) ->
      Arith.minus_set (Set_Interval.atLeastLessThan Arith.zero_nat n)
        (Arith.set
          (F_Algebra.constant_positions
            (Ordered_Algebra_Impl.e (simplified_alist alist)
              (\ _ -> Max_Monus.MaxF))
            f n)))
    (Sum_Type.Inr ()) (Sum_Type.Inr ()) (Sum_Type.Inr ()) (Sum_Type.Inr ())
    (Sum_Type.Inr ()) (Sum_Type.Inr ()) Term_Order.empty_af
    (\ _ ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
          "monotonicity of max-monus is not yet supported"))
    (Just (map fst (simplified_alist alist))) Nothing
    Term_Rewriting.no_complexity_check ();

max_monus_rel_impl ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b, Quasi_Order.Linorder b,
      Shows_Literal.Showl b) => Max_monus_impl a ->
                                  Term_Rewriting.Rel_impl_ext a b ();
max_monus_rel_impl (Max_Monus_Impl typea rp) =
  create_max_monus_rel_impl rp typea;

}
