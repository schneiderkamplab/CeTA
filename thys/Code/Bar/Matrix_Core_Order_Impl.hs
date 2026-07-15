{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Matrix_Core_Order_Impl(show_core_matrix_inter_main, core_EI_rel_impl_int,
                          core_EI_rel_impl_fract)
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
import qualified Matrix_Core_Order;
import qualified Term_Order;
import qualified HOL;
import qualified Complexity;
import qualified Shows_Literal_Matrix;
import qualified Matrix_Comparison;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Quasi_Order;
import qualified Matrix_Carrier_Impl;
import qualified Show_Instances;
import qualified Linear_Polynomial;
import qualified Archimedean_Field;
import qualified SN_Orders;
import qualified Term_Rewriting;
import qualified Matrix;
import qualified SN_Order_Carrier;
import qualified Shows_Literal;
import qualified Arith;

check_valid_dims ::
  forall a b c.
    (Shows_Literal.Showl a, Arith.Zero b, Eq b, Quasi_Order.Ord b,
      Eq c) => Arith.Nat ->
                 ((a, Arith.Nat), ([Matrix.Mat b], Matrix.Mat c)) ->
                   Sum_Type.Sum (String -> String) ();
check_valid_dims n =
  (\ (a, b) ->
    (case a of {
      (f, k) ->
        (\ (cs, c) ->
          Error_Monad.bind
            (Check_Monad.check
              (all (\ ca ->
                     Arith.member ca (Matrix.carrier_mat n n) &&
                       Matrix_Comparison.mat_ge ca (Matrix.zero_mat n n))
                cs)
              (Shows_Literal.showsl_literal "coefficients must be in N"))
            (\ _ ->
              Error_Monad.bind
                (Check_Monad.check (Arith.member c (Matrix.carrier_mat n n))
                  (Shows_Literal.showsl_literal
                    "wrong matrix dimension of constant part"))
                (\ _ ->
                  Check_Monad.check (Arith.equal_nat (Arith.size_list cs) k)
                    ((Shows_Literal.showsl_literal
                        "number of coefficient of symbol " .
                       Shows_Literal.showsl f) .
                      Shows_Literal.showsl_literal
                        " differs from arity of symbol"))));
    })
      b);

show_core_matrix_inter_main ::
  forall a b c.
    (Shows_Literal.Showl a, Shows_Literal.Showl b,
      Shows_Literal.Showl c) => String ->
                                  a -> [Arith.Nat] ->
 [((b, Arith.Nat), ([c], c))] -> String -> String;
show_core_matrix_inter_main mode d idx intr =
  (((((((Shows_Literal.showsl_lit "core matrix interpretation (mode = " .
          Shows_Literal.showsl_lit mode) .
         Shows_Literal.showsl_lit ") with dimension ") .
        Shows_Literal.showsl d) .
       Shows_Literal.showsl_lit " and strict indices I = ") .
      Shows_Literal.showsl_lista (map Arith.suc idx)) .
     Shows_Literal.showsl_lit " where\n") .
    Shows_Literal.showsl_sep
      (\ (a, b) ->
        (case a of {
          (f, n) ->
            (\ (cs, c) ->
              ((Shows_Literal.showsl_lit "[" .
                 Term_Rewriting.showsl_terma
                   (Term_Rewriting.Fun f
                     (map (\ i ->
                            Term_Rewriting.Var
                              ([Arith.char_0x78] ++
                                Show_Instances.shows_prec_nat Arith.zero_nat i
                                  []))
                       (Arith.upt Arith.one_nat (Arith.suc n))))) .
                Shows_Literal.showsl_lit "] = ") .
                Linear_Polynomial.showsl_l_poly
                  (Linear_Polynomial.LPoly c
                    (zip (map (\ i ->
                                [Arith.char_0x78] ++
                                  Show_Instances.shows_prec_nat Arith.zero_nat i
                                    [])
                           (Arith.upt Arith.one_nat (Arith.suc n)))
                      cs)));
        })
          b)
      (Shows_Literal.showsl_lit "\n") intr) .
    Shows_Literal.showsl_lit
      "\nand\n[f(x1,..,xn)] = x1 + ... + xn + 1 for all other symbols f\n\n";

core_EI_rel_impl ::
  forall a b c.
    (Arith.Ordered_ab_group_add a, Eq a, Arith.Ordered_semiring_0 a,
      Arith.Ring_1 a, Arith.Zero_less_one a, SN_Orders.Ordered_semiring_1 a,
      Shows_Literal.Showl a, Eq b, Shows_Literal.Showl b, Eq c,
      Shows_Literal.Showl c) => Arith.Nat ->
                                  a -> [Arith.Nat] ->
 [((b, Arith.Nat), ([Matrix.Mat a], Matrix.Mat a))] ->
   Term_Rewriting.Rel_impl_ext b c ();
core_EI_rel_impl n delta i fk_cs =
  let {
    ii = Matrix_Core_Order.iI_list_to_II n delta fk_cs;
    checkNS =
      (\ lr ->
        Check_Monad.check
          (Matrix_Core_Order.check_lpoly_N_N n
            (Matrix_Core_Order.poly_of_rule_N n ii (Arith.set i) lr))
          (Shows_Literal.showsl_literal "could not weakly orient rule " .
            Term_Rewriting.showsl_rule lr));
  } in Term_Rewriting.Rel_impl_ext
         (Error_Monad.bind
           (Check_Monad.check (Quasi_Order.less Arith.zero delta)
             (Shows_Literal.showsl_literal "delta must be positive"))
           (\ _ ->
             Error_Monad.bind
               (Check_Monad.check (all (\ ia -> Arith.less_nat ia n) i)
                 (Shows_Literal.showsl_literal
                   "indices in I must be below matrix dimension"))
               (\ _ ->
                 Error_Monad.bind
                   (Check_Monad.check (not (null i))
                     (Shows_Literal.showsl_literal
                       "indices I must be non-empty"))
                   (\ _ ->
                     Error_Monad.bind
                       (Error_Monad.catch_error
                         (Error_Monad.forallM (check_valid_dims n) fk_cs)
                         (\ x -> Sum_Type.Inl (snd x)))
                       (\ _ ->
                         Error_Monad.bind
                           (Error_Monad.catch_error
                             (Error_Monad.forallM
                               (\ (fk, _) ->
                                 Check_Monad.check
                                   (Matrix_Core_Order.check_lpoly_N_E_I n
                                     (Arith.set i)
                                     (Matrix_Core_Order.inter_lpoly_N n ii
                                       (Arith.set i) fk))
                                   ((Shows_Literal.showsl_literal
                                       "interpretation of symbol " .
                                      Shows_Literal.showsl (fst fk)) .
                                     Shows_Literal.showsl_literal
                                       " exceeds E-I carrier"))
                               fk_cs)
                             (\ x -> Sum_Type.Inl (snd x)))
                           (\ _ ->
                             Error_Monad.catch_error
                               (Error_Monad.forallM
                                 (\ (_, csc) ->
                                   Check_Monad.check
                                     (all (\ a ->
    Matrix_Comparison.mat_ge a (Matrix_Core_Order.oneE_I n (Arith.set i)))
                                       (fst csc))
                                     (Shows_Literal.showsl_literal
                                       " require monotone coefficient in E-I"))
                                 fk_cs)
                               (\ x -> Sum_Type.Inl (snd x))))))))
         (Sum_Type.Inr ()) (show_core_matrix_inter_main "E_I" n i fk_cs)
         (\ lr ->
           Check_Monad.check
             (Matrix_Core_Order.check_lpoly_N_P_I n delta i
               (Matrix_Core_Order.poly_of_rule_N n ii (Arith.set i) lr))
             (Shows_Literal.showsl_literal "could not strictly orient rule " .
               Term_Rewriting.showsl_rule lr))
         checkNS checkNS Term_Order.full_af Term_Order.full_af (Sum_Type.Inr ())
         (Sum_Type.Inr ()) (Sum_Type.Inr ()) (Sum_Type.Inr ()) (Sum_Type.Inr ())
         (Sum_Type.Inr ()) (\ _ -> Arith.top_set) (\ _ -> Sum_Type.Inr ())
         Nothing Nothing Term_Rewriting.no_complexity_check ();

core_EI_rel_impl_int ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => Arith.Nat ->
                                  [Arith.Nat] ->
                                    [((a, Arith.Nat),
                                       ([Matrix.Mat Arith.Int],
 Matrix.Mat Arith.Int))] ->
                                      Term_Rewriting.Rel_impl_ext a b ();
core_EI_rel_impl_int n = core_EI_rel_impl n Arith.one_int;

core_EI_rel_impl_fract ::
  forall a b c.
    (Archimedean_Field.Floor_ceiling a, Eq a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b, Eq c,
      Shows_Literal.Showl c) => Arith.Nat ->
                                  a -> [Arith.Nat] ->
 [((b, Arith.Nat), ([Matrix.Mat a], Matrix.Mat a))] ->
   Term_Rewriting.Rel_impl_ext b c ();
core_EI_rel_impl_fract n delta = core_EI_rel_impl n delta;

}
