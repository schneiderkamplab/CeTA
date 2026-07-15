{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Matrix_TRS_Impl(Core_matrix_mode(..), Core_matrix_inter(..),
                   create_core_matrix_int, create_core_matrix_fract)
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
import qualified Term_Order;
import qualified Complexity;
import qualified Norms;
import qualified Matrix_Core_Order_Impl;
import qualified Term_Order_Impl;
import qualified Compare;
import qualified SN_Order_Carrier;
import qualified Archimedean_Field;
import qualified Trs_Impl;
import qualified Linear_Polynomial;
import qualified Term;
import qualified Shows_Literal_Matrix;
import qualified Matrix_IArray_Impl;
import qualified Set_Interval;
import qualified Phantom_Type;
import qualified Set;
import qualified Collection_Order;
import qualified Collection_Enum;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified HOL;
import qualified Sum_Type;
import qualified Orderings;
import qualified Shows_Literal;
import qualified List;
import qualified Linear_Poly_Interpretation;
import qualified Ordered_Semiring;
import qualified Congruence;
import qualified Group;
import qualified Ring;
import qualified SN_Orders;
import qualified Matrix_TRS;
import qualified Product_Type;
import qualified Option;
import qualified Map;
import qualified Matrix;
import qualified Arith;

data Core_matrix_mode = E_I | M_I;

data Core_matrix_inter a b =
  Core_Matrix_Inter Core_matrix_mode Arith.Nat [Arith.Nat]
    [((a, Arith.Nat), ([Matrix.Mat b], Matrix.Mat b))];

pI :: forall a b.
        (Eq a,
          Arith.Ring_1 b) => Arith.Nat ->
                               [((a, Arith.Nat),
                                  ([Matrix.Mat b], Matrix.Mat b))] ->
                                 (a, Arith.Nat) ->
                                   ([Matrix.Mat b], Matrix.Mat b);
pI n fc = (\ (f, n1) -> (case Map.map_of fc (f, n1) of {
                          Nothing -> Matrix_TRS.default_mat_inter n n1;
                          Just val -> val;
                        }));

rring ::
  forall a.
    (Arith.Ordered_semiring_0 a, Arith.Ring_1 a,
      SN_Orders.Ordered_semiring_1 a) => Arith.Nat ->
   Congruence.Partial_object_ext (Matrix.Mat a)
     (Group.Monoid_ext (Matrix.Mat a)
       (Ring.Ring_ext (Matrix.Mat a)
         (Ordered_Semiring.Ordered_semiring_ext (Matrix.Mat a)
           (Linear_Poly_Interpretation.Explicit_minus_semiring_ext
             (Matrix.Mat a) ()))));
rring n = Matrix_TRS.matsemiring n (\ _ _ -> True);

check_carrier ::
  forall a. Arith.Nat -> Matrix.Mat a -> Sum_Type.Sum (String -> String) ();
check_carrier n m =
  Error_Monad.bind
    (Check_Monad.check (Arith.equal_nat (Matrix.dim_row m) n)
      (((Shows_Literal.showsl_lit "Expected " . Shows_Literal.showsl_nat n) .
         Shows_Literal.showsl_lit " rows in matrix, got ") .
        Shows_Literal.showsl_nat (Matrix.dim_row m)))
    (\ _ ->
      Check_Monad.check (Arith.equal_nat (Matrix.dim_col m) n)
        (((Shows_Literal.showsl_lit "Expected " . Shows_Literal.showsl_nat n) .
           Shows_Literal.showsl_lit " columns in matrix, got ") .
          Shows_Literal.showsl_nat (Matrix.dim_col m)));

check_N ::
  forall a.
    (Arith.Zero a, Orderings.Ord a,
      Shows_Literal.Showl a) => Arith.Nat ->
                                  Matrix.Mat a ->
                                    Sum_Type.Sum (String -> String) ();
check_N n m =
  Error_Monad.bind (check_carrier n m)
    (\ _ ->
      Check_Monad.check
        (let {
           d = Arith.minus_nat n Arith.one_nat;
         } in (if Arith.less_nat d n
                then List.all_interval
                       (\ i ->
                         let {
                           da = Arith.minus_nat n Arith.one_nat;
                         } in (if Arith.less_nat da n
                                then List.all_interval
                                       (\ j ->
 Orderings.less_eq Arith.zero (Matrix.index_mat m (i, j)))
                                       Arith.zero_nat da
                                else True))
                       Arith.zero_nat d
                else True))
        (Shows_Literal.showsl_lit
           "Expected all matrix element to be non-negative: " .
          Shows_Literal.showsl_lista (Matrix.mat_to_list m)));

check_indices :: Arith.Nat -> [Arith.Nat] -> Sum_Type.Sum (String -> String) ();
check_indices n ids =
  Error_Monad.bind
    (Check_Monad.check
      (not (Collection_Eq.set_eq (List.set ids)
             (Set_Impl.set_empty
               (Phantom_Type.of_phantom Set_Impl.set_impl_nat))))
      (Shows_Literal.showsl_lit "Set of indices should not be empty"))
    (\ _ ->
      Check_Monad.check
        (Set.less_eq_set (List.set ids)
          (Set_Interval.atLeastLessThan Arith.zero_nat n))
        (Shows_Literal.showsl_lit "I should be a subset of {0..n-1}"));

check_lpoly_coef_N ::
  forall a b.
    (Arith.Zero b, Orderings.Ord b,
      Shows_Literal.Showl b) => Arith.Nat ->
                                  Linear_Polynomial.L_poly a (Matrix.Mat b) ->
                                    Sum_Type.Sum (String -> String) ();
check_lpoly_coef_N n lp =
  Error_Monad.catch_error
    (Error_Monad.catch_error
      (Error_Monad.forallM (check_N n)
        (Linear_Poly_Interpretation.coeffs_of_lpoly_better lp))
      (\ x -> Sum_Type.Inl (snd x)))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "Expected all lpoly coefficient to be greater or equal to 0 mat.\n" .
          x));

check_E_I_weak ::
  forall a b c d.
    (Eq b, Shows_Literal.Showl b, Eq c, Arith.Ordered_semiring_0 c,
      Arith.Ring_1 c, SN_Orders.Ordered_semiring_1 c, Shows_Literal.Showl c,
      Eq d,
      Shows_Literal.Showl d) => Arith.Nat ->
                                  a -> [((b, Arith.Nat),
  ([Matrix.Mat c], Matrix.Mat c))] ->
 (Term.Term b d, Term.Term b d) -> Sum_Type.Sum (String -> String) ();
check_E_I_weak n ids fc =
  (\ (l, r) ->
    let {
      diff = Linear_Poly_Interpretation.evalp_rule (rring n) (pI n fc) l r;
    } in Error_Monad.catch_error (check_lpoly_coef_N n diff)
           (\ x ->
             Sum_Type.Inl
               ((((((Shows_Literal.showsl_lit
                       "problem in E_I-weak decrease of " .
                      Trs_Impl.showsl_rule (l, r)) .
                     Shows_Literal.showsl_literal "\n") .
                    Shows_Literal.showsl_lit
                      "with interpretation [left] - [right] = ") .
                   Linear_Polynomial.showsl_l_poly diff) .
                  Shows_Literal.showsl_literal "\n") .
                 x)));

check_M_I_weak ::
  forall a b c d.
    (Eq b, Shows_Literal.Showl b, Eq c, Arith.Ordered_semiring_0 c,
      Arith.Ring_1 c, SN_Orders.Ordered_semiring_1 c, Shows_Literal.Showl c,
      Eq d,
      Shows_Literal.Showl d) => Arith.Nat ->
                                  a -> [((b, Arith.Nat),
  ([Matrix.Mat c], Matrix.Mat c))] ->
 (Term.Term b d, Term.Term b d) -> Sum_Type.Sum (String -> String) ();
check_M_I_weak n ids fc =
  (\ (l, r) ->
    let {
      diff = Linear_Poly_Interpretation.evalp_rule (rring n) (pI n fc) l r;
    } in Error_Monad.catch_error (check_lpoly_coef_N n diff)
           (\ x ->
             Sum_Type.Inl
               ((((((Shows_Literal.showsl_lit
                       "problem in M_I-weak decrease of " .
                      Trs_Impl.showsl_rule (l, r)) .
                     Shows_Literal.showsl_literal "\n") .
                    Shows_Literal.showsl_lit
                      "with interpretation [left] - [right] = ") .
                   Linear_Polynomial.showsl_l_poly diff) .
                  Shows_Literal.showsl_literal "\n") .
                 x)));

check_E_I ::
  forall a.
    (Arith.One a, Orderings.Ord a,
      Shows_Literal.Showl a) => Arith.Nat ->
                                  [Arith.Nat] ->
                                    Matrix.Mat a ->
                                      Sum_Type.Sum (String -> String) ();
check_E_I n ids m =
  Check_Monad.check
    (all (\ i -> Orderings.less_eq Arith.one (Matrix.index_mat m (i, i))) ids)
    (Shows_Literal.showsl_lit
       "[E_I set] Expected all diagonal elements to be at least 1: " .
      Shows_Literal.showsl_lista (Matrix.mat_to_list m));

check_L_I ::
  forall a b.
    (Shows_Literal.Showl a,
      Arith.Zero b) => Arith.Nat ->
                         (a -> b -> Bool) ->
                           [Arith.Nat] ->
                             [Matrix.Mat a] ->
                               Sum_Type.Sum (String -> String) ();
check_L_I n gt ids ms =
  Check_Monad.check
    (all (\ i ->
           any (\ m ->
                 any (\ j -> gt (Matrix.index_mat m (i, j)) Arith.zero) ids)
             ms)
      ids)
    (Shows_Literal.showsl_lit
       "[L_I set] Expected at least one positive element per row for coefficients: " .
      Shows_Literal.showsl_list_list (map Matrix.mat_to_list ms));

check_M_I ::
  forall a.
    (Arith.One a, Orderings.Ord a,
      Shows_Literal.Showl a) => Arith.Nat ->
                                  [Arith.Nat] ->
                                    Matrix.Mat a ->
                                      Sum_Type.Sum (String -> String) ();
check_M_I n ids m =
  Check_Monad.check
    (all (\ i ->
           any (\ j -> Orderings.less_eq Arith.one (Matrix.index_mat m (i, j)))
             ids)
      ids)
    (Shows_Literal.showsl_lit
       "[M_I set] Expected at least one element element per row that is at least 1 " .
      Shows_Literal.showsl_lista (Matrix.mat_to_list m));

check_P_I ::
  forall a b.
    (Arith.Zero b) => Arith.Nat ->
                        (a -> b -> Bool) ->
                          [Arith.Nat] ->
                            Matrix.Mat a -> Sum_Type.Sum (String -> String) ();
check_P_I n gt ids m =
  Check_Monad.check
    (any (\ i -> any (\ j -> gt (Matrix.index_mat m (i, j)) Arith.zero) ids)
      ids)
    (Shows_Literal.showsl_lit
      "[P_I set] Expected at least one positive element");

check_poly_coef_one_P_I ::
  forall a b c.
    (Arith.Zero a, Orderings.Ord a, Shows_Literal.Showl a,
      Arith.Zero b) => Arith.Nat ->
                         (a -> b -> Bool) ->
                           [Arith.Nat] ->
                             Linear_Polynomial.L_poly c (Matrix.Mat a) ->
                               Sum_Type.Sum (String -> String) ();
check_poly_coef_one_P_I n gt ids lp =
  Error_Monad.bind (check_lpoly_coef_N n lp)
    (\ _ ->
      Check_Monad.check
        (any (\ c -> Error_Monad.isOK (check_P_I n gt ids c))
          (Linear_Poly_Interpretation.coeffs_of_lpoly_better lp))
        (Shows_Literal.showsl_lit
           "Expected at least one lpoly coefficient to be in P_I, got none." .
          Shows_Literal.showsl_list_list
            (map Matrix.mat_to_list
              (Linear_Poly_Interpretation.coeffs_of_lpoly_better lp))));

check_E_I_strict ::
  forall a b c d.
    (Eq a, Arith.Ordered_semiring_0 a, Arith.Ring_1 a,
      SN_Orders.Ordered_semiring_1 a, Shows_Literal.Showl a, Arith.Zero b, Eq c,
      Shows_Literal.Showl c, Eq d,
      Shows_Literal.Showl d) => Arith.Nat ->
                                  (a -> b -> Bool) ->
                                    [Arith.Nat] ->
                                      [((c, Arith.Nat),
 ([Matrix.Mat a], Matrix.Mat a))] ->
(Term.Term c d, Term.Term c d) -> Sum_Type.Sum (String -> String) ();
check_E_I_strict n gt ids fc =
  (\ (l, r) ->
    let {
      diff = Linear_Poly_Interpretation.evalp_rule (rring n) (pI n fc) l r;
    } in Error_Monad.catch_error
           (Error_Monad.bind (check_lpoly_coef_N n diff)
             (\ _ -> check_poly_coef_one_P_I n gt ids diff))
           (\ x ->
             Sum_Type.Inl
               ((((((Shows_Literal.showsl_lit
                       "problem in E_I-strict decrease of " .
                      Trs_Impl.showsl_rule (l, r)) .
                     Shows_Literal.showsl_literal "\n") .
                    Shows_Literal.showsl_lit
                      "with interpretation [left] - [right] = ") .
                   Linear_Polynomial.showsl_l_poly diff) .
                  Shows_Literal.showsl_literal "\n") .
                 x)));

check_poly_coef_one_L_I ::
  forall a b c.
    (Shows_Literal.Showl a,
      Arith.Zero b) => Arith.Nat ->
                         (a -> b -> Bool) ->
                           [Arith.Nat] ->
                             Linear_Polynomial.L_poly c (Matrix.Mat a) ->
                               Sum_Type.Sum (String -> String) ();
check_poly_coef_one_L_I n gt ids lp =
  Error_Monad.catch_error
    (check_L_I n gt ids (Linear_Poly_Interpretation.coeffs_of_lpoly_better lp))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit "problem in checking strict L_I-decrease.\n" .
          x));

check_M_I_strict ::
  forall a b c d.
    (Eq a, Arith.Ordered_semiring_0 a, Arith.Ring_1 a,
      SN_Orders.Ordered_semiring_1 a, Shows_Literal.Showl a, Arith.Zero b, Eq c,
      Shows_Literal.Showl c, Eq d,
      Shows_Literal.Showl d) => Arith.Nat ->
                                  (a -> b -> Bool) ->
                                    [Arith.Nat] ->
                                      [((c, Arith.Nat),
 ([Matrix.Mat a], Matrix.Mat a))] ->
(Term.Term c d, Term.Term c d) -> Sum_Type.Sum (String -> String) ();
check_M_I_strict n gt ids fc =
  (\ (l, r) ->
    let {
      diff = Linear_Poly_Interpretation.evalp_rule (rring n) (pI n fc) l r;
    } in Error_Monad.catch_error
           (Error_Monad.bind (check_lpoly_coef_N n diff)
             (\ _ -> check_poly_coef_one_L_I n gt ids diff))
           (\ x ->
             Sum_Type.Inl
               ((((((Shows_Literal.showsl_lit
                       "problem in M_I-strict decrease of " .
                      Trs_Impl.showsl_rule (l, r)) .
                     Shows_Literal.showsl_literal "\n") .
                    Shows_Literal.showsl_lit
                      "with interpretation [left] - [right] = ") .
                   Linear_Polynomial.showsl_l_poly diff) .
                  Shows_Literal.showsl_literal "\n") .
                 x)));

core_matrix_gt_int ::
  Sum_Type.Sum (String -> String) (Arith.Int -> Arith.Int -> Bool);
core_matrix_gt_int = Sum_Type.Inr (\ x y -> Arith.less_int y x);

check_coeffs_length ::
  forall a b c.
    (Shows_Literal.Showl a) => [((a, Arith.Nat),
                                  ([Matrix.Mat b], Matrix.Mat c))] ->
                                 Sum_Type.Sum (String -> String) ();
check_coeffs_length fc =
  Error_Monad.catch_error
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ ((f, n), (cs, _)) ->
          Check_Monad.check (Arith.equal_nat (List.size_list cs) n)
            (((((Shows_Literal.showsl_lit
                   "Expected as many multiplicative coefficients as the arity of " .
                  Shows_Literal.showsl f) .
                 Shows_Literal.showsl_lit ". Got ") .
                Shows_Literal.showsl_nat (List.size_list cs)) .
               Shows_Literal.showsl_lit " instead of ") .
              Shows_Literal.showsl_nat n))
        fc)
      (\ x -> Sum_Type.Inl (snd x)))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "The number of interpretation coefficients (multiplicative, i.e. not the constant coefficient)\n should always match the arity of the corresponding function symbol.\n" .
          x));

check_coefficients_N ::
  forall a b.
    (Shows_Literal.Showl a, Arith.Zero b, Orderings.Ord b,
      Shows_Literal.Showl b) => Arith.Nat ->
                                  [Arith.Nat] ->
                                    [((a, Arith.Nat),
                                       ([Matrix.Mat b], Matrix.Mat b))] ->
                                      Sum_Type.Sum (String -> String) ();
check_coefficients_N n ids fc =
  Error_Monad.catch_error
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ ((f, _), (cs, c)) ->
          Error_Monad.catch_error
            (Error_Monad.catch_error (Error_Monad.forallM (check_N n) (c : cs))
              (\ x -> Sum_Type.Inl (snd x)))
            (\ x ->
              Sum_Type.Inl
                (((Shows_Literal.showsl_lit
                     "Expected all interpretation coefficients of symbol " .
                    Shows_Literal.showsl f) .
                   Shows_Literal.showsl_lit " to be in N\n") .
                  x)))
        fc)
      (\ x -> Sum_Type.Inl (snd x)))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "Expected all interpretation coefficients of all function symbols used to be in N.\n" .
          x));

core_matrix_gt_delta ::
  forall a.
    (Archimedean_Field.Floor_ceiling a,
      Shows_Literal.Showl a) => a -> Sum_Type.Sum (String -> String)
                                       (a -> a -> Bool);
core_matrix_gt_delta d =
  Error_Monad.bind
    (Check_Monad.check
      (Orderings.less Arith.zero d && Orderings.less_eq d Arith.one)
      ((Shows_Literal.showsl_lit "parameter delta " . Shows_Literal.showsl d) .
        Shows_Literal.showsl_lit " must be between 0 and 1"))
    (\ _ -> Sum_Type.Inr (SN_Order_Carrier.delta_gt d));

check_coefficients_M_I ::
  forall a b.
    (Shows_Literal.Showl a, Arith.One b, Arith.Zero b, Orderings.Ord b,
      Shows_Literal.Showl b) => Arith.Nat ->
                                  [Arith.Nat] ->
                                    [((a, Arith.Nat),
                                       ([Matrix.Mat b], Matrix.Mat b))] ->
                                      Sum_Type.Sum (String -> String) ();
check_coefficients_M_I n ids fc =
  Error_Monad.bind (check_coefficients_N n ids fc)
    (\ _ ->
      Error_Monad.catch_error
        (Error_Monad.catch_error
          (Error_Monad.forallM
            (\ ((f, _), (cs, c)) ->
              Error_Monad.bind
                (Error_Monad.catch_error
                  (Error_Monad.catch_error
                    (Error_Monad.forallM (check_M_I n ids) cs)
                    (\ x -> Sum_Type.Inl (snd x)))
                  (\ x ->
                    Sum_Type.Inl
                      (((Shows_Literal.showsl_lit
                           "Expected all interpretation multiplicative coefficients of symbol " .
                          Shows_Literal.showsl f) .
                         Shows_Literal.showsl_lit " to be in M_I.\n") .
                        x)))
                (\ _ ->
                  Check_Monad.check
                    (any (\ ci -> Error_Monad.isOK (check_M_I n ids ci))
                      (c : cs))
                    ((((Shows_Literal.showsl_lit
                          "Expected the constant coefficient " .
                         Shows_Literal.showsl_lista (Matrix.mat_to_list c)) .
                        Shows_Literal.showsl_lit " of symbol ") .
                       Shows_Literal.showsl f) .
                      Shows_Literal.showsl_lit
                        " to be in M_I whenever there are no multiplicative coefficient (i.e. symbol of arity 0).")))
            fc)
          (\ x -> Sum_Type.Inl (snd x)))
        (\ x ->
          Sum_Type.Inl
            (Shows_Literal.showsl_lit
               "Expected all interpretation multiplicative coeffs to be in M_I\n and the constant coeff to be in M_I whenever there are none multiplicative coeffs, for all function symbols.\n" .
              x)));

check_coeffs_M_I_final ::
  forall a b.
    (Shows_Literal.Showl a, Arith.One b, Arith.Zero b, Orderings.Ord b,
      Shows_Literal.Showl b) => Arith.Nat ->
                                  [Arith.Nat] ->
                                    [((a, Arith.Nat),
                                       ([Matrix.Mat b], Matrix.Mat b))] ->
                                      Sum_Type.Sum (String -> String) ();
check_coeffs_M_I_final n ids fc =
  Error_Monad.bind (check_coeffs_length fc)
    (\ _ ->
      Error_Monad.bind (check_coefficients_N n ids fc)
        (\ _ -> check_coefficients_M_I n ids fc));

check_coefficients_E_I ::
  forall a b.
    (Shows_Literal.Showl a, Arith.One b, Arith.Zero b, Orderings.Ord b,
      Shows_Literal.Showl b) => Arith.Nat ->
                                  [Arith.Nat] ->
                                    [((a, Arith.Nat),
                                       ([Matrix.Mat b], Matrix.Mat b))] ->
                                      Sum_Type.Sum (String -> String) ();
check_coefficients_E_I n ids fc =
  Error_Monad.bind (check_coefficients_N n ids fc)
    (\ _ ->
      Error_Monad.catch_error
        (Error_Monad.catch_error
          (Error_Monad.forallM
            (\ ((f, _), (cs, c)) ->
              Error_Monad.bind
                (Error_Monad.catch_error
                  (Error_Monad.catch_error
                    (Error_Monad.forallM (check_E_I n ids) cs)
                    (\ x -> Sum_Type.Inl (snd x)))
                  (\ x ->
                    Sum_Type.Inl
                      (((Shows_Literal.showsl_lit
                           "Expected all interpretation multiplicative coefficients of symbol " .
                          Shows_Literal.showsl f) .
                         Shows_Literal.showsl_lit " to be in E_I.\n") .
                        x)))
                (\ _ ->
                  Check_Monad.check
                    (any (\ ci -> Error_Monad.isOK (check_E_I n ids ci))
                      (c : cs))
                    ((((Shows_Literal.showsl_lit
                          "Expected the constant coefficient " .
                         Shows_Literal.showsl_lista (Matrix.mat_to_list c)) .
                        Shows_Literal.showsl_lit " of symbol ") .
                       Shows_Literal.showsl f) .
                      Shows_Literal.showsl_lit
                        " to be in E_I whenever there are no multiplicative coefficient (i.e. symbol of arity 0).")))
            fc)
          (\ x -> Sum_Type.Inl (snd x)))
        (\ x ->
          Sum_Type.Inl
            (Shows_Literal.showsl_lit
               "Expected all interpretation multiplicative coeffs to be in E_I\n and the constant coeff to be in E_I whenever there are none multiplicative coeffs, for all function symbols.\n" .
              x)));

check_coeffs_E_I_final ::
  forall a b.
    (Shows_Literal.Showl a, Arith.One b, Arith.Zero b, Orderings.Ord b,
      Shows_Literal.Showl b) => Arith.Nat ->
                                  [Arith.Nat] ->
                                    [((a, Arith.Nat),
                                       ([Matrix.Mat b], Matrix.Mat b))] ->
                                      Sum_Type.Sum (String -> String) ();
check_coeffs_E_I_final n ids fc =
  Error_Monad.bind (check_coeffs_length fc)
    (\ _ ->
      Error_Monad.bind (check_coefficients_N n ids fc)
        (\ _ -> check_coefficients_E_I n ids fc));

create_core_matrix_rel_impl ::
  forall a b c d.
    (Eq a, Arith.Ordered_semiring_0 a, Arith.Ring_1 a,
      SN_Orders.Ordered_semiring_1 a, Shows_Literal.Showl a, Arith.Zero b,
      Compare.Compare_order c, Eq c, Shows_Literal.Showl c, Eq d,
      Shows_Literal.Showl d) => Sum_Type.Sum (String -> String)
                                  (a -> b -> Bool) ->
                                  Core_matrix_inter c a ->
                                    Term_Order_Impl.Rel_impl_ext c d ();
create_core_matrix_rel_impl gtc (Core_Matrix_Inter mode n ids fc) =
  let {
    ns = (case mode of {
           E_I -> check_E_I_weak n ids fc;
           M_I -> check_M_I_weak n ids fc;
         });
    s = let {
          gt = Sum_Type.projr gtc;
        } in (case mode of {
               E_I -> check_E_I_strict n gt ids fc;
               M_I -> check_M_I_strict n gt ids fc;
             });
  } in Term_Order_Impl.Rel_impl_ext
         (Error_Monad.bind gtc
           (\ _ ->
             Error_Monad.bind (check_indices n ids)
               (\ _ -> (case mode of {
                         E_I -> check_coeffs_E_I_final n ids fc;
                         M_I -> check_coeffs_M_I_final n ids fc;
                       }))))
         (Sum_Type.Inr ())
         (Matrix_Core_Order_Impl.show_core_matrix_inter_main (case mode of {
                       E_I -> "E_I";
                       M_I -> "M_I";
                     })
           n ids fc)
         s ns ns Term_Order.full_af Term_Order.full_af (Sum_Type.Inr ())
         (Sum_Type.Inr ()) (Sum_Type.Inr ()) (Sum_Type.Inr ()) (Sum_Type.Inr ())
         (Sum_Type.Inr ()) (\ _ -> Set.top_set) (\ _ -> Sum_Type.Inr ()) Nothing
         Nothing Term_Order_Impl.no_complexity_check ();

create_core_matrix_int ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => Core_matrix_inter a Arith.Int ->
                                  Term_Order_Impl.Rel_impl_ext a b ();
create_core_matrix_int rel =
  (case rel of {
    Core_Matrix_Inter E_I n i fk_cs ->
      Matrix_Core_Order_Impl.core_EI_rel_impl_int n i fk_cs;
    Core_Matrix_Inter M_I _ _ _ ->
      create_core_matrix_rel_impl core_matrix_gt_int rel;
  });

create_core_matrix_fract ::
  forall a b c.
    (Archimedean_Field.Floor_ceiling a, Eq a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b, Shows_Literal.Showl b, Eq c,
      Shows_Literal.Showl c) => a -> Core_matrix_inter b a ->
                                       Term_Order_Impl.Rel_impl_ext b c ();
create_core_matrix_fract delta rel =
  (case rel of {
    Core_Matrix_Inter E_I n i fk_cs ->
      Matrix_Core_Order_Impl.core_EI_rel_impl_fract n delta i fk_cs;
    Core_Matrix_Inter M_I _ _ _ ->
      create_core_matrix_rel_impl (core_matrix_gt_delta delta) rel;
  });

}
