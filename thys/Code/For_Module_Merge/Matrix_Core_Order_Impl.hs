{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Matrix_Core_Order_Impl(Core_matrix_mode(..), Core_matrix_inter(..),
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
import qualified Trs_Impl;
import qualified HOL;
import qualified Complexity;
import qualified Phantom_Type;
import qualified Shows_Literal_Matrix;
import qualified Collection_Order;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Show_Instances;
import qualified Term_More;
import qualified Product_Type;
import qualified List;
import qualified Linear_Polynomial;
import qualified Str;
import qualified Term;
import qualified Orderings;
import qualified Archimedean_Field;
import qualified Matrix_Comparison;
import qualified Set;
import qualified Matrix_Carrier_Impl;
import qualified Term_Order_Impl;
import qualified Matrix_Core_Order;
import qualified Shows_Literal;
import qualified Matrix;
import qualified Arith;

data Core_matrix_mode = E_I | M_I;

data Core_matrix_inter a b =
  Core_Matrix_Inter Core_matrix_mode Arith.Nat [Arith.Nat]
    [((a, Arith.Nat), ([Matrix.Mat b], Matrix.Mat b))];

check_valid_dims ::
  forall a b c.
    (Shows_Literal.Showl a, Arith.Zero b, Eq b, Orderings.Ord b,
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
                     Set.member ca (Matrix.carrier_mat n n) &&
                       Matrix_Comparison.mat_ge ca (Matrix.zero_mat n n))
                cs)
              (Shows_Literal.showsl_literal "coefficients must be in N"))
            (\ _ ->
              Error_Monad.bind
                (Check_Monad.check (Set.member c (Matrix.carrier_mat n n))
                  (Shows_Literal.showsl_literal
                    "wrong matrix dimension of constant part"))
                (\ _ ->
                  Check_Monad.check (Arith.equal_nat (List.size_list cs) k)
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
                 Term_More.showsl_terma
                   (Term.Fun f
                     (map (\ i ->
                            Term.Var
                              ([Str.char_0x78] ++
                                Show_Instances.shows_prec_nat Arith.zero_nat i
                                  []))
                       (List.upt Arith.one_nat (Arith.suc n))))) .
                Shows_Literal.showsl_lit "] = ") .
                Linear_Polynomial.showsl_l_poly
                  (Linear_Polynomial.LPoly c
                    (zip (map (\ i ->
                                [Str.char_0x78] ++
                                  Show_Instances.shows_prec_nat Arith.zero_nat i
                                    [])
                           (List.upt Arith.one_nat (Arith.suc n)))
                      cs)));
        })
          b)
      (Shows_Literal.showsl_lit "\n") intr) .
    Shows_Literal.showsl_lit
      "\nand\n[f(x1,..,xn)] = x1 + ... + xn + 1 for all other symbols f\n\n";

in_N ::
  forall a.
    (Eq a, Matrix_Core_Order.SN_delta_order a,
      Shows_Literal.Showl a) => Arith.Nat -> Matrix.Mat a -> Bool;
in_N n a =
  Set.member a (Matrix.carrier_mat n n) &&
    Matrix_Comparison.mat_ge a (Matrix.zero_mat n n);

in_MI ::
  forall a.
    (Eq a, Matrix_Core_Order.SN_delta_order a,
      Shows_Literal.Showl a) => Arith.Nat ->
                                  [Arith.Nat] -> Matrix.Mat a -> Bool;
in_MI n i a =
  in_N n a &&
    all (\ ia ->
          any (\ j -> Orderings.less_eq Arith.one (Matrix.index_mat a (ia, j)))
            i)
      i;

core_MI_rel_impl ::
  forall a b c.
    (Eq a, Matrix_Core_Order.SN_delta_order a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b, Eq c,
      Shows_Literal.Showl c) => Arith.Nat ->
                                  a -> [Arith.Nat] ->
 [((b, Arith.Nat), ([Matrix.Mat a], Matrix.Mat a))] ->
   Term_Order_Impl.Rel_impl_ext b c ();
core_MI_rel_impl n delta i fk_cs =
  let {
    def = Matrix.smult_mat (Arith.plus delta Arith.one) (Matrix.one_mat n);
    alpha = Matrix_Core_Order.alpha_list_to_Alpha n def fk_cs;
    checkNS =
      (\ lr ->
        Check_Monad.check
          (case Matrix_Core_Order.alpha_lhs_minus_rhs n alpha lr of {
            Linear_Polynomial.LPoly c cs -> all (in_N n) (c : map snd cs);
          })
          ((((Shows_Literal.showsl_literal "could not weakly orient rule " .
               Trs_Impl.showsl_rule lr) .
              Shows_Literal.showsl_literal "\n") .
             Shows_Literal.showsl_literal "where lhs - rhs evaluates to ") .
            Linear_Polynomial.showsl_l_poly
              (Matrix_Core_Order.alpha_lhs_minus_rhs n alpha lr)));
  } in Term_Order_Impl.Rel_impl_ext
         (Error_Monad.bind
           (Check_Monad.check (Orderings.less Arith.zero delta)
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
                         Error_Monad.catch_error
                           (Error_Monad.forallM
                             (\ (fk, _) ->
                               Check_Monad.check
                                 (case Matrix_Core_Order.inter_lpoly n alpha fk
                                   of {
                                   Linear_Polynomial.LPoly c cs ->
                                     all (in_N n) (c : map snd cs) &&
                                       all
 (\ ia ->
   any (\ a ->
         any (\ j -> Orderings.less_eq Arith.one (Matrix.index_mat a (ia, j)))
           i)
     (c : map snd cs))
 i;
                                 })
                                 ((Shows_Literal.showsl_literal
                                     "cannot ensure that interpretation of symbol " .
                                    Shows_Literal.showsl (fst fk)) .
                                   Shows_Literal.showsl_literal
                                     " is function from M-I^* to M-I"))
                             fk_cs)
                           (\ x -> Sum_Type.Inl (snd x)))))))
         (Sum_Type.Inr ()) (show_core_matrix_inter_main "M_I" n i fk_cs)
         (\ lr ->
           Check_Monad.check
             (case Matrix_Core_Order.alpha_lhs_minus_rhs n alpha lr of {
               Linear_Polynomial.LPoly c cs ->
                 all (in_N n) (c : map snd cs) &&
                   all (\ ia ->
                         any (\ a ->
                               any (\ j ->
                                     Orderings.less_eq delta
                                       (Matrix.index_mat a (ia, j)))
                                 i)
                           (c : map snd cs))
                     i;
             })
             ((((Shows_Literal.showsl_literal
                   "could not strictly orient rule " .
                  Trs_Impl.showsl_rule lr) .
                 Shows_Literal.showsl_literal "\n") .
                Shows_Literal.showsl_literal "where lhs - rhs evaluates to ") .
               Linear_Polynomial.showsl_l_poly
                 (Matrix_Core_Order.alpha_lhs_minus_rhs n alpha lr)))
         checkNS checkNS (Matrix_Core_Order.core_mat_af n alpha)
         (Matrix_Core_Order.core_mat_af n alpha) (Sum_Type.Inr ())
         (Sum_Type.Inr ()) (Sum_Type.Inr ()) (Sum_Type.Inr ()) (Sum_Type.Inr ())
         (Sum_Type.Inr ())
         (\ _ ->
           Set_Impl.set_empty (Phantom_Type.of_phantom Set_Impl.set_impl_nat))
         (\ _ ->
           Error_Monad.catch_error
             (Error_Monad.forallM
               (\ (_, csc) ->
                 Check_Monad.check (all (in_MI n i) (fst csc))
                   (Shows_Literal.showsl_literal
                     " require monotone coefficient in M-I"))
               fk_cs)
             (\ x -> Sum_Type.Inl (snd x)))
         Nothing Nothing Term_Order_Impl.no_complexity_check ();

core_EI_rel_impl ::
  forall a b c.
    (Eq a, Matrix_Core_Order.SN_delta_order a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b, Eq c,
      Shows_Literal.Showl c) => Arith.Nat ->
                                  a -> [Arith.Nat] ->
 [((b, Arith.Nat), ([Matrix.Mat a], Matrix.Mat a))] ->
   Term_Order_Impl.Rel_impl_ext b c ();
core_EI_rel_impl n delta i fk_cs =
  let {
    def = Matrix.smult_mat (Arith.plus delta Arith.one) (Matrix.one_mat n);
    alpha = Matrix_Core_Order.alpha_list_to_Alpha n def fk_cs;
    checkNS =
      (\ lr ->
        Check_Monad.check
          (Matrix_Core_Order.check_lpoly_EI_N n (List.set i)
            (Matrix_Core_Order.alpha_lhs_minus_rhs n alpha lr))
          ((((Shows_Literal.showsl_literal "could not weakly orient rule " .
               Trs_Impl.showsl_rule lr) .
              Shows_Literal.showsl_literal "\n") .
             Shows_Literal.showsl_literal "where lhs - rhs evaluates to ") .
            Linear_Polynomial.showsl_l_poly
              (Matrix_Core_Order.alpha_lhs_minus_rhs n alpha lr)));
  } in Term_Order_Impl.Rel_impl_ext
         (Error_Monad.bind
           (Check_Monad.check (Orderings.less Arith.zero delta)
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
                         Error_Monad.catch_error
                           (Error_Monad.forallM
                             (\ (fk, _) ->
                               Check_Monad.check
                                 (Matrix_Core_Order.check_lpoly_EI_EI n
                                   (List.set i)
                                   (Matrix_Core_Order.inter_lpoly n alpha fk))
                                 ((Shows_Literal.showsl_literal
                                     "cannot ensure that interpretation of symbol " .
                                    Shows_Literal.showsl (fst fk)) .
                                   Shows_Literal.showsl_literal
                                     " is function from E-I^* to E-I"))
                             fk_cs)
                           (\ x -> Sum_Type.Inl (snd x)))))))
         (Sum_Type.Inr ()) (show_core_matrix_inter_main "E_I" n i fk_cs)
         (\ lr ->
           Check_Monad.check
             (Matrix_Core_Order.check_lpoly_EI_PI n delta (List.set i) i
               (Matrix_Core_Order.alpha_lhs_minus_rhs n alpha lr))
             ((((Shows_Literal.showsl_literal
                   "could not strictly orient rule " .
                  Trs_Impl.showsl_rule lr) .
                 Shows_Literal.showsl_literal "\n") .
                Shows_Literal.showsl_literal "where lhs - rhs evaluates to ") .
               Linear_Polynomial.showsl_l_poly
                 (Matrix_Core_Order.alpha_lhs_minus_rhs n alpha lr)))
         checkNS checkNS (Matrix_Core_Order.core_mat_af n alpha)
         (Matrix_Core_Order.core_mat_af n alpha) (Sum_Type.Inr ())
         (Sum_Type.Inr ()) (Sum_Type.Inr ()) (Sum_Type.Inr ()) (Sum_Type.Inr ())
         (Sum_Type.Inr ())
         (\ _ ->
           Set_Impl.set_empty (Phantom_Type.of_phantom Set_Impl.set_impl_nat))
         (\ _ ->
           Error_Monad.catch_error
             (Error_Monad.forallM
               (\ (_, csc) ->
                 Check_Monad.check
                   (all (\ a ->
                          Matrix_Comparison.mat_ge a
                            (Matrix_Core_Order.oneE_I n (List.set i)))
                     (fst csc))
                   (Shows_Literal.showsl_literal
                     " require monotone coefficient in E-I"))
               fk_cs)
             (\ x -> Sum_Type.Inl (snd x)))
         Nothing Nothing Term_Order_Impl.no_complexity_check ();

core_rel_impl ::
  forall a b c.
    (Eq a, Matrix_Core_Order.SN_delta_order a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b, Eq c,
      Shows_Literal.Showl c) => Arith.Nat ->
                                  a -> Core_matrix_mode ->
 [Arith.Nat] ->
   [((b, Arith.Nat), ([Matrix.Mat a], Matrix.Mat a))] ->
     Term_Order_Impl.Rel_impl_ext b c ();
core_rel_impl n delta E_I = core_EI_rel_impl n delta;
core_rel_impl n delta M_I = core_MI_rel_impl n delta;

create_core_matrix_int ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => Core_matrix_inter a Arith.Int ->
                                  Term_Order_Impl.Rel_impl_ext a b ();
create_core_matrix_int rel =
  (case rel of {
    Core_Matrix_Inter mode n a b -> core_rel_impl n Arith.one_int mode a b;
  });

create_core_matrix_fract ::
  forall a b c.
    (Archimedean_Field.Floor_ceiling a, Eq a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b, Eq c,
      Shows_Literal.Showl c) => a -> Core_matrix_inter b a ->
                                       Term_Order_Impl.Rel_impl_ext b c ();
create_core_matrix_fract delta rel =
  (case rel of {
    Core_Matrix_Inter mode n a b -> core_rel_impl n delta mode a b;
  });

}
