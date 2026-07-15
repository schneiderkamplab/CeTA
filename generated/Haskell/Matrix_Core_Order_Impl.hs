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
import qualified HOL;
import qualified Phantom_Type;
import qualified Shows_Literal_Matrix;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Quasi_Order;
import qualified Matrix_Comparison;
import qualified Matrix_Carrier_Impl;
import qualified Term_Rewriting;
import qualified Matrix;
import qualified Arith;

data Core_matrix_mode = E_I | M_I;

data Core_matrix_inter a b =
  Core_Matrix_Inter Core_matrix_mode Arith.Nat [Arith.Nat]
    [((a, Arith.Nat), ([Matrix.Mat b], Matrix.Mat b))];

check_valid_dims ::
  forall a b c.
    (Term_Rewriting.Showl a, Arith.Zero b, Eq b, Quasi_Order.Ord b,
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
              (Term_Rewriting.showsl_literal "coefficients must be in N"))
            (\ _ ->
              Error_Monad.bind
                (Check_Monad.check (Arith.member c (Matrix.carrier_mat n n))
                  (Term_Rewriting.showsl_literal
                    "wrong matrix dimension of constant part"))
                (\ _ ->
                  Check_Monad.check (Arith.equal_nat (Arith.size_list cs) k)
                    ((Term_Rewriting.showsl_literal
                        "number of coefficient of symbol " .
                       Term_Rewriting.showsl f) .
                      Term_Rewriting.showsl_literal
                        " differs from arity of symbol"))));
    })
      b);

show_core_matrix_inter_main ::
  forall a b c.
    (Term_Rewriting.Showl a, Term_Rewriting.Showl b,
      Term_Rewriting.Showl c) => String ->
                                   a -> [Arith.Nat] ->
  [((b, Arith.Nat), ([c], c))] -> String -> String;
show_core_matrix_inter_main mode d idx intr =
  (((((((Term_Rewriting.showsl_lit "core matrix interpretation (mode = " .
          Term_Rewriting.showsl_lit mode) .
         Term_Rewriting.showsl_lit ") with dimension ") .
        Term_Rewriting.showsl d) .
       Term_Rewriting.showsl_lit " and strict indices I = ") .
      Term_Rewriting.showsl_lista (map Arith.suc idx)) .
     Term_Rewriting.showsl_lit " where\n") .
    Term_Rewriting.showsl_sep
      (\ (a, b) ->
        (case a of {
          (f, n) ->
            (\ (cs, c) ->
              ((Term_Rewriting.showsl_lit "[" .
                 Term_Rewriting.showsl_terma
                   (Term_Rewriting.Fun f
                     (map (\ i ->
                            Term_Rewriting.Var
                              ([Arith.char_0x78] ++
                                Term_Rewriting.shows_prec_nat Arith.zero_nat i
                                  []))
                       (Arith.upt Arith.one_nat (Arith.suc n))))) .
                Term_Rewriting.showsl_lit "] = ") .
                Term_Rewriting.showsl_l_poly
                  (Term_Rewriting.LPoly c
                    (zip (map (\ i ->
                                [Arith.char_0x78] ++
                                  Term_Rewriting.shows_prec_nat Arith.zero_nat i
                                    [])
                           (Arith.upt Arith.one_nat (Arith.suc n)))
                      cs)));
        })
          b)
      (Term_Rewriting.showsl_lit "\n") intr) .
    Term_Rewriting.showsl_lit
      "\nand\n[f(x1,..,xn)] = x1 + ... + xn + 1 for all other symbols f\n\n";

in_N ::
  forall a.
    (Eq a, Term_Rewriting.SN_delta_order a,
      Term_Rewriting.Showl a) => Arith.Nat -> Matrix.Mat a -> Bool;
in_N n a =
  Arith.member a (Matrix.carrier_mat n n) &&
    Matrix_Comparison.mat_ge a (Matrix.zero_mat n n);

in_MI ::
  forall a.
    (Eq a, Term_Rewriting.SN_delta_order a,
      Term_Rewriting.Showl a) => Arith.Nat ->
                                   [Arith.Nat] -> Matrix.Mat a -> Bool;
in_MI n i a =
  in_N n a &&
    all (\ ia ->
          any (\ j ->
                Quasi_Order.less_eq Arith.one (Matrix.index_mat a (ia, j)))
            i)
      i;

core_MI_rel_impl ::
  forall a b c.
    (Eq a, Term_Rewriting.SN_delta_order a, Term_Rewriting.Showl a, Eq b,
      Term_Rewriting.Showl b, Eq c,
      Term_Rewriting.Showl c) => Arith.Nat ->
                                   a -> [Arith.Nat] ->
  [((b, Arith.Nat), ([Matrix.Mat a], Matrix.Mat a))] ->
    Term_Rewriting.Rel_impl_ext b c ();
core_MI_rel_impl n delta i fk_cs =
  let {
    def = Matrix.smult_mat (Arith.plus delta Arith.one) (Matrix.one_mat n);
    alpha = Term_Rewriting.alpha_list_to_Alpha n def fk_cs;
    checkNS =
      (\ lr ->
        Check_Monad.check
          (case Term_Rewriting.alpha_lhs_minus_rhs n alpha lr of {
            Term_Rewriting.LPoly c cs -> all (in_N n) (c : map snd cs);
          })
          ((((Term_Rewriting.showsl_literal "could not weakly orient rule " .
               Term_Rewriting.showsl_rule lr) .
              Term_Rewriting.showsl_literal "\n") .
             Term_Rewriting.showsl_literal "where lhs - rhs evaluates to ") .
            Term_Rewriting.showsl_l_poly
              (Term_Rewriting.alpha_lhs_minus_rhs n alpha lr)));
  } in Term_Rewriting.Rel_impl_ext
         (Error_Monad.bind
           (Check_Monad.check (Quasi_Order.less Arith.zero delta)
             (Term_Rewriting.showsl_literal "delta must be positive"))
           (\ _ ->
             Error_Monad.bind
               (Check_Monad.check (all (\ ia -> Arith.less_nat ia n) i)
                 (Term_Rewriting.showsl_literal
                   "indices in I must be below matrix dimension"))
               (\ _ ->
                 Error_Monad.bind
                   (Check_Monad.check (not (null i))
                     (Term_Rewriting.showsl_literal
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
                                 (case Term_Rewriting.inter_lpoly n alpha fk of
                                   {
                                   Term_Rewriting.LPoly c cs ->
                                     all (in_N n) (c : map snd cs) &&
                                       all
 (\ ia ->
   any (\ a ->
         any (\ j -> Quasi_Order.less_eq Arith.one (Matrix.index_mat a (ia, j)))
           i)
     (c : map snd cs))
 i;
                                 })
                                 ((Term_Rewriting.showsl_literal
                                     "cannot ensure that interpretation of symbol " .
                                    Term_Rewriting.showsl (fst fk)) .
                                   Term_Rewriting.showsl_literal
                                     " is function from M-I^* to M-I"))
                             fk_cs)
                           (\ x -> Sum_Type.Inl (snd x)))))))
         (Sum_Type.Inr ()) (show_core_matrix_inter_main "M_I" n i fk_cs)
         (\ lr ->
           Check_Monad.check
             (case Term_Rewriting.alpha_lhs_minus_rhs n alpha lr of {
               Term_Rewriting.LPoly c cs ->
                 all (in_N n) (c : map snd cs) &&
                   all (\ ia ->
                         any (\ a ->
                               any (\ j ->
                                     Quasi_Order.less_eq delta
                                       (Matrix.index_mat a (ia, j)))
                                 i)
                           (c : map snd cs))
                     i;
             })
             ((((Term_Rewriting.showsl_literal
                   "could not strictly orient rule " .
                  Term_Rewriting.showsl_rule lr) .
                 Term_Rewriting.showsl_literal "\n") .
                Term_Rewriting.showsl_literal "where lhs - rhs evaluates to ") .
               Term_Rewriting.showsl_l_poly
                 (Term_Rewriting.alpha_lhs_minus_rhs n alpha lr)))
         checkNS checkNS (Term_Rewriting.core_mat_af n alpha)
         (Term_Rewriting.core_mat_af n alpha) (Sum_Type.Inr ())
         (Sum_Type.Inr ()) (Sum_Type.Inr ()) (Sum_Type.Inr ()) (Sum_Type.Inr ())
         (Sum_Type.Inr ())
         (\ _ -> Arith.set_empty (Phantom_Type.of_phantom Arith.set_impl_nat))
         (\ _ ->
           Error_Monad.catch_error
             (Error_Monad.forallM
               (\ (_, csc) ->
                 Check_Monad.check (all (in_MI n i) (fst csc))
                   (Term_Rewriting.showsl_literal
                     " require monotone coefficient in M-I"))
               fk_cs)
             (\ x -> Sum_Type.Inl (snd x)))
         Nothing Nothing Term_Rewriting.no_complexity_check ();

core_EI_rel_impl ::
  forall a b c.
    (Eq a, Term_Rewriting.SN_delta_order a, Term_Rewriting.Showl a, Eq b,
      Term_Rewriting.Showl b, Eq c,
      Term_Rewriting.Showl c) => Arith.Nat ->
                                   a -> [Arith.Nat] ->
  [((b, Arith.Nat), ([Matrix.Mat a], Matrix.Mat a))] ->
    Term_Rewriting.Rel_impl_ext b c ();
core_EI_rel_impl n delta i fk_cs =
  let {
    def = Matrix.smult_mat (Arith.plus delta Arith.one) (Matrix.one_mat n);
    alpha = Term_Rewriting.alpha_list_to_Alpha n def fk_cs;
    checkNS =
      (\ lr ->
        Check_Monad.check
          (Term_Rewriting.check_lpoly_EI_N n (Arith.set i)
            (Term_Rewriting.alpha_lhs_minus_rhs n alpha lr))
          ((((Term_Rewriting.showsl_literal "could not weakly orient rule " .
               Term_Rewriting.showsl_rule lr) .
              Term_Rewriting.showsl_literal "\n") .
             Term_Rewriting.showsl_literal "where lhs - rhs evaluates to ") .
            Term_Rewriting.showsl_l_poly
              (Term_Rewriting.alpha_lhs_minus_rhs n alpha lr)));
  } in Term_Rewriting.Rel_impl_ext
         (Error_Monad.bind
           (Check_Monad.check (Quasi_Order.less Arith.zero delta)
             (Term_Rewriting.showsl_literal "delta must be positive"))
           (\ _ ->
             Error_Monad.bind
               (Check_Monad.check (all (\ ia -> Arith.less_nat ia n) i)
                 (Term_Rewriting.showsl_literal
                   "indices in I must be below matrix dimension"))
               (\ _ ->
                 Error_Monad.bind
                   (Check_Monad.check (not (null i))
                     (Term_Rewriting.showsl_literal
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
                                 (Term_Rewriting.check_lpoly_EI_EI n
                                   (Arith.set i)
                                   (Term_Rewriting.inter_lpoly n alpha fk))
                                 ((Term_Rewriting.showsl_literal
                                     "cannot ensure that interpretation of symbol " .
                                    Term_Rewriting.showsl (fst fk)) .
                                   Term_Rewriting.showsl_literal
                                     " is function from E-I^* to E-I"))
                             fk_cs)
                           (\ x -> Sum_Type.Inl (snd x)))))))
         (Sum_Type.Inr ()) (show_core_matrix_inter_main "E_I" n i fk_cs)
         (\ lr ->
           Check_Monad.check
             (Term_Rewriting.check_lpoly_EI_PI n delta (Arith.set i) i
               (Term_Rewriting.alpha_lhs_minus_rhs n alpha lr))
             ((((Term_Rewriting.showsl_literal
                   "could not strictly orient rule " .
                  Term_Rewriting.showsl_rule lr) .
                 Term_Rewriting.showsl_literal "\n") .
                Term_Rewriting.showsl_literal "where lhs - rhs evaluates to ") .
               Term_Rewriting.showsl_l_poly
                 (Term_Rewriting.alpha_lhs_minus_rhs n alpha lr)))
         checkNS checkNS (Term_Rewriting.core_mat_af n alpha)
         (Term_Rewriting.core_mat_af n alpha) (Sum_Type.Inr ())
         (Sum_Type.Inr ()) (Sum_Type.Inr ()) (Sum_Type.Inr ()) (Sum_Type.Inr ())
         (Sum_Type.Inr ())
         (\ _ -> Arith.set_empty (Phantom_Type.of_phantom Arith.set_impl_nat))
         (\ _ ->
           Error_Monad.catch_error
             (Error_Monad.forallM
               (\ (_, csc) ->
                 Check_Monad.check
                   (all (\ a ->
                          Matrix_Comparison.mat_ge a
                            (Term_Rewriting.oneE_I n (Arith.set i)))
                     (fst csc))
                   (Term_Rewriting.showsl_literal
                     " require monotone coefficient in E-I"))
               fk_cs)
             (\ x -> Sum_Type.Inl (snd x)))
         Nothing Nothing Term_Rewriting.no_complexity_check ();

core_rel_impl ::
  forall a b c.
    (Eq a, Term_Rewriting.SN_delta_order a, Term_Rewriting.Showl a, Eq b,
      Term_Rewriting.Showl b, Eq c,
      Term_Rewriting.Showl c) => Arith.Nat ->
                                   a -> Core_matrix_mode ->
  [Arith.Nat] ->
    [((b, Arith.Nat), ([Matrix.Mat a], Matrix.Mat a))] ->
      Term_Rewriting.Rel_impl_ext b c ();
core_rel_impl n delta E_I = core_EI_rel_impl n delta;
core_rel_impl n delta M_I = core_MI_rel_impl n delta;

create_core_matrix_int ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Eq b,
      Term_Rewriting.Showl b) => Core_matrix_inter a Arith.Int ->
                                   Term_Rewriting.Rel_impl_ext a b ();
create_core_matrix_int rel =
  (case rel of {
    Core_Matrix_Inter mode n a b -> core_rel_impl n Arith.one_int mode a b;
  });

create_core_matrix_fract ::
  forall a b c.
    (Term_Rewriting.Floor_ceiling a, Eq a, Term_Rewriting.Showl a, Eq b,
      Term_Rewriting.Showl b, Eq c,
      Term_Rewriting.Showl c) => a -> Core_matrix_inter b a ->
Term_Rewriting.Rel_impl_ext b c ();
create_core_matrix_fract delta rel =
  (case rel of {
    Core_Matrix_Inter mode n a b -> core_rel_impl n delta mode a b;
  });

}
