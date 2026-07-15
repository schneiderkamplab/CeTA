{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Poly_Order_Neg(Poly_carrier, check_poly_inter_list_neg,
                  create_negpoly_rel_impl)
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
import qualified Map_Choice;
import qualified Compare_Order_Instances;
import qualified Show_Instances;
import qualified Term_Order;
import qualified Error_Monad;
import qualified Complexity;
import qualified Compare;
import qualified List_Lexorder;
import qualified Show_Literal_Polynomial;
import qualified Poly_Order;
import qualified Check_Monad;
import qualified HOL;
import qualified Sum_Type;
import qualified Term_Rewriting;
import qualified Shows_Literal;
import qualified Polynomials;
import qualified Quasi_Order;
import qualified SN_Orders;
import qualified SN_Order_Carrier;
import qualified Arith;

class (Arith.Ring a, SN_Orders.Poly_carrier a) => Poly_carrier a where {
};

instance Poly_carrier Arith.Int where {
};

default_I ::
  forall a.
    (Poly_carrier a) => a -> Arith.Nat -> [(Polynomials.Monom Arith.Nat, a)];
default_I def n = Polynomials.zero_poly;

poly_convert ::
  forall a b.
    (Eq a, Quasi_Order.Linorder a, Eq b,
      Poly_carrier b) => [(Polynomials.Monom a, b)] ->
                           [(Polynomials.Monom a, b)];
poly_convert p =
  Polynomials.poly_subst
    (\ v -> [(Polynomials.var_monom v, Arith.uminus Arith.one)]) p;

check_poly_neg_gt ::
  forall a b.
    (Eq a, Poly_carrier a, Eq b,
      Quasi_Order.Linorder b) => (a -> a -> Bool) ->
                                   [(Polynomials.Monom b, a)] ->
                                     [(Polynomials.Monom b, a)] -> Bool;
check_poly_neg_gt gt p q = let {
                             pa = poly_convert p;
                             a = poly_convert q;
                           } in Polynomials.check_poly_gt gt pa a;

check_neg_s ::
  forall a b c.
    (Eq a, Poly_carrier a, Shows_Literal.Showl a, Shows_Literal.Showl b, Eq c,
      Quasi_Order.Linorder c,
      Shows_Literal.Showl c) => (a -> a -> Bool) ->
                                  ((b, Arith.Nat) ->
                                    [(Polynomials.Monom Arith.Nat, a)]) ->
                                    (Term_Rewriting.Term b c,
                                      Term_Rewriting.Term b c) ->
                                      Sum_Type.Sum (String -> String) ();
check_neg_s gt i =
  (\ (s, t) ->
    let {
      p = Poly_Order.eval_term i s;
      q = Poly_Order.eval_term i t;
    } in Check_Monad.check (check_poly_neg_gt gt p q)
           (((((((Shows_Literal.showsl_literal "could not ensure " .
                   Term_Rewriting.showsl_terma s) .
                  Shows_Literal.showsl_literal " > ") .
                 Term_Rewriting.showsl_terma t) .
                Shows_Literal.showsl_literal " since we\ncould not ensure ") .
               Show_Literal_Polynomial.showsl_poly p) .
              Shows_Literal.showsl_literal " > ") .
             Show_Literal_Polynomial.showsl_poly q));

check_poly_neg_ge ::
  forall a b.
    (Eq a, Quasi_Order.Linorder a, Eq b,
      Poly_carrier b) => [(Polynomials.Monom a, b)] ->
                           [(Polynomials.Monom a, b)] -> Bool;
check_poly_neg_ge p q = let {
                          pa = poly_convert p;
                          a = poly_convert q;
                        } in Polynomials.check_poly_ge pa a;

check_neg_ns ::
  forall a b c.
    (Shows_Literal.Showl a, Eq b, Quasi_Order.Preorder b, Poly_carrier b,
      Shows_Literal.Showl b, Eq c, Quasi_Order.Linorder c,
      Shows_Literal.Showl c) => ((a, Arith.Nat) ->
                                  [(Polynomials.Monom Arith.Nat, b)]) ->
                                  (Term_Rewriting.Term a c,
                                    Term_Rewriting.Term a c) ->
                                    Sum_Type.Sum (String -> String) ();
check_neg_ns i =
  (\ (s, t) ->
    let {
      p = Poly_Order.eval_term i s;
      q = Poly_Order.eval_term i t;
    } in Check_Monad.check (check_poly_neg_ge p q)
           (((((((Shows_Literal.showsl_literal "could not ensure " .
                   Term_Rewriting.showsl_terma s) .
                  Shows_Literal.showsl_literal " >= ") .
                 Term_Rewriting.showsl_terma t) .
                Shows_Literal.showsl_literal " since we\ncould not ensure ") .
               Show_Literal_Polynomial.showsl_poly p) .
              Shows_Literal.showsl_literal " >= ") .
             Show_Literal_Polynomial.showsl_poly q));

poly_inter_list_to_inter_neg ::
  forall a b.
    (Poly_carrier a,
      Compare.Compare_order b) => a -> [((b, Arith.Nat),
  [(Polynomials.Monom Arith.Nat, a)])] ->
 (b, Arith.Nat) -> [(Polynomials.Monom Arith.Nat, a)];
poly_inter_list_to_inter_neg def i =
  Map_Choice.fun_of_map_fun (Map_Choice.ceta_map_of i)
    (\ fn -> default_I def (snd fn));

check_poly_weak_mono_easy ::
  forall a b.
    (Eq a, Quasi_Order.Linorder a, Eq b,
      Poly_carrier b) => [(Polynomials.Monom a, b)] -> Bool;
check_poly_weak_mono_easy p =
  Polynomials.check_poly_weak_mono_all
    (Polynomials.monom_mult_poly (Polynomials.one_monom, Arith.uminus Arith.one)
      (poly_convert p));

check_poly_weak_mono_and_neg ::
  forall a b.
    (Eq a, Quasi_Order.Linorder a, Eq b,
      Poly_carrier b) => [(Polynomials.Monom a, b)] -> Bool;
check_poly_weak_mono_and_neg p =
  check_poly_neg_ge Polynomials.zero_poly p && check_poly_weak_mono_easy p;

check_poly_inter_list_neg ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Eq b,
      Poly_carrier b) => [((a, Arith.Nat),
                            [(Polynomials.Monom Arith.Nat, b)])] ->
                           Sum_Type.Sum (String -> String) ();
check_poly_inter_list_neg i =
  Error_Monad.bind
    (Check_Monad.check (Arith.distinct (map fst i))
      (Shows_Literal.showsl_literal "some symbol has two interpretations"))
    (\ _ ->
      Error_Monad.catch_error
        (Error_Monad.catch_error
          (Error_Monad.forallM
            (\ x ->
              (if (case x of {
                    (_, a) -> check_poly_weak_mono_and_neg a;
                  })
                then Sum_Type.Inr () else Sum_Type.Inl x))
            i)
          (\ x -> Sum_Type.Inl (snd x)))
        (\ x ->
          Sum_Type.Inl
            (case x of {
              (a, b) ->
                (case a of {
                  (f, _) ->
                    (\ _ ->
                      Shows_Literal.showsl_literal
                        "could not ensure weak-mono-, or neg.-property of interpretation of symbol " .
                        Shows_Literal.showsl f);
                })
                  b;
            })));

create_negpoly_rel_impl ::
  forall a b c.
    (Eq a, Quasi_Order.Preorder a, Poly_carrier a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b, Shows_Literal.Showl b, Eq c,
      Quasi_Order.Linorder c,
      Shows_Literal.Showl c) => Sum_Type.Sum (String -> String) () ->
                                  a -> (a -> a -> Bool) ->
 Bool ->
   [((b, Arith.Nat), [(Polynomials.Monom Arith.Nat, a)])] ->
     Term_Rewriting.Rel_impl_ext b c ();
create_negpoly_rel_impl cI def gt discrete i =
  let {
    j = poly_inter_list_to_inter_neg def i;
    x = Polynomials.poly_subst
          (\ n ->
            Polynomials.poly_of
              (Polynomials.PVar
                ([Arith.char_0x78, Arith.char_0x5F] ++
                  Show_Instances.shows_prec_nat Arith.zero_nat n [])));
  } in Term_Rewriting.Rel_impl_ext
         (Error_Monad.bind cI (\ _ -> check_poly_inter_list_neg i))
         (Sum_Type.Inr ())
         (Shows_Literal.showsl_literal "polynomial interpretation\n" .
           Shows_Literal.showsl_sep
             (\ (a, b) ->
               (case a of {
                 (f, n) ->
                   (\ p ->
                     ((((Shows_Literal.showsl_literal "Pol(" .
                          Shows_Literal.showsl f) .
                         Shows_Literal.showsl_literal "/") .
                        Shows_Literal.showsl_nat n) .
                       Shows_Literal.showsl_literal ") = ") .
                       Show_Literal_Polynomial.showsl_poly (x p));
               })
                 b)
             (Shows_Literal.showsl_literal "\n") i)
         (check_neg_s gt j) (check_neg_ns j)
         (\ _ ->
           Sum_Type.Inl
             (Shows_Literal.showsl_lit "top-order not supported by neg-polys"))
         Term_Order.full_af Term_Order.full_af
         (Sum_Type.Inl
           (Shows_Literal.showsl_lit "SN not supported by neg-polys"))
         (Sum_Type.Inr ())
         (Sum_Type.Inl
           (Shows_Literal.showsl_lit "Ce not supported by neg-polys"))
         (Sum_Type.Inr ())
         (Sum_Type.Inl
           (Shows_Literal.showsl_lit "top-mono not supported by neg-polys"))
         (Sum_Type.Inl
           (Shows_Literal.showsl_lit "top-refl not supported by neg-polys"))
         Term_Order.empty_af
         (\ _ ->
           Sum_Type.Inl
             (Shows_Literal.showsl_lit
               "strict monotonicity not supported by neg-polys"))
         Nothing Nothing Term_Rewriting.no_complexity_check ();

}
