{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Poly_Order(eval_term, create_nlpoly_rel_impl, create_nlpoly_non_inf_order)
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
import qualified Show_Instances;
import qualified List_Lexorder;
import qualified Missing_List;
import qualified Complexity;
import qualified Set_Interval;
import qualified Map_Choice;
import qualified Non_Inf_Order;
import qualified Compare;
import qualified Compare_Order_Instances;
import qualified Error_Monad;
import qualified Non_Inf_Order_Impl;
import qualified Show_Literal_Polynomial;
import qualified Check_Monad;
import qualified HOL;
import qualified Sum_Type;
import qualified Term_Rewriting;
import qualified Shows_Literal;
import qualified SN_Orders;
import qualified Polynomials;
import qualified Quasi_Order;
import qualified Arith;

max_v ::
  forall a b.
    (Arith.Zero a,
      Quasi_Order.Ord a) => a -> ((b, Arith.Nat) ->
                                   [(Polynomials.Monom Arith.Nat, a)]) ->
                                   [(b, Arith.Nat)] -> a;
max_v v i fs =
  Quasi_Order.max v
    (Arith.foldr
      (\ f m ->
        Quasi_Order.max m
          (fst (Polynomials.poly_split Polynomials.one_monom (i f))))
      fs Arith.zero);

eval_term ::
  forall a b c.
    (Eq b, SN_Orders.Poly_carrier b, Eq c,
      Quasi_Order.Linorder c) => ((a, Arith.Nat) ->
                                   [(Polynomials.Monom Arith.Nat, b)]) ->
                                   Term_Rewriting.Term a c ->
                                     [(Polynomials.Monom c, b)];
eval_term uu (Term_Rewriting.Var x) = [(Polynomials.var_monom x, Arith.one)];
eval_term i (Term_Rewriting.Fun f ts) =
  let {
    ps = map (eval_term i) ts;
    n = Arith.size_list ts;
  } in Polynomials.poly_subst
         (\ ia ->
           (if Arith.less_nat ia n then Arith.nth ps ia
             else Polynomials.zero_poly))
         (i (f, n));

check_s ::
  forall a b c.
    (Eq a, SN_Orders.Poly_carrier a, Shows_Literal.Showl a,
      Shows_Literal.Showl b, Eq c, Quasi_Order.Linorder c,
      Shows_Literal.Showl c) => (a -> a -> Bool) ->
                                  ((b, Arith.Nat) ->
                                    [(Polynomials.Monom Arith.Nat, a)]) ->
                                    (Term_Rewriting.Term b c,
                                      Term_Rewriting.Term b c) ->
                                      Sum_Type.Sum (String -> String) ();
check_s gt i =
  (\ (s, t) ->
    let {
      p = eval_term i s;
      q = eval_term i t;
    } in Check_Monad.check (Polynomials.check_poly_gt gt p q)
           (((((((Shows_Literal.showsl_literal "could not ensure " .
                   Term_Rewriting.showsl_terma s) .
                  Shows_Literal.showsl_literal " > ") .
                 Term_Rewriting.showsl_terma t) .
                Shows_Literal.showsl_literal " since we\ncould not ensure ") .
               Show_Literal_Polynomial.showsl_poly p) .
              Shows_Literal.showsl_literal " > ") .
             Show_Literal_Polynomial.showsl_poly q));

square_possibilities ::
  forall a b.
    (Eq a, SN_Orders.Poly_carrier a, Eq b,
      Quasi_Order.Linorder b) => (a -> [a]) ->
                                   [(Polynomials.Monom b, a)] ->
                                     [[(Polynomials.Monom b, a)]];
square_possibilities sqrt p =
  let {
    roots =
      map (\ x ->
            map (\ a -> (x, a))
              (sqrt (fst (Polynomials.poly_split
                           (Polynomials.times_monom (Polynomials.var_monom x)
                             (Polynomials.var_monom x))
                           p))))
        (Polynomials.poly_vars_list p);
    choices =
      (if Arith.membera roots [] then [] else Missing_List.concat_lists roots);
    polys =
      map (\ xas ->
            Polynomials.poly_of
              (Polynomials.PSum
                (map (\ (x, a) ->
                       Polynomials.PMult
                         [Polynomials.PVar x, Polynomials.PNum a])
                  xas)))
        choices;
  } in polys;

check_quadratic ::
  forall a.
    (Eq a,
      SN_Orders.Poly_carrier a) => (a -> [a]) ->
                                     [(Polynomials.Monom Arith.Nat, a)] ->
                                       Sum_Type.Sum (String -> String) ();
check_quadratic sqrt p =
  Error_Monad.bind
    (Check_Monad.check
      (Arith.equal_nat (Polynomials.poly_degree p)
        (Arith.nat_of_integer (2 :: Integer)))
      (Shows_Literal.showsl_literal "not quadratic"))
    (\ _ ->
      let {
        polys = square_possibilities sqrt p;
      } in Check_Monad.check
             (any (\ q ->
                    Polynomials.check_poly_eq (Polynomials.poly_mult q q) p)
               polys)
             (Shows_Literal.showsl_literal
               "could not find quadratic polynomial"));

check_quadratic_ge_const ::
  forall a b c.
    (Eq a, SN_Orders.Poly_carrier a, Eq c,
      Quasi_Order.Linorder c) => (a -> [a]) ->
                                   ((b, Arith.Nat) ->
                                     [(Polynomials.Monom Arith.Nat, a)]) ->
                                     (Term_Rewriting.Term b c,
                                       Term_Rewriting.Term b c) ->
                                       Sum_Type.Sum (String -> String) ();
check_quadratic_ge_const sq i st =
  (case st of {
    (s, t) ->
      Error_Monad.bind
        (Check_Monad.check (not (Term_Rewriting.is_Var s))
          (Shows_Literal.showsl_literal "require non-variables as arguments"))
        (\ _ ->
          let {
            pt = eval_term i t;
          } in (case Polynomials.poly_split Polynomials.one_monom pt of {
                 (c, p0) ->
                   Error_Monad.bind
                     (Check_Monad.check (p0 == Polynomials.zero_poly)
                       (Shows_Literal.showsl_literal
                         "rhs must evaluate to constant"))
                     (\ _ ->
                       let {
                         ps = i (Arith.the (Term_Rewriting.root s));
                       } in (case Polynomials.poly_split Polynomials.one_monom
                                    ps
                              of {
                              (d, psx) ->
                                Error_Monad.bind
                                  (Check_Monad.check (Quasi_Order.less_eq c d)
                                    (Shows_Literal.showsl_literal
                                      "problem in comparing constants"))
                                  (\ _ -> check_quadratic sq psx);
                            }));
               }));
  });

check_ns ::
  forall a b c.
    (Shows_Literal.Showl a, Eq b, SN_Orders.Poly_carrier b,
      Shows_Literal.Showl b, Eq c, Quasi_Order.Linorder c,
      Shows_Literal.Showl c) => ((a, Arith.Nat) ->
                                  [(Polynomials.Monom Arith.Nat, b)]) ->
                                  (Term_Rewriting.Term a c,
                                    Term_Rewriting.Term a c) ->
                                    Sum_Type.Sum (String -> String) ();
check_ns i =
  (\ (s, t) ->
    let {
      p = eval_term i s;
      q = eval_term i t;
    } in Check_Monad.check (Polynomials.check_poly_ge p q)
           (((((((Shows_Literal.showsl_literal "could not ensure " .
                   Term_Rewriting.showsl_terma s) .
                  Shows_Literal.showsl_literal " >= ") .
                 Term_Rewriting.showsl_terma t) .
                Shows_Literal.showsl_literal " since we\ncould not ensure ") .
               Show_Literal_Polynomial.showsl_poly p) .
              Shows_Literal.showsl_literal " >= ") .
             Show_Literal_Polynomial.showsl_poly q));

check_cc ::
  forall a b c.
    (Eq a, SN_Orders.Poly_carrier a, Shows_Literal.Showl a,
      Shows_Literal.Showl b, Eq c, Quasi_Order.Linorder c,
      Shows_Literal.Showl c) => (a -> [a]) ->
                                  (a -> a -> Bool) ->
                                    ((b, Arith.Nat) ->
                                      [(Polynomials.Monom Arith.Nat, a)]) ->
                                      Non_Inf_Order_Impl.C_constraint b c ->
Sum_Type.Sum (String -> String) ();
check_cc sq gt i (Non_Inf_Order_Impl.Unconditional_C False st) =
  (if Error_Monad.isOK (check_quadratic_ge_const sq i st) then Sum_Type.Inr ()
    else check_ns i st);
check_cc sq gt i (Non_Inf_Order_Impl.Unconditional_C True st) = check_s gt i st;
check_cc sq gt i (Non_Inf_Order_Impl.Conditional_C True (u, v) (s, t)) =
  let {
    ss = eval_term i s;
    tt = eval_term i t;
    uu = eval_term i u;
    vv = eval_term i v;
  } in (if Polynomials.check_poly_gt gt ss tt then Sum_Type.Inr ()
         else Check_Monad.check
                (Polynomials.check_poly_ge (Polynomials.poly_add ss vv)
                  (Polynomials.poly_add tt uu))
                (((((((Shows_Literal.showsl_literal "could not ensure " .
                        Term_Rewriting.showsl_terma u) .
                       Shows_Literal.showsl_literal " > ") .
                      Term_Rewriting.showsl_terma v) .
                     Shows_Literal.showsl_literal " ==> ") .
                    Term_Rewriting.showsl_terma s) .
                   Shows_Literal.showsl_literal " > ") .
                  Term_Rewriting.showsl_terma t));
check_cc sq gt i (Non_Inf_Order_Impl.Conditional_C False (u, v) (s, t)) =
  (if Error_Monad.isOK (check_quadratic_ge_const sq i (s, t))
    then Sum_Type.Inr ()
    else let {
           ss = eval_term i s;
           tt = eval_term i t;
           uu = eval_term i u;
           vv = eval_term i v;
         } in (if Polynomials.check_poly_ge ss tt then Sum_Type.Inr ()
                else Check_Monad.check
                       (Polynomials.check_poly_ge (Polynomials.poly_add ss vv)
                         (Polynomials.poly_add tt uu))
                       (((((((Shows_Literal.showsl_literal "could not ensure " .
                               Term_Rewriting.showsl_terma u) .
                              Shows_Literal.showsl_literal " >= ") .
                             Term_Rewriting.showsl_terma v) .
                            Shows_Literal.showsl_literal " ==> ") .
                           Term_Rewriting.showsl_terma s) .
                          Shows_Literal.showsl_literal " >= ") .
                         Term_Rewriting.showsl_terma t)));

default_I ::
  forall a.
    (SN_Orders.Poly_carrier a) => a -> Arith.Nat ->
 [(Polynomials.Monom Arith.Nat, a)];
default_I def n =
  (Polynomials.one_monom, def) :
    map (\ i -> (Polynomials.var_monom i, Arith.one))
      (Arith.upt Arith.zero_nat n);

check_ge_v ::
  forall a.
    (SN_Orders.Poly_carrier a) => a -> [(Polynomials.Monom Arith.Nat, a)] ->
 Bool;
check_ge_v v p =
  (case p of {
    [] -> True;
    [(m, c)] ->
      Polynomials.equal_monom m Polynomials.one_monom &&
        Quasi_Order.less_eq c v;
    (_, _) : _ : _ -> False;
  });

poly_inter_list_to_inter ::
  forall a b.
    (SN_Orders.Poly_carrier a,
      Compare.Compare_order b) => a -> [((b, Arith.Nat),
  [(Polynomials.Monom Arith.Nat, a)])] ->
 (b, Arith.Nat) -> [(Polynomials.Monom Arith.Nat, a)];
poly_inter_list_to_inter def i =
  Map_Choice.fun_of_map_fun (Map_Choice.ceta_map_of i)
    (\ fn -> default_I def (snd fn));

create_dep ::
  forall a b.
    (Eq a, SN_Orders.Poly_carrier a, Compare.Compare_order b,
      Eq b) => Bool ->
                 a -> [((b, Arith.Nat), [(Polynomials.Monom Arith.Nat, a)])] ->
                        (b, Arith.Nat) -> Arith.Nat -> Non_Inf_Order.Dependance;
create_dep discrete def i =
  let {
    fs = Arith.remdups (map fst i);
    ii = poly_inter_list_to_inter def i;
    fsres =
      map (\ fn ->
            let {
              p = ii fn;
              vars = Polynomials.poly_vars_list p;
              is = Arith.upt Arith.zero_nat (snd fn);
              a = map (\ ia ->
                        (if Arith.membera vars ia
                          then (if Polynomials.check_poly_weak_mono_smart
                                     discrete p ia
                                 then Non_Inf_Order.Increase
                                 else (if Polynomials.check_poly_weak_anti_mono_smart
    discrete p ia
then Non_Inf_Order.Decrease else Non_Inf_Order.Wild))
                          else Non_Inf_Order.Ignore))
                    is;
            } in (fn, a))
        fs;
    iii = Map_Choice.fun_of_map_funa (Map_Choice.ceta_map_of fsres)
            (\ _ _ -> Non_Inf_Order.Increase) Arith.nth;
  } in iii;

strongly_linear ::
  forall a.
    (SN_Orders.Poly_carrier a) => Arith.Nat ->
                                    [(Polynomials.Monom Arith.Nat, a)] ->
                                      a -> Bool;
strongly_linear x p v =
  (if Arith.equal_nat x Arith.zero_nat then check_ge_v v p
    else (case Polynomials.poly_split
                 (Polynomials.var_monom (Arith.minus_nat x Arith.one_nat)) p
           of {
           (a, pa) ->
             Quasi_Order.less_eq a Arith.one &&
               strongly_linear (Arith.minus_nat x Arith.one_nat) pa v;
         }));

poly_inter_to_af ::
  forall a b.
    (Compare.Compare_order a) => [((a, Arith.Nat),
                                    [(Polynomials.Monom Arith.Nat, b)])] ->
                                   (a, Arith.Nat) -> Arith.Set Arith.Nat;
poly_inter_to_af i =
  Map_Choice.fun_of_map_fun
    (Map_Choice.ceta_map_of
      (map (\ (fn, e) -> (fn, Polynomials.poly_vars e)) i))
    (\ fn -> Set_Interval.atLeastLessThan Arith.zero_nat (snd fn));

sl_complexity_sig_check ::
  forall a b.
    (SN_Orders.Poly_carrier b) => ((a, Arith.Nat) ->
                                    [(Polynomials.Monom Arith.Nat, b)]) ->
                                    b -> [(a, Arith.Nat)] ->
   Sum_Type.Sum (a, Arith.Nat) ();
sl_complexity_sig_check i v f =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ (fa, n) -> Check_Monad.check (strongly_linear n (i (fa, n)) v) (fa, n))
      f)
    (\ x -> Sum_Type.Inl (snd x));

sl_complexity_check ::
  forall a b.
    (SN_Orders.Poly_carrier a,
      Shows_Literal.Showl b) => a -> ((b, Arith.Nat) ->
                                       [(Polynomials.Monom Arith.Nat, a)]) ->
                                       [(b, Arith.Nat)] ->
 Sum_Type.Sum (String -> String) ();
sl_complexity_check v i f =
  let {
    w = max_v v i f;
  } in Error_Monad.catch_error (sl_complexity_sig_check i w f)
         (\ x ->
           Sum_Type.Inl
             (case x of {
               (fa, _) ->
                 (Shows_Literal.showsl_literal "symbol " .
                   Shows_Literal.showsl fa) .
                   Shows_Literal.showsl_literal
                     " does not possess a strongly linear interpretation";
             }));

nl_complexity_check ::
  forall a b c.
    (Shows_Literal.Showl a,
      SN_Orders.Poly_carrier b) => ((a, Arith.Nat) ->
                                     [(Polynomials.Monom Arith.Nat, b)]) ->
                                     Complexity.Complexity_measure a c ->
                                       Complexity.Complexity_class ->
 Sum_Type.Sum (String -> String) ();
nl_complexity_check i (Complexity.Derivational_Complexity f) cc =
  Error_Monad.bind (sl_complexity_check Arith.zero i f)
    (\ _ ->
      Check_Monad.check
        (Complexity.less_eq_complexity_class
          (Complexity.Comp_Poly Arith.one_nat) cc)
        (Shows_Literal.showsl_literal
          "cannot deduce constant complexity for derivational complexity"));
nl_complexity_check i (Complexity.Runtime_Complexity c d)
  (Complexity.Comp_Poly deg) =
  Error_Monad.bind (sl_complexity_check Arith.one i c)
    (\ _ ->
      Error_Monad.catch_error
        (Error_Monad.forallM
          (\ f ->
            Check_Monad.check
              (Arith.less_eq_nat (Polynomials.poly_degree (i f)) deg)
              ((Shows_Literal.showsl_literal "degree of interpretation for " .
                 Shows_Literal.showsl_prod f) .
                Shows_Literal.showsl_literal " exceeds bound "))
          d)
        (\ x -> Sum_Type.Inl (snd x)));

check_poly_inter_list ::
  forall a b.
    (Eq a, Eq b,
      SN_Orders.Poly_carrier b) => Bool ->
                                     [((a, Arith.Nat),
[(Polynomials.Monom Arith.Nat, b)])] ->
                                       Sum_Type.Sum
 (Sum_Type.Sum (String -> String) (a, [(Polynomials.Monom Arith.Nat, b)])) ();
check_poly_inter_list discrete i =
  Error_Monad.bind
    (Check_Monad.check (Arith.distinct (map fst i))
      (Sum_Type.Inl
        (Shows_Literal.showsl_literal "some symbol has two interpretations")))
    (\ _ ->
      Error_Monad.catch_error
        (Error_Monad.catch_error
          (Error_Monad.forallM
            (\ x ->
              (if (case x of {
                    (_, a) ->
                      Polynomials.check_poly_weak_mono_and_pos discrete a;
                  })
                then Sum_Type.Inr () else Sum_Type.Inl x))
            i)
          (\ x -> Sum_Type.Inl (snd x)))
        (\ x ->
          Sum_Type.Inl
            (case x of {
              (a, b) -> (case a of {
                          (f, _) -> (\ p -> Sum_Type.Inr (f, p));
                        })
                          b;
            })));

poly_inter_to_mono_af ::
  forall a b.
    (Eq a, SN_Orders.Poly_carrier a,
      Compare.Compare_order b) => Bool ->
                                    Bool ->
                                      (a -> a -> Bool) ->
[((b, Arith.Nat), [(Polynomials.Monom Arith.Nat, a)])] ->
  (b, Arith.Nat) -> Arith.Set Arith.Nat;
poly_inter_to_mono_af discrete power_mono gt i =
  Map_Choice.fun_of_map_fun
    (Map_Choice.ceta_map_of
      (map (\ (a, b) ->
             (case a of {
               (f, n) ->
                 (\ e ->
                   ((f, n),
                     Arith.set
                       (filter
                         (\ ia ->
                           Polynomials.check_poly_weak_mono_and_pos discrete
                             e &&
                             Polynomials.check_poly_strict_mono_smart discrete
                               power_mono gt e ia)
                         (Arith.upt Arith.zero_nat n))));
             })
               b)
        i))
    (\ fn -> Set_Interval.atLeastLessThan Arith.zero_nat (snd fn));

create_nlpoly_rel_impl ::
  forall a b c.
    (Eq a, SN_Orders.Poly_carrier a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b, Shows_Literal.Showl b, Eq c,
      Quasi_Order.Linorder c,
      Shows_Literal.Showl c) => Sum_Type.Sum (String -> String) () ->
                                  a -> (a -> a -> Bool) ->
 Bool ->
   Bool ->
     [((b, Arith.Nat), [(Polynomials.Monom Arith.Nat, a)])] ->
       Term_Rewriting.Rel_impl_ext b c ();
create_nlpoly_rel_impl cI def gt power_mono discrete i =
  let {
    j = poly_inter_list_to_inter def i;
    x = Polynomials.poly_subst
          (\ n ->
            Polynomials.poly_of
              (Polynomials.PVar
                ([Arith.char_0x78, Arith.char_0x5F] ++
                  Show_Instances.shows_prec_nat Arith.zero_nat n [])));
  } in Term_Rewriting.Rel_impl_ext
         (Error_Monad.bind cI
           (\ _ ->
             Error_Monad.catch_error (check_poly_inter_list discrete i)
               (\ xa ->
                 Sum_Type.Inl
                   (case xa of {
                     Sum_Type.Inl a -> id a;
                     Sum_Type.Inr (f, p) ->
                       (((Shows_Literal.showsl_literal "interpretation " .
                           Show_Literal_Polynomial.showsl_poly (x p)) .
                          Shows_Literal.showsl_literal " of ") .
                         Shows_Literal.showsl f) .
                         Shows_Literal.showsl_literal " invalid ";
                   }))))
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
         (check_s gt j) (check_ns j) (check_ns j) (poly_inter_to_af i)
         (poly_inter_to_af i) (Sum_Type.Inr ()) (Sum_Type.Inr ())
         (Sum_Type.Inr ()) (Sum_Type.Inr ()) (Sum_Type.Inr ()) (Sum_Type.Inr ())
         (poly_inter_to_mono_af discrete power_mono gt i)
         (\ _ ->
           Error_Monad.catch_error
             (Error_Monad.catch_error
               (Error_Monad.forallM
                 (\ xa ->
                   (if (case xa of {
                         (a, b) ->
                           (case a of {
                             (_, n) ->
                               (\ p ->
                                 all (Polynomials.check_poly_strict_mono_smart
                                       discrete power_mono gt p)
                                   (Arith.upt Arith.zero_nat n));
                           })
                             b;
                       })
                     then Sum_Type.Inr () else Sum_Type.Inl xa))
                 i)
               (\ xa -> Sum_Type.Inl (snd xa)))
             (\ xa ->
               Sum_Type.Inl
                 (case xa of {
                   (a, b) ->
                     (case a of {
                       (f, _) ->
                         (\ p ->
                           ((Shows_Literal.showsl_literal
                               "could not ensure monotonicty of " .
                              Show_Literal_Polynomial.showsl_poly (x p)) .
                             Shows_Literal.showsl_literal
                               " as interpretation of ") .
                             Shows_Literal.showsl f);
                     })
                       b;
                 })))
         (Just (map fst i)) (Just (map fst i)) (nl_complexity_check j) ();

check_non_inf_poly_inter_list ::
  forall a b.
    (Eq a, Eq b,
      SN_Orders.Poly_carrier b) => Bool ->
                                     [(a, Arith.Nat)] ->
                                       [((a, Arith.Nat),
  [(Polynomials.Monom Arith.Nat, b)])] ->
 Sum_Type.Sum (a, [(Polynomials.Monom Arith.Nat, b)]) ();
check_non_inf_poly_inter_list discrete f i =
  Error_Monad.catch_error
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ x ->
          (if (case x of {
                (_, a) -> Polynomials.check_poly_weak_mono_and_pos discrete a;
              })
            then Sum_Type.Inr () else Sum_Type.Inl x))
        (filter (\ (fn, _) -> Arith.membera f fn) i))
      (\ x -> Sum_Type.Inl (snd x)))
    (\ x -> Sum_Type.Inl (case x of {
                           (a, b) -> (case a of {
                                       (fa, _) -> (\ aa -> (fa, aa));
                                     })
                                       b;
                         }));

create_nlpoly_non_inf_order ::
  forall a b c.
    (Eq a, SN_Orders.Poly_carrier a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b, Shows_Literal.Showl b, Eq c,
      Quasi_Order.Linorder c,
      Shows_Literal.Showl c) => Sum_Type.Sum (String -> String) () ->
                                  a -> (a -> a -> Bool) ->
 Bool ->
   Bool ->
     (a -> [a]) ->
       [((b, Arith.Nat), [(Polynomials.Monom Arith.Nat, a)])] ->
         [(b, Arith.Nat)] -> Non_Inf_Order_Impl.Non_inf_order_ext b c ();
create_nlpoly_non_inf_order cI def gt power_mono discrete sqrt i f =
  let {
    j = poly_inter_list_to_inter def i;
    x = Polynomials.poly_subst
          (\ n ->
            Polynomials.poly_of
              (Polynomials.PVar
                ([Arith.char_0x78, Arith.char_0x5F] ++
                  Show_Instances.shows_prec_nat Arith.zero_nat n [])));
  } in Non_Inf_Order_Impl.Non_inf_order_ext
         (Error_Monad.bind cI
           (\ _ ->
             Error_Monad.catch_error
               (check_non_inf_poly_inter_list discrete f i)
               (\ xa ->
                 Sum_Type.Inl
                   (case xa of {
                     (fa, p) ->
                       (((Shows_Literal.showsl_literal "interpretation " .
                           Show_Literal_Polynomial.showsl_poly (x p)) .
                          Shows_Literal.showsl_literal " of ") .
                         Shows_Literal.showsl fa) .
                         Shows_Literal.showsl_literal " invalid ";
                   }))))
         (check_ns j) (check_cc sqrt gt j) (create_dep discrete def i)
         (Shows_Literal.showsl_literal "polynomial interpretation\n" .
           Shows_Literal.showsl_sep
             (\ (a, b) ->
               (case a of {
                 (fa, n) ->
                   (\ p ->
                     ((((Shows_Literal.showsl_literal "Pol(" .
                          Shows_Literal.showsl fa) .
                         Shows_Literal.showsl_literal "/") .
                        Shows_Literal.showsl_nat n) .
                       Shows_Literal.showsl_literal ") = ") .
                       Show_Literal_Polynomial.showsl_poly (x p));
               })
                 b)
             (Shows_Literal.showsl_literal "\n") i)
         ();

}
