{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Polynomials(Monom, rep_monom, equal_monom, Tpoly(..), one_monom, zero_poly,
               var_monom, times_monom, monom_mult_poly, poly_add, poly_mult,
               one_poly, poly_of, eval_poly, poly_vars, poly_minus, poly_split,
               poly_subst, poly_degree, check_poly_eq, check_poly_ge,
               check_poly_gt, poly_vars_list, check_poly_weak_mono_all,
               check_poly_weak_mono_smart, check_poly_strict_mono_smart,
               check_poly_weak_mono_and_pos, check_poly_weak_anti_mono_smart)
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
import qualified Binary_Exponentiation;
import qualified Groups_List;
import qualified HOL;
import qualified SN_Orders;
import qualified Utility;
import qualified Arith;
import qualified Quasi_Order;

newtype Monom a = Abs_monom [(a, Arith.Nat)];

rep_monom :: forall a. (Quasi_Order.Linorder a) => Monom a -> [(a, Arith.Nat)];
rep_monom (Abs_monom x) = x;

equal_monom ::
  forall a. (Eq a, Quasi_Order.Linorder a) => Monom a -> Monom a -> Bool;
equal_monom xa xc = rep_monom xa == rep_monom xc;

instance (Eq a, Quasi_Order.Linorder a) => Eq (Monom a) where {
  a == b = equal_monom a b;
};

data Tpoly a b = PVar a | PNum b | PSum [Tpoly a b] | PMult [Tpoly a b];

one_monom :: forall a. (Quasi_Order.Linorder a) => Monom a;
one_monom = Abs_monom [];

zero_poly :: forall a b. [(Monom a, b)];
zero_poly = [];

var_monom :: forall a. (Quasi_Order.Linorder a) => a -> Monom a;
var_monom xa = Abs_monom [(xa, Arith.one_nat)];

monom_mult_list ::
  forall a.
    (Eq a,
      Quasi_Order.Linorder a) => [(a, Arith.Nat)] ->
                                   [(a, Arith.Nat)] -> [(a, Arith.Nat)];
monom_mult_list [] n = n;
monom_mult_list ((x, p) : m) n =
  (case n of {
    [] -> (x, p) : m;
    (y, q) : na ->
      (if x == y then (x, Arith.plus_nat p q) : monom_mult_list m na
        else (if Quasi_Order.less x y then (x, p) : monom_mult_list m n
               else (y, q) : monom_mult_list ((x, p) : m) na));
  });

times_monom ::
  forall a. (Eq a, Quasi_Order.Linorder a) => Monom a -> Monom a -> Monom a;
times_monom xb xc = Abs_monom (monom_mult_list (rep_monom xb) (rep_monom xc));

monom_mult_poly ::
  forall a b.
    (Eq a, Quasi_Order.Linorder a, Eq b,
      Arith.Semiring_0 b) => (Monom a, b) -> [(Monom a, b)] -> [(Monom a, b)];
monom_mult_poly uu [] = [];
monom_mult_poly (ma, c) ((m, d) : p) =
  (if Arith.times c d == Arith.zero then monom_mult_poly (ma, c) p
    else (times_monom ma m, Arith.times c d) : monom_mult_poly (ma, c) p);

poly_add ::
  forall a b.
    (Eq a, Quasi_Order.Linorder a, Eq b,
      Arith.Semiring_0 b) => [(Monom a, b)] -> [(Monom a, b)] -> [(Monom a, b)];
poly_add [] q = q;
poly_add ((m, c) : p) q =
  (case Arith.extract (\ mc -> fst mc == m) q of {
    Nothing -> (m, c) : poly_add p q;
    Just (q1, ((_, d), q2)) ->
      (if Arith.plus c d == Arith.zero then poly_add p (q1 ++ q2)
        else (m, Arith.plus c d) : poly_add p (q1 ++ q2));
  });

poly_mult ::
  forall a b.
    (Eq a, Quasi_Order.Linorder a, Eq b,
      Arith.Semiring_0 b) => [(Monom a, b)] -> [(Monom a, b)] -> [(Monom a, b)];
poly_mult [] q = [];
poly_mult (mc : p) q = poly_add (monom_mult_poly mc q) (poly_mult p q);

one_poly ::
  forall a b. (Quasi_Order.Linorder a, Arith.Semiring_1 b) => [(Monom a, b)];
one_poly = [(one_monom, Arith.one)];

poly_of ::
  forall a b.
    (Eq a, Quasi_Order.Linorder a, Eq b,
      Arith.Comm_semiring_1 b) => Tpoly a b -> [(Monom a, b)];
poly_of (PNum i) = (if i == Arith.zero then [] else [(one_monom, i)]);
poly_of (PVar x) = [(var_monom x, Arith.one)];
poly_of (PSum []) = zero_poly;
poly_of (PSum (p : ps)) = poly_add (poly_of p) (poly_of (PSum ps));
poly_of (PMult []) = one_poly;
poly_of (PMult (p : ps)) = poly_mult (poly_of p) (poly_of (PMult ps));

eval_monom_list ::
  forall a b.
    (Quasi_Order.Linorder a,
      Arith.Comm_semiring_1 b) => (a -> b) -> [(a, Arith.Nat)] -> b;
eval_monom_list alpha [] = Arith.one;
eval_monom_list alpha ((x, p) : m) =
  Arith.times (eval_monom_list alpha m)
    (Binary_Exponentiation.binary_power (alpha x) p);

eval_monom ::
  forall a b.
    (Quasi_Order.Linorder a,
      Arith.Comm_semiring_1 b) => (a -> b) -> Monom a -> b;
eval_monom x xc = eval_monom_list x (rep_monom xc);

eval_poly ::
  forall a b.
    (Quasi_Order.Linorder a,
      Arith.Comm_semiring_1 b) => (a -> b) -> [(Monom a, b)] -> b;
eval_poly alpha [] = Arith.zero;
eval_poly alpha (mc : p) =
  Arith.plus (Arith.times (eval_monom alpha (fst mc)) (snd mc))
    (eval_poly alpha p);

monom_vars_list :: forall a. (Quasi_Order.Linorder a) => Monom a -> [a];
monom_vars_list xa = map fst (rep_monom xa);

poly_vars ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Quasi_Order.Linorder a,
      Arith.Set_impl a) => [(Monom a, b)] -> Arith.Set a;
poly_vars p = Arith.set (concatMap (monom_vars_list . fst) p);

monom_list :: forall a. (Quasi_Order.Linorder a) => Monom a -> [(a, Arith.Nat)];
monom_list x = rep_monom x;

monom_vars ::
  forall a.
    (Arith.Ceq a, Arith.Ccompare a, Quasi_Order.Linorder a,
      Arith.Set_impl a) => Monom a -> Arith.Set a;
monom_vars m = Arith.set (monom_vars_list m);

poly_minus ::
  forall a b.
    (Eq a, Quasi_Order.Linorder a, Eq b,
      Arith.Ring_1 b) => [(Monom a, b)] -> [(Monom a, b)] -> [(Monom a, b)];
poly_minus f g =
  poly_add f (monom_mult_poly (one_monom, Arith.uminus Arith.one) g);

poly_power ::
  forall a b.
    (Eq a, Quasi_Order.Linorder a, Eq b,
      Arith.Comm_semiring_1 b) => [(Monom a, b)] -> Arith.Nat -> [(Monom a, b)];
poly_power uu n =
  (if Arith.equal_nat n Arith.zero_nat then one_poly
    else poly_mult uu (poly_power uu (Arith.minus_nat n Arith.one_nat)));

poly_split ::
  forall a b.
    (Eq a, Quasi_Order.Linorder a,
      Arith.Zero b) => Monom a -> [(Monom a, b)] -> (b, [(Monom a, b)]);
poly_split m p = (case Arith.extract (\ (n, _) -> m == n) p of {
                   Nothing -> (Arith.zero, p);
                   Just (p1, ((_, c), p2)) -> (c, p1 ++ p2);
                 });

monom_list_subst ::
  forall a b c.
    (Eq b, Quasi_Order.Linorder b, Eq c,
      Arith.Comm_semiring_1 c) => (a -> [(Monom b, c)]) ->
                                    [(a, Arith.Nat)] -> [(Monom b, c)];
monom_list_subst sigma [] = one_poly;
monom_list_subst sigma ((x, p) : m) =
  poly_mult (poly_power (sigma x) p) (monom_list_subst sigma m);

monom_subst ::
  forall a b c.
    (Quasi_Order.Linorder a, Eq b, Quasi_Order.Linorder b, Eq c,
      Arith.Comm_semiring_1 c) => (a -> [(Monom b, c)]) ->
                                    Monom a -> [(Monom b, c)];
monom_subst sigma m = monom_list_subst sigma (monom_list m);

poly_subst ::
  forall a b c.
    (Quasi_Order.Linorder a, Eq b, Quasi_Order.Linorder b, Eq c,
      Arith.Comm_semiring_1 c) => (a -> [(Monom b, c)]) ->
                                    [(Monom a, c)] -> [(Monom b, c)];
poly_subst sigma [] = zero_poly;
poly_subst sigma ((m, c) : p) =
  poly_add (poly_mult [(one_monom, c)] (monom_subst sigma m))
    (poly_subst sigma p);

monom_list_degree :: forall a. [(a, Arith.Nat)] -> Arith.Nat;
monom_list_degree xps = Groups_List.sum_list (map snd xps);

monom_degree :: forall a. (Quasi_Order.Linorder a) => Monom a -> Arith.Nat;
monom_degree xa = monom_list_degree (rep_monom xa);

poly_degree ::
  forall a b. (Quasi_Order.Linorder a) => [(Monom a, b)] -> Arith.Nat;
poly_degree p = Utility.max_list (map (\ (m, _) -> monom_degree m) p);

check_poly_eq ::
  forall a b.
    (Eq a, Quasi_Order.Linorder a, Eq b,
      Arith.Semiring_0 b) => [(Monom a, b)] -> [(Monom a, b)] -> Bool;
check_poly_eq [] q = null q;
check_poly_eq ((m, c) : p) q =
  (case Arith.extract (\ nd -> fst nd == m) q of {
    Nothing -> False;
    Just (q1, ((_, d), q2)) -> c == d && check_poly_eq p (q1 ++ q2);
  });

check_poly_ge ::
  forall a b.
    (Eq a, Quasi_Order.Linorder a,
      SN_Orders.Ordered_semiring_0 b) => [(Monom a, b)] ->
   [(Monom a, b)] -> Bool;
check_poly_ge [] q = all (\ (_, d) -> Quasi_Order.less_eq d Arith.zero) q;
check_poly_ge ((m, c) : p) q =
  (case Arith.extract (\ nd -> fst nd == m) q of {
    Nothing -> Quasi_Order.less_eq Arith.zero c && check_poly_ge p q;
    Just (q1, ((_, d), q2)) ->
      Quasi_Order.less_eq d c && check_poly_ge p (q1 ++ q2);
  });

check_poly_gt ::
  forall a b.
    (SN_Orders.Ordered_semiring_0 a, Eq b,
      Quasi_Order.Linorder b) => (a -> a -> Bool) ->
                                   [(Monom b, a)] -> [(Monom b, a)] -> Bool;
check_poly_gt gt p q =
  (case poly_split one_monom p of {
    (a1, p1) -> (case poly_split one_monom q of {
                  (b1, q1) -> gt a1 b1 && check_poly_ge p1 q1;
                });
  });

poly_vars_list ::
  forall a b. (Eq a, Quasi_Order.Linorder a) => [(Monom a, b)] -> [a];
poly_vars_list p = Arith.remdups (concatMap (monom_vars_list . fst) p);

univariate_power_list ::
  forall a. (Eq a) => a -> [(a, Arith.Nat)] -> Maybe Arith.Nat;
univariate_power_list x [(y, n)] = (if x == y then Just n else Nothing);
univariate_power_list uu [] = Nothing;
univariate_power_list uu (v : vb : vc) = Nothing;

univariate_power ::
  forall a. (Eq a, Quasi_Order.Linorder a) => a -> Monom a -> Maybe Arith.Nat;
univariate_power x xc = univariate_power_list x (rep_monom xc);

check_poly_weak_mono ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Quasi_Order.Linorder a, Arith.Set_impl a,
      SN_Orders.Ordered_semiring_0 b) => [(Monom a, b)] -> a -> Bool;
check_poly_weak_mono p v =
  all (\ (m, c) ->
        Quasi_Order.less_eq Arith.zero c || not (Arith.member v (monom_vars m)))
    p;

check_monom_strict_mono ::
  forall a. (Eq a, Quasi_Order.Linorder a) => Bool -> Monom a -> a -> Bool;
check_monom_strict_mono pm m v =
  (case univariate_power v m of {
    Nothing -> False;
    Just p -> pm || Arith.equal_nat p Arith.one_nat;
  });

check_poly_strict_mono ::
  forall a b.
    (Eq a, Quasi_Order.Linorder a,
      SN_Orders.Poly_carrier b) => Bool -> [(Monom a, b)] -> a -> Bool;
check_poly_strict_mono pm p v =
  any (\ (m, c) ->
        Quasi_Order.less_eq Arith.one c && check_monom_strict_mono pm m v)
    p;

check_poly_weak_mono_all ::
  forall a b. (SN_Orders.Ordered_semiring_0 b) => [(Monom a, b)] -> Bool;
check_poly_weak_mono_all p =
  all (\ (_, a) -> Quasi_Order.less_eq Arith.zero a) p;

check_poly_weak_anti_mono ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Quasi_Order.Linorder a, Arith.Set_impl a,
      SN_Orders.Ordered_semiring_0 b) => [(Monom a, b)] -> a -> Bool;
check_poly_weak_anti_mono p v =
  all (\ (m, c) ->
        Quasi_Order.less_eq c Arith.zero || not (Arith.member v (monom_vars m)))
    p;

check_poly_weak_mono_discrete ::
  forall a b.
    (Eq a, Quasi_Order.Linorder a, Eq b,
      SN_Orders.Poly_carrier b) => [(Monom a, b)] -> a -> Bool;
check_poly_weak_mono_discrete p v =
  check_poly_ge
    (poly_subst
      (\ w ->
        poly_of (if w == v then PSum [PNum Arith.one, PVar v] else PVar w))
      p)
    p;

check_poly_weak_mono_smart ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Eq a, Quasi_Order.Linorder a,
      Arith.Set_impl a, Eq b,
      SN_Orders.Poly_carrier b) => Bool -> [(Monom a, b)] -> a -> Bool;
check_poly_weak_mono_smart discrete =
  (if discrete then check_poly_weak_mono_discrete else check_poly_weak_mono);

check_poly_strict_mono_discrete ::
  forall a b.
    (Eq a, SN_Orders.Poly_carrier a, Eq b,
      Quasi_Order.Linorder b) => (a -> a -> Bool) ->
                                   [(Monom b, a)] -> b -> Bool;
check_poly_strict_mono_discrete gt p v =
  check_poly_gt gt
    (poly_subst
      (\ w ->
        poly_of (if w == v then PSum [PNum Arith.one, PVar v] else PVar w))
      p)
    p;

check_poly_strict_mono_smart ::
  forall a b.
    (Eq a, SN_Orders.Poly_carrier a, Eq b,
      Quasi_Order.Linorder b) => Bool ->
                                   Bool ->
                                     (a -> a -> Bool) ->
                                       [(Monom b, a)] -> b -> Bool;
check_poly_strict_mono_smart discrete pm gt p v =
  (if discrete then check_poly_strict_mono_discrete gt p v
    else check_poly_strict_mono pm p v);

check_poly_weak_mono_and_pos ::
  forall a b.
    (Eq a, Quasi_Order.Linorder a, Eq b,
      SN_Orders.Poly_carrier b) => Bool -> [(Monom a, b)] -> Bool;
check_poly_weak_mono_and_pos discrete p =
  (if discrete
    then all (check_poly_weak_mono_discrete p) (poly_vars_list p) &&
           Quasi_Order.less_eq Arith.zero (eval_poly (\ _ -> Arith.zero) p)
    else check_poly_weak_mono_all p);

check_poly_weak_anti_mono_discrete ::
  forall a b.
    (Eq a, Quasi_Order.Linorder a, Eq b,
      SN_Orders.Poly_carrier b) => [(Monom a, b)] -> a -> Bool;
check_poly_weak_anti_mono_discrete p v =
  check_poly_ge p
    (poly_subst
      (\ w ->
        poly_of (if w == v then PSum [PNum Arith.one, PVar v] else PVar w))
      p);

check_poly_weak_anti_mono_smart ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Eq a, Quasi_Order.Linorder a,
      Arith.Set_impl a, Eq b,
      SN_Orders.Poly_carrier b) => Bool -> [(Monom a, b)] -> a -> Bool;
check_poly_weak_anti_mono_smart discrete =
  (if discrete then check_poly_weak_anti_mono_discrete
    else check_poly_weak_anti_mono);

}
