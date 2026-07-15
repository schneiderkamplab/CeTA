{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Polynomial(Poly, coeffs, equal_poly, zero_poly, smult, pCons, uminus_poly,
              poly, order, degree, pderiv, content, map_poly, coeff, pseudo_mod,
              primitive_part, div_field_poly_impl, modulo_poly, normalize_poly)
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
import qualified More_List;
import qualified Groups_List;
import qualified Arith;

newtype Poly a = Poly [a];

coeffs :: forall a. (Arith.Zero a) => Poly a -> [a];
coeffs (Poly x) = x;

equal_poly :: forall a. (Arith.Zero a, Eq a) => Poly a -> Poly a -> Bool;
equal_poly p q = coeffs p == coeffs q;

instance (Arith.Zero a, Eq a) => Eq (Poly a) where {
  a == b = equal_poly a b;
};

zero_poly :: forall a. (Arith.Zero a) => Poly a;
zero_poly = Poly [];

cCons :: forall a. (Arith.Zero a, Eq a) => a -> [a] -> [a];
cCons x xs = (if null xs && x == Arith.zero then [] else x : xs);

plus_coeffs :: forall a. (Arith.Comm_monoid_add a, Eq a) => [a] -> [a] -> [a];
plus_coeffs xs [] = xs;
plus_coeffs [] (v : va) = v : va;
plus_coeffs (x : xs) (y : ys) = cCons (Arith.plus x y) (plus_coeffs xs ys);

plus_poly ::
  forall a. (Arith.Comm_monoid_add a, Eq a) => Poly a -> Poly a -> Poly a;
plus_poly p q = Poly (plus_coeffs (coeffs p) (coeffs q));

fold_coeffs :: forall a b. (Arith.Zero a) => (a -> b -> b) -> Poly a -> b -> b;
fold_coeffs f p = Arith.foldr f (coeffs p);

smult ::
  forall a.
    (Eq a, Arith.Comm_semiring_0 a,
      Arith.Semiring_no_zero_divisors a) => a -> Poly a -> Poly a;
smult a p =
  Poly (if a == Arith.zero then [] else map (Arith.times a) (coeffs p));

pCons :: forall a. (Arith.Zero a, Eq a) => a -> Poly a -> Poly a;
pCons a p = Poly (cCons a (coeffs p));

times_poly ::
  forall a.
    (Eq a, Arith.Comm_semiring_0 a,
      Arith.Semiring_no_zero_divisors a) => Poly a -> Poly a -> Poly a;
times_poly p q =
  fold_coeffs (\ a pa -> plus_poly (smult a q) (pCons Arith.zero pa)) p
    zero_poly;

instance (Eq a, Arith.Comm_semiring_0 a,
           Arith.Semiring_no_zero_divisors a) => Arith.Times (Poly a) where {
  times = times_poly;
};

instance (Eq a, Arith.Comm_semiring_1 a,
           Arith.Semiring_no_zero_divisors a) => Arith.Dvd (Poly a) where {
};

one_poly :: forall a. (Arith.Comm_semiring_1 a) => Poly a;
one_poly = Poly [Arith.one];

instance (Arith.Comm_semiring_1 a) => Arith.One (Poly a) where {
  one = one_poly;
};

uminus_poly :: forall a. (Arith.Ab_group_add a) => Poly a -> Poly a;
uminus_poly p = Poly (map Arith.uminus (coeffs p));

minus_poly ::
  forall a. (Arith.Ab_group_add a, Eq a) => Poly a -> Poly a -> Poly a;
minus_poly p q = plus_poly p (uminus_poly q);

instance (Arith.Comm_monoid_add a, Eq a) => Arith.Plus (Poly a) where {
  plus = plus_poly;
};

instance (Arith.Comm_monoid_add a, Eq a) => Arith.Semigroup_add (Poly a) where {
};

instance (Arith.Cancel_comm_monoid_add a,
           Eq a) => Arith.Cancel_semigroup_add (Poly a) where {
};

instance (Arith.Comm_monoid_add a,
           Eq a) => Arith.Ab_semigroup_add (Poly a) where {
};

instance (Arith.Ab_group_add a, Eq a) => Arith.Minus (Poly a) where {
  minusa = minus_poly;
};

instance (Arith.Ab_group_add a,
           Eq a) => Arith.Cancel_ab_semigroup_add (Poly a) where {
};

instance (Arith.Zero a) => Arith.Zero (Poly a) where {
  zero = zero_poly;
};

instance (Arith.Comm_monoid_add a, Eq a) => Arith.Monoid_add (Poly a) where {
};

instance (Arith.Comm_monoid_add a,
           Eq a) => Arith.Comm_monoid_add (Poly a) where {
};

instance (Arith.Ab_group_add a,
           Eq a) => Arith.Cancel_comm_monoid_add (Poly a) where {
};

instance (Eq a, Arith.Comm_semiring_0 a,
           Arith.Semiring_no_zero_divisors a) => Arith.Mult_zero (Poly
                           a) where {
};

instance (Eq a, Arith.Comm_semiring_0 a,
           Arith.Semiring_no_zero_divisors a) => Arith.Semigroup_mult (Poly
                                a) where {
};

instance (Eq a, Arith.Comm_semiring_0 a,
           Arith.Semiring_no_zero_divisors a) => Arith.Semiring (Poly a) where {
};

instance (Eq a, Arith.Comm_semiring_0 a,
           Arith.Semiring_no_zero_divisors a) => Arith.Semiring_0 (Poly
                            a) where {
};

instance (Arith.Ab_group_add a, Eq a, Arith.Comm_semiring_0_cancel a,
           Arith.Semiring_no_zero_divisors a) => Arith.Semiring_0_cancel (Poly
                                   a) where {
};

instance (Eq a, Arith.Comm_semiring_0 a,
           Arith.Semiring_no_zero_divisors a) => Arith.Ab_semigroup_mult (Poly
                                   a) where {
};

instance (Eq a, Arith.Comm_semiring_0 a,
           Arith.Semiring_no_zero_divisors a) => Arith.Comm_semiring (Poly
                               a) where {
};

instance (Eq a, Arith.Comm_semiring_0 a,
           Arith.Semiring_no_zero_divisors a) => Arith.Comm_semiring_0 (Poly
                                 a) where {
};

instance (Arith.Ab_group_add a, Eq a, Arith.Comm_semiring_0_cancel a,
           Arith.Semiring_no_zero_divisors a) => Arith.Comm_semiring_0_cancel (Poly
a) where {
};

instance (Eq a, Arith.Comm_semiring_1 a,
           Arith.Semiring_no_zero_divisors a) => Arith.Power (Poly a) where {
};

instance (Eq a, Arith.Comm_semiring_1 a,
           Arith.Semiring_no_zero_divisors a) => Arith.Monoid_mult (Poly
                             a) where {
};

instance (Eq a, Arith.Comm_semiring_1 a) => Arith.Numeral (Poly a) where {
};

instance (Eq a, Arith.Comm_semiring_1 a,
           Arith.Semiring_no_zero_divisors a) => Arith.Semiring_numeral (Poly
                                  a) where {
};

instance (Arith.Comm_semiring_1 a) => Arith.Zero_neq_one (Poly a) where {
};

instance (Eq a, Arith.Comm_semiring_1 a,
           Arith.Semiring_no_zero_divisors a) => Arith.Semiring_1 (Poly
                            a) where {
};

instance (Eq a, Arith.Comm_ring_1 a,
           Arith.Semiring_no_zero_divisors a) => Arith.Semiring_1_cancel (Poly
                                   a) where {
};

instance (Eq a, Arith.Comm_semiring_1 a,
           Arith.Semiring_no_zero_divisors a) => Arith.Comm_monoid_mult (Poly
                                  a) where {
};

instance (Eq a, Arith.Comm_semiring_1 a,
           Arith.Semiring_no_zero_divisors a) => Arith.Comm_semiring_1 (Poly
                                 a) where {
};

instance (Eq a, Arith.Comm_ring_1 a,
           Arith.Semiring_no_zero_divisors a) => Arith.Comm_semiring_1_cancel (Poly
a) where {
};

instance (Eq a,
           Arith.Idom a) => Arith.Comm_semiring_1_cancel_crossproduct (Poly
                                a) where {
};

instance (Eq a, Arith.Comm_semiring_0 a,
           Arith.Semiring_no_zero_divisors a) => Arith.Semiring_no_zero_divisors (Poly
   a) where {
};

instance (Eq a, Arith.Comm_semiring_1 a,
           Arith.Semiring_1_no_zero_divisors a) => Arith.Semiring_1_no_zero_divisors (Poly
       a) where {
};

instance (Eq a,
           Arith.Idom a) => Arith.Semiring_no_zero_divisors_cancel (Poly
                             a) where {
};

instance (Arith.Ab_group_add a) => Arith.Uminus (Poly a) where {
  uminus = uminus_poly;
};

instance (Arith.Ab_group_add a, Eq a) => Arith.Group_add (Poly a) where {
};

instance (Arith.Ab_group_add a, Eq a) => Arith.Ab_group_add (Poly a) where {
};

instance (Eq a, Arith.Comm_ring a,
           Arith.Semiring_no_zero_divisors a) => Arith.Ring (Poly a) where {
};

instance (Eq a, Arith.Idom a) => Arith.Ring_no_zero_divisors (Poly a) where {
};

instance (Eq a, Arith.Comm_ring_1 a) => Arith.Neg_numeral (Poly a) where {
};

instance (Eq a, Arith.Comm_ring_1 a,
           Arith.Semiring_no_zero_divisors a) => Arith.Ring_1 (Poly a) where {
};

instance (Eq a, Arith.Idom a) => Arith.Ring_1_no_zero_divisors (Poly a) where {
};

instance (Eq a, Arith.Comm_ring a,
           Arith.Semiring_no_zero_divisors a) => Arith.Comm_ring (Poly
                           a) where {
};

instance (Eq a, Arith.Comm_ring_1 a,
           Arith.Semiring_no_zero_divisors a) => Arith.Comm_ring_1 (Poly
                             a) where {
};

instance (Eq a, Arith.Idom a) => Arith.Semidom (Poly a) where {
};

instance (Eq a, Arith.Idom a) => Arith.Idom (Poly a) where {
};

minus_poly_rev_list :: forall a. (Arith.Group_add a) => [a] -> [a] -> [a];
minus_poly_rev_list (x : xs) (y : ys) =
  Arith.minusa x y : minus_poly_rev_list xs ys;
minus_poly_rev_list xs [] = xs;
minus_poly_rev_list [] (y : ys) = [];

divide_poly_main_list ::
  forall a.
    (Eq a, Arith.Idom_divide a) => a -> [a] -> [a] -> [a] -> Arith.Nat -> [a];
divide_poly_main_list lc q r d n =
  (if Arith.equal_nat n Arith.zero_nat then q
    else let {
           cr = Arith.hda r;
         } in (if cr == Arith.zero
                then divide_poly_main_list lc (cCons cr q) (Arith.tla r) d
                       (Arith.minus_nat n Arith.one_nat)
                else let {
                       a = Arith.divide cr lc;
                       qq = cCons a q;
                       rr = minus_poly_rev_list r (map (Arith.times a) d);
                     } in (if Arith.hda rr == Arith.zero
                            then divide_poly_main_list lc qq (Arith.tla rr) d
                                   (Arith.minus_nat n Arith.one_nat)
                            else [])));

poly_of_list :: forall a. (Arith.Comm_monoid_add a, Eq a) => [a] -> Poly a;
poly_of_list asa = Poly (More_List.strip_while (\ a -> Arith.zero == a) asa);

divide_poly_list ::
  forall a. (Eq a, Arith.Idom_divide a) => Poly a -> Poly a -> Poly a;
divide_poly_list f g =
  let {
    cg = coeffs g;
  } in (if null cg then g
         else let {
                cf = coeffs f;
                cgr = reverse cg;
              } in poly_of_list
                     (divide_poly_main_list (Arith.hda cgr) [] (reverse cf) cgr
                       (Arith.minus_nat
                         (Arith.plus_nat Arith.one_nat (Arith.size_list cf))
                         (Arith.size_list cg))));

divide_poly ::
  forall a. (Eq a, Arith.Idom_divide a) => Poly a -> Poly a -> Poly a;
divide_poly f g = divide_poly_list f g;

instance (Eq a, Arith.Idom_divide a) => Arith.Divide (Poly a) where {
  divide = divide_poly;
};

instance (Eq a, Arith.Idom_divide a) => Arith.Divide_trivial (Poly a) where {
};

instance (Eq a, Arith.Idom_divide a) => Arith.Semidom_divide (Poly a) where {
};

instance (Eq a, Arith.Idom_divide a) => Arith.Idom_divide (Poly a) where {
};

poly :: forall a. (Arith.Comm_semiring_0 a) => Poly a -> a -> a;
poly p a = Groups_List.horner_sum id a (coeffs p);

order :: forall a. (Eq a, Arith.Idom_divide a) => a -> Poly a -> Arith.Nat;
order a p =
  (if (case coeffs p of {
        [] -> True;
        _ : _ -> False;
      })
    then (error :: forall a. String -> (() -> a) -> a)
           "order of polynomial 0 undefined" (\ _ -> order a p)
    else (if not (poly p a == Arith.zero) then Arith.zero_nat
           else Arith.suc
                  (order a
                    (divide_poly p
                      (pCons (Arith.uminus a) (pCons Arith.one zero_poly))))));

degree :: forall a. (Arith.Zero a) => Poly a -> Arith.Nat;
degree p = Arith.minus_nat (Arith.size_list (coeffs p)) Arith.one_nat;

pderiv_coeffs_code ::
  forall a.
    (Eq a, Arith.Comm_semiring_1 a,
      Arith.Semiring_no_zero_divisors a) => a -> [a] -> [a];
pderiv_coeffs_code f (x : xs) =
  cCons (Arith.times f x) (pderiv_coeffs_code (Arith.plus f Arith.one) xs);
pderiv_coeffs_code f [] = [];

pderiv_coeffs ::
  forall a.
    (Eq a, Arith.Comm_semiring_1 a,
      Arith.Semiring_no_zero_divisors a) => [a] -> [a];
pderiv_coeffs xs = pderiv_coeffs_code Arith.one (Arith.tla xs);

pderiv ::
  forall a.
    (Eq a, Arith.Comm_semiring_1 a,
      Arith.Semiring_no_zero_divisors a) => Poly a -> Poly a;
pderiv p = Poly (pderiv_coeffs (coeffs p));

content :: forall a. (Arith.Semiring_gcd a) => Poly a -> a;
content p = fold_coeffs Arith.gcda p Arith.zero;

map_poly ::
  forall b a.
    (Arith.Zero b, Arith.Zero a, Eq a) => (b -> a) -> Poly b -> Poly a;
map_poly f p =
  Poly (More_List.strip_while (\ a -> Arith.zero == a) (map f (coeffs p)));

coeff :: forall a. (Arith.Zero a) => Poly a -> Arith.Nat -> a;
coeff p = More_List.nth_default Arith.zero (coeffs p);

pseudo_mod_main_list ::
  forall a. (Eq a, Arith.Comm_ring_1 a) => a -> [a] -> [a] -> Arith.Nat -> [a];
pseudo_mod_main_list lc r d n =
  (if Arith.equal_nat n Arith.zero_nat then r
    else let {
           rr = map (Arith.times lc) r;
           a = Arith.hda r;
           rrr = Arith.tla
                   (if a == Arith.zero then rr
                     else minus_poly_rev_list rr (map (Arith.times a) d));
         } in pseudo_mod_main_list lc rrr d (Arith.minus_nat n Arith.one_nat));

pseudo_mod_list :: forall a. (Eq a, Arith.Comm_ring_1 a) => [a] -> [a] -> [a];
pseudo_mod_list p q =
  (if null q then p
    else let {
           rq = reverse q;
           a = pseudo_mod_main_list (Arith.hda rq) (reverse p) rq
                 (Arith.minus_nat
                   (Arith.plus_nat Arith.one_nat (Arith.size_list p))
                   (Arith.size_list q));
         } in reverse a);

pseudo_mod ::
  forall a.
    (Eq a, Arith.Comm_ring_1 a,
      Arith.Semiring_1_no_zero_divisors a) => Poly a -> Poly a -> Poly a;
pseudo_mod f g = poly_of_list (pseudo_mod_list (coeffs f) (coeffs g));

primitive_part :: forall a. (Arith.Semiring_gcd a, Eq a) => Poly a -> Poly a;
primitive_part p = map_poly (\ x -> Arith.divide x (content p)) p;

divmod_poly_one_main_list ::
  forall a.
    (Eq a, Arith.Comm_ring_1 a) => [a] -> [a] -> [a] -> Arith.Nat -> ([a], [a]);
divmod_poly_one_main_list q r d n =
  (if Arith.equal_nat n Arith.zero_nat then (q, r)
    else let {
           a = Arith.hda r;
           qqq = cCons a q;
           rr = Arith.tla
                  (if a == Arith.zero then r
                    else minus_poly_rev_list r (map (Arith.times a) d));
         } in divmod_poly_one_main_list qqq rr d
                (Arith.minus_nat n Arith.one_nat));

div_field_poly_impl ::
  forall a. (Arith.Field a, Eq a) => Poly a -> Poly a -> Poly a;
div_field_poly_impl f g =
  let {
    cg = coeffs g;
  } in (if null cg then zero_poly
         else let {
                cf = coeffs f;
                ilc = Arith.inverse (Arith.last cg);
                ch = map (Arith.times ilc) cg;
                q = fst (divmod_poly_one_main_list [] (reverse cf) (reverse ch)
                          (Arith.minus_nat
                            (Arith.plus_nat Arith.one_nat (Arith.size_list cf))
                            (Arith.size_list cg)));
              } in poly_of_list (map (Arith.times ilc) q));

mod_poly_one_main_list ::
  forall a. (Eq a, Arith.Comm_ring_1 a) => [a] -> [a] -> Arith.Nat -> [a];
mod_poly_one_main_list r d n =
  (if Arith.equal_nat n Arith.zero_nat then r
    else let {
           a = Arith.hda r;
           rr = Arith.tla
                  (if a == Arith.zero then r
                    else minus_poly_rev_list r (map (Arith.times a) d));
         } in mod_poly_one_main_list rr d (Arith.minus_nat n Arith.one_nat));

modulo_poly :: forall a. (Arith.Field a, Eq a) => Poly a -> Poly a -> Poly a;
modulo_poly f g =
  let {
    cg = coeffs g;
  } in (if null cg then f
         else let {
                cf = coeffs f;
                ilc = Arith.inverse (Arith.last cg);
                ch = map (Arith.times ilc) cg;
                r = mod_poly_one_main_list (reverse cf) (reverse ch)
                      (Arith.minus_nat
                        (Arith.plus_nat Arith.one_nat (Arith.size_list cf))
                        (Arith.size_list cg));
              } in poly_of_list (reverse r));

normalize_poly ::
  forall a.
    (Eq a, Arith.Idom_divide a,
      Arith.Semidom_divide_unit_factor a) => Poly a -> Poly a;
normalize_poly p =
  divide_poly p (pCons (Arith.unit_factor (coeff p (degree p))) zero_poly);

}
