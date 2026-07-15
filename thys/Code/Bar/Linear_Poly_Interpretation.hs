{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Linear_Poly_Interpretation(Explicit_minus_semiring_ext(..), evalp_rule,
                              coeffs_of_lpoly_better)
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
import qualified Term_Rewriting;
import qualified HOL;
import qualified Ordered_Semiring;
import qualified Congruence;
import qualified Linear_Polynomial;
import qualified Group;
import qualified Ring;
import qualified Arith;

data Explicit_minus_semiring_ext a b = Explicit_minus_semiring_ext (a -> a) b;

list_sum_poly ::
  forall a b c.
    (Eq a,
      Eq c) => Congruence.Partial_object_ext a
                 (Group.Monoid_ext a
                   (Ring.Ring_ext a
                     (Ordered_Semiring.Ordered_semiring_ext a
                       (Explicit_minus_semiring_ext a b)))) ->
                 [Linear_Polynomial.L_poly c a] -> Linear_Polynomial.L_poly c a;
list_sum_poly r [] = Linear_Polynomial.LPoly (Ring.zero r) [];
list_sum_poly r (p : ps) = Linear_Polynomial.sum_lpoly r p (list_sum_poly r ps);

ip :: forall a b c d.
        (Eq a,
          Eq d) => Congruence.Partial_object_ext a
                     (Group.Monoid_ext a
                       (Ring.Ring_ext a
                         (Ordered_Semiring.Ordered_semiring_ext a
                           (Explicit_minus_semiring_ext a b)))) ->
                     ((c, Arith.Nat) -> ([a], a)) ->
                       c -> [Linear_Polynomial.L_poly d a] ->
                              Linear_Polynomial.L_poly d a;
ip r pI f asa =
  (case pI (f, Arith.size_list asa) of {
    (cs, c) ->
      list_sum_poly r
        (Linear_Polynomial.LPoly c [] :
          map (\ ca -> Linear_Polynomial.mul_lpoly r (fst ca) (snd ca))
            (zip cs asa));
  });

vpoly ::
  forall a b c.
    Congruence.Partial_object_ext a
      (Group.Monoid_ext a
        (Ring.Ring_ext a
          (Ordered_Semiring.Ordered_semiring_ext a
            (Explicit_minus_semiring_ext a b)))) ->
      c -> Linear_Polynomial.L_poly c a;
vpoly r x = Linear_Polynomial.LPoly (Ring.zero r) [(x, Group.one r)];

minus ::
  forall a b.
    Congruence.Partial_object_ext a
      (Group.Monoid_ext a
        (Ring.Ring_ext a
          (Ordered_Semiring.Ordered_semiring_ext a
            (Explicit_minus_semiring_ext a b)))) ->
      a -> a;
minus (Congruence.Partial_object_ext carrier
        (Group.Monoid_ext mult one
          (Ring.Ring_ext zero add
            (Ordered_Semiring.Ordered_semiring_ext geq gt max
              (Explicit_minus_semiring_ext minus more)))))
  = minus;

expl_a_minus ::
  forall a b.
    Congruence.Partial_object_ext a
      (Group.Monoid_ext a
        (Ring.Ring_ext a
          (Ordered_Semiring.Ordered_semiring_ext a
            (Explicit_minus_semiring_ext a b)))) ->
      a -> a -> a;
expl_a_minus r x y = Ring.add r x (minus r y);

sub_var ::
  forall a b c.
    (Eq a,
      Eq c) => Congruence.Partial_object_ext a
                 (Group.Monoid_ext a
                   (Ring.Ring_ext a
                     (Ordered_Semiring.Ordered_semiring_ext a
                       (Explicit_minus_semiring_ext a b)))) ->
                 [(c, a)] -> c -> a -> [(c, a)];
sub_var r [] x b = [(x, minus r b)];
sub_var r ((y, a) : vas) x b =
  (if x == y then let {
                    s = expl_a_minus r a b;
                  } in (if s == Ring.zero r then vas else (x, s) : vas)
    else (y, a) : sub_var r vas x b);

sub_pvars ::
  forall a b c.
    (Eq a,
      Eq c) => Congruence.Partial_object_ext a
                 (Group.Monoid_ext a
                   (Ring.Ring_ext a
                     (Ordered_Semiring.Ordered_semiring_ext a
                       (Explicit_minus_semiring_ext a b)))) ->
                 [(c, a)] -> [(c, a)] -> [(c, a)];
sub_pvars r vas [] = vas;
sub_pvars r vas ((x, b) : vbs) =
  (if b == Ring.zero r then sub_pvars r vas vbs
    else sub_pvars r (sub_var r vas x b) vbs);

sub_lpoly ::
  forall a b c.
    (Eq a,
      Eq c) => Congruence.Partial_object_ext a
                 (Group.Monoid_ext a
                   (Ring.Ring_ext a
                     (Ordered_Semiring.Ordered_semiring_ext a
                       (Explicit_minus_semiring_ext a b)))) ->
                 Linear_Polynomial.L_poly c a ->
                   Linear_Polynomial.L_poly c a -> Linear_Polynomial.L_poly c a;
sub_lpoly r (Linear_Polynomial.LPoly a vas) (Linear_Polynomial.LPoly b vbs) =
  Linear_Polynomial.LPoly (expl_a_minus r a b) (sub_pvars r vas vbs);

evalp_rule ::
  forall a b c d.
    (Eq a,
      Eq d) => Congruence.Partial_object_ext a
                 (Group.Monoid_ext a
                   (Ring.Ring_ext a
                     (Ordered_Semiring.Ordered_semiring_ext a
                       (Explicit_minus_semiring_ext a b)))) ->
                 ((c, Arith.Nat) -> ([a], a)) ->
                   Term_Rewriting.Term c d ->
                     Term_Rewriting.Term c d -> Linear_Polynomial.L_poly d a;
evalp_rule ra pI l r =
  sub_lpoly ra (Term_Rewriting.eval_term (ip ra pI) l (vpoly ra))
    (Term_Rewriting.eval_term (ip ra pI) r (vpoly ra));

coeffs_of_pvars_better :: forall a b. [(a, b)] -> [b];
coeffs_of_pvars_better = map snd;

coeffs_of_lpoly_better :: forall a b. Linear_Polynomial.L_poly a b -> [b];
coeffs_of_lpoly_better (Linear_Polynomial.LPoly a_0 a_is) =
  a_0 : coeffs_of_pvars_better a_is;

}
