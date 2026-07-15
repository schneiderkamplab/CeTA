{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Linear_Polynomial(L_poly(..), wf_lpoly, list_prod, mul_lpoly, sum_lpoly,
                     var_lpoly, eval_lpoly, showsl_lpoly, check_lpoly_s,
                     check_lpoly_ns, sum_list_lpoly, showsl_l_poly)
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
import qualified Linear_Poly_Complexity;
import qualified Ordered_Semiring;
import qualified Product_Type;
import qualified Option;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Shows_Literal;
import qualified List;
import qualified Set;
import qualified Collection_Order;
import qualified Collection_Enum;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified HOL;
import qualified Congruence;
import qualified Group;
import qualified Ring;

data L_poly a b = LPoly b [(a, b)];

add_var ::
  forall a b c.
    (Eq a,
      Eq c) => Congruence.Partial_object_ext a
                 (Group.Monoid_ext a (Ring.Ring_ext a b)) ->
                 c -> a -> [(c, a)] -> [(c, a)];
add_var r x a [] = [(x, a)];
add_var r x a ((y, b) : vas) =
  (if x == y then let {
                    s = Ring.add r a b;
                  } in (if s == Ring.zero r then vas else (x, s) : vas)
    else (y, b) : add_var r x a vas);

wf_pvars ::
  forall a b c.
    (Collection_Enum.Cenum a, Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Set_Impl.Set_impl a,
      Eq c) => Congruence.Partial_object_ext a b -> [(c, a)] -> Bool;
wf_pvars r vas =
  Set.less_eq_set (List.set (map snd vas)) (Congruence.carrier r) &&
    List.distinct (map fst vas);

wf_lpoly ::
  forall a b c.
    (Collection_Enum.Cenum a, Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Set_Impl.Set_impl a,
      Eq c) => Congruence.Partial_object_ext a b -> L_poly c a -> Bool;
wf_lpoly r (LPoly a vas) =
  Set.member a (Congruence.carrier r) && wf_pvars r vas;

list_prod ::
  forall a b.
    Congruence.Partial_object_ext a (Group.Monoid_ext a b) -> [a] -> a;
list_prod r [] = Group.one r;
list_prod r (x : xs) = Group.mult r x (list_prod r xs);

mul_pvars ::
  forall a b c.
    (Eq a) => Congruence.Partial_object_ext a
                (Group.Monoid_ext a (Ring.Ring_ext a b)) ->
                a -> [(c, a)] -> [(c, a)];
mul_pvars r a [] = [];
mul_pvars r a ((x, b) : vas) =
  let {
    p = Group.mult r a b;
    res = mul_pvars r a vas;
  } in (if p == Ring.zero r then res else (x, p) : res);

mul_lpoly ::
  forall a b c.
    (Eq a) => Congruence.Partial_object_ext a
                (Group.Monoid_ext a (Ring.Ring_ext a b)) ->
                a -> L_poly c a -> L_poly c a;
mul_lpoly r a (LPoly b vas) = LPoly (Group.mult r a b) (mul_pvars r a vas);

sum_pvars ::
  forall a b c.
    (Eq a,
      Eq c) => Congruence.Partial_object_ext a
                 (Group.Monoid_ext a (Ring.Ring_ext a b)) ->
                 [(c, a)] -> [(c, a)] -> [(c, a)];
sum_pvars r [] vbs = vbs;
sum_pvars r ((x, a) : vas) vbs =
  (if a == Ring.zero r then sum_pvars r vas vbs
    else sum_pvars r vas (add_var r x a vbs));

sum_lpoly ::
  forall a b c.
    (Eq a,
      Eq c) => Congruence.Partial_object_ext a
                 (Group.Monoid_ext a (Ring.Ring_ext a b)) ->
                 L_poly c a -> L_poly c a -> L_poly c a;
sum_lpoly r (LPoly a vas) (LPoly b vbs) =
  LPoly (Ring.add r a b) (sum_pvars r vas vbs);

var_lpoly ::
  forall a b c.
    Congruence.Partial_object_ext a (Group.Monoid_ext a (Ring.Ring_ext a b)) ->
      c -> L_poly c a;
var_lpoly r x = LPoly (Ring.zero r) [(x, Group.one r)];

eval_pvars ::
  forall a b c.
    Congruence.Partial_object_ext a (Group.Monoid_ext a (Ring.Ring_ext a b)) ->
      (c -> a) -> [(c, a)] -> a;
eval_pvars r uu [] = Ring.zero r;
eval_pvars r alpha ((x, a) : vas) =
  Ring.add r (Group.mult r a (alpha x)) (eval_pvars r alpha vas);

eval_lpoly ::
  forall a b c.
    Congruence.Partial_object_ext a (Group.Monoid_ext a (Ring.Ring_ext a b)) ->
      (c -> a) -> L_poly c a -> a;
eval_lpoly r alpha (LPoly a vas) = Ring.add r a (eval_pvars r alpha vas);

lookup_rest :: forall a b. (Eq a) => a -> [(a, b)] -> Maybe (b, [(a, b)]);
lookup_rest x [] = Nothing;
lookup_rest x ((y, c) : ycs) =
  (if x == y then Just (c, ycs)
    else (case lookup_rest x ycs of {
           Nothing -> Nothing;
           Just (d, yccs) -> Just (d, (y, c) : yccs);
         }));

check_pvars ::
  forall a b c.
    (Shows_Literal.Showl a,
      Eq c) => Congruence.Partial_object_ext a
                 (Group.Monoid_ext a (Ring.Ring_ext a b)) ->
                 (a -> a -> Bool) -> [(c, a)] -> [(c, a)] -> Sum_Type.Sum c ();
check_pvars r rel vas [] =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ va -> Check_Monad.check (rel (snd va) (Ring.zero r)) (fst va)) vas)
    (\ x -> Sum_Type.Inl (snd x));
check_pvars r rel vas ((x, b) : vbs) =
  (case (case lookup_rest x vas of {
          Nothing -> (Ring.zero r, vas);
          Just (a, ba) -> (a, ba);
        })
    of {
    (a, vasa) ->
      Error_Monad.bind (Check_Monad.check (rel a b) x)
        (\ _ -> check_pvars r rel vasa vbs);
  });

showl_pvars ::
  forall a b c.
    (Eq a, Shows_Literal.Showl a,
      Shows_Literal.Showl c) => Congruence.Partial_object_ext a
                                  (Group.Monoid_ext a (Ring.Ring_ext a b)) ->
                                  [(c, a)] -> [String];
showl_pvars r [] = [];
showl_pvars r ((x, c) : vas) =
  (if c == Group.one r then id else Shows_Literal.showsl c)
    (Shows_Literal.showsl x "") :
    showl_pvars r vas;

showsl_lpoly ::
  forall a b c.
    (Eq a, Shows_Literal.Showl a,
      Shows_Literal.Showl c) => Congruence.Partial_object_ext a
                                  (Group.Monoid_ext a (Ring.Ring_ext a b)) ->
                                  L_poly c a -> String -> String;
showsl_lpoly r (LPoly c cs) =
  (case showl_pvars r cs of {
    [] -> Shows_Literal.showsl c;
    a : list ->
      (if c == Ring.zero r then id
        else Shows_Literal.showsl c . Shows_Literal.showsl_literal " + ") .
        Shows_Literal.showsl_list_gen Shows_Literal.showsl_literal "" "" " + "
          "" (a : list);
  });

check_lpoly_s ::
  forall a b c.
    (Eq a, Shows_Literal.Showl a, Eq c,
      Shows_Literal.Showl c) => Congruence.Partial_object_ext a
                                  (Group.Monoid_ext a
                                    (Ring.Ring_ext a
                                      (Ordered_Semiring.Ordered_semiring_ext a
(Linear_Poly_Complexity.Lpoly_order_semiring_ext a b)))) ->
                                  L_poly c a ->
                                    L_poly c a ->
                                      Sum_Type.Sum (String -> String) ();
check_lpoly_s r (LPoly a vas) (LPoly b vbs) =
  Error_Monad.catch_error
    (Error_Monad.bind
      (Check_Monad.check (Ordered_Semiring.gt r a b)
        (Shows_Literal.showsl_literal "problem when comparing constant part"))
      (\ _ ->
        Error_Monad.catch_error
          (check_pvars r
            (if Linear_Poly_Complexity.plus_single_mono r
              then Ordered_Semiring.geq r else Ordered_Semiring.gt r)
            vas vbs)
          (\ x ->
            Sum_Type.Inl
              (Shows_Literal.showsl_literal
                 "problem when comparing coefficients of variable " .
                Shows_Literal.showsl x))))
    (\ x ->
      Sum_Type.Inl
        (((((Shows_Literal.showsl_literal "problem when comparing " .
              showsl_lpoly r (LPoly a vas)) .
             Shows_Literal.showsl_literal " > ") .
            showsl_lpoly r (LPoly b vbs)) .
           Shows_Literal.showsl_literal "\n") .
          x));

check_lpoly_ns ::
  forall a b c.
    (Eq a, Shows_Literal.Showl a, Eq c,
      Shows_Literal.Showl c) => Congruence.Partial_object_ext a
                                  (Group.Monoid_ext a
                                    (Ring.Ring_ext a
                                      (Ordered_Semiring.Ordered_semiring_ext a
b))) ->
                                  L_poly c a ->
                                    L_poly c a ->
                                      Sum_Type.Sum (String -> String) ();
check_lpoly_ns r (LPoly a vas) (LPoly b vbs) =
  Error_Monad.catch_error
    (Error_Monad.bind
      (Check_Monad.check (Ordered_Semiring.geq r a b)
        (Shows_Literal.showsl_literal "problem when comparing constant parts"))
      (\ _ ->
        Error_Monad.catch_error (check_pvars r (Ordered_Semiring.geq r) vas vbs)
          (\ x ->
            Sum_Type.Inl
              (Shows_Literal.showsl_literal
                 "problem when comparing coefficients of variable " .
                Shows_Literal.showsl x))))
    (\ x ->
      Sum_Type.Inl
        (((((Shows_Literal.showsl_literal "problem when comparing " .
              showsl_lpoly r (LPoly a vas)) .
             Shows_Literal.showsl_literal " >= ") .
            showsl_lpoly r (LPoly b vbs)) .
           Shows_Literal.showsl_literal "\n") .
          x));

sum_list_lpoly ::
  forall a b c.
    (Eq a,
      Eq c) => Congruence.Partial_object_ext a
                 (Group.Monoid_ext a (Ring.Ring_ext a b)) ->
                 [L_poly c a] -> L_poly c a;
sum_list_lpoly r =
  List.rec_list (LPoly (Ring.zero r) []) (\ x _ -> sum_lpoly r x);

showsl_l_poly ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => L_poly a b -> String -> String;
showsl_l_poly (LPoly c xcs) =
  Shows_Literal.showsl c .
    (if null xcs then id
      else Shows_Literal.showsl_lit " + " .
             Shows_Literal.showsl_sep
               (\ (x, ca) ->
                 (Shows_Literal.showsl ca . Shows_Literal.showsl_lit " * ") .
                   Shows_Literal.showsl x)
               (Shows_Literal.showsl_lit " + ") xcs);

}
