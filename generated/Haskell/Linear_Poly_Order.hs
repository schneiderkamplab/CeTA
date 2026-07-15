{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Linear_Poly_Order(create_poly_rel_impl) where {

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
import qualified Name;
import qualified Check_Monad;
import qualified Term_Order;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Set_Interval;
import qualified Map_Choice;
import qualified Linear_Poly_Complexity;
import qualified Compare;
import qualified Compare_Order_Instances;
import qualified HOL;
import qualified Ordered_Semiring;
import qualified Congruence;
import qualified Group;
import qualified Ring;
import qualified Arith;
import qualified Term_Rewriting;

pleftI ::
  forall a b c d.
    (Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a, Eq a, Arith.Set_impl a,
      Eq d) => Congruence.Partial_object_ext a
                 (Group.Monoid_ext a
                   (Ring.Ring_ext a
                     (Ordered_Semiring.Ordered_semiring_ext a b))) ->
                 ((c, Arith.Nat) -> (a, [a])) ->
                   Term_Rewriting.Term c d -> Term_Rewriting.L_poly d a;
pleftI r pi (Term_Rewriting.Var x) =
  Term_Rewriting.LPoly (Ring.zero r) [(x, Group.one r)];
pleftI r pi (Term_Rewriting.Fun f ts) =
  (case pi (f, Arith.size_list ts) of {
    (c, asa) ->
      (case Term_Rewriting.sum_lpoly r (Term_Rewriting.LPoly c [])
              (Term_Rewriting.list_prod
                (Congruence.Partial_object_ext
                  (Arith.collect (Term_Rewriting.wf_lpoly r))
                  (Group.Monoid_ext (Term_Rewriting.sum_lpoly r)
                    (Term_Rewriting.LPoly (Ring.zero r) []) ()))
                (map (\ at ->
                       Term_Rewriting.mul_lpoly r (fst at)
                         (pleftI r pi (snd at)))
                  (zip asa ts)))
        of {
        Term_Rewriting.LPoly d [] ->
          Term_Rewriting.LPoly (Ordered_Semiring.max r (Ring.zero r) d) [];
        Term_Rewriting.LPoly d (ab : lista) ->
          Term_Rewriting.LPoly d (ab : lista);
      });
  });

prightI ::
  forall a b c d.
    (Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a, Eq a, Arith.Set_impl a,
      Eq d) => Congruence.Partial_object_ext a
                 (Group.Monoid_ext a
                   (Ring.Ring_ext a
                     (Ordered_Semiring.Ordered_semiring_ext a b))) ->
                 ((c, Arith.Nat) -> (a, [a])) ->
                   Term_Rewriting.Term c d -> Term_Rewriting.L_poly d a;
prightI r pi (Term_Rewriting.Var x) =
  Term_Rewriting.LPoly (Ring.zero r) [(x, Group.one r)];
prightI r pi (Term_Rewriting.Fun f ts) =
  (case pi (f, Arith.size_list ts) of {
    (c, asa) ->
      (case Term_Rewriting.sum_lpoly r (Term_Rewriting.LPoly c [])
              (Term_Rewriting.list_prod
                (Congruence.Partial_object_ext
                  (Arith.collect (Term_Rewriting.wf_lpoly r))
                  (Group.Monoid_ext (Term_Rewriting.sum_lpoly r)
                    (Term_Rewriting.LPoly (Ring.zero r) []) ()))
                (map (\ at ->
                       Term_Rewriting.mul_lpoly r (fst at)
                         (prightI r pi (snd at)))
                  (zip asa ts)))
        of {
        Term_Rewriting.LPoly d a ->
          Term_Rewriting.LPoly (Ordered_Semiring.max r (Ring.zero r) d) a;
      });
  });

create_af ::
  forall a b c.
    (Eq a,
      Compare.Compare_order c) => Congruence.Partial_object_ext a
                                    (Group.Monoid_ext a
                                      (Ring.Ring_ext a
(Ordered_Semiring.Ordered_semiring_ext a
  (Linear_Poly_Complexity.Lpoly_order_semiring_ext a b)))) ->
                                    [((c, Arith.Nat), (a, [a]))] ->
                                      (c, Arith.Nat) -> Arith.Set Arith.Nat;
create_af r i =
  Map_Choice.fun_of_map_funa (Map_Choice.ceta_map_of i)
    (\ (_, a) -> Set_Interval.atLeastLessThan Arith.zero_nat a)
    (\ (_, coeffs) ->
      Arith.set
        (concatMap (\ (c, ia) -> (if not (c == Ring.zero r) then [ia] else []))
          (zip coeffs (Arith.upt Arith.zero_nat (Arith.size_list coeffs)))));

check_polo_s ::
  forall a b c d.
    (Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a, Eq a, Arith.Set_impl a,
      Term_Rewriting.Showl a, Term_Rewriting.Showl c, Eq d,
      Term_Rewriting.Showl d) => Congruence.Partial_object_ext a
                                   (Group.Monoid_ext a
                                     (Ring.Ring_ext a
                                       (Ordered_Semiring.Ordered_semiring_ext a
 (Linear_Poly_Complexity.Lpoly_order_semiring_ext a b)))) ->
                                   ((c, Arith.Nat) -> (a, [a])) ->
                                     (Term_Rewriting.Term c d,
                                       Term_Rewriting.Term c d) ->
                                       Sum_Type.Sum (String -> String) ();
check_polo_s r pi (s, t) =
  let {
    left = pleftI r pi s;
    right = prightI r pi t;
  } in Error_Monad.catch_error (Term_Rewriting.check_lpoly_s r left right)
         (\ x ->
           Sum_Type.Inl
             (((((Term_Rewriting.showsl_literal "could not ensure " .
                   Term_Rewriting.showsl_terma s) .
                  Term_Rewriting.showsl_literal " > ") .
                 Term_Rewriting.showsl_terma t) .
                Term_Rewriting.showsl_literal "\n") .
               x));

check_polo_ns ::
  forall a b c d.
    (Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a, Eq a, Arith.Set_impl a,
      Term_Rewriting.Showl a, Term_Rewriting.Showl c, Eq d,
      Term_Rewriting.Showl d) => Congruence.Partial_object_ext a
                                   (Group.Monoid_ext a
                                     (Ring.Ring_ext a
                                       (Ordered_Semiring.Ordered_semiring_ext a
 (Linear_Poly_Complexity.Lpoly_order_semiring_ext a b)))) ->
                                   ((c, Arith.Nat) -> (a, [a])) ->
                                     (Term_Rewriting.Term c d,
                                       Term_Rewriting.Term c d) ->
                                       Sum_Type.Sum (String -> String) ();
check_polo_ns r pi (s, t) =
  let {
    left = pleftI r pi s;
    right = prightI r pi t;
  } in Error_Monad.catch_error (Term_Rewriting.check_lpoly_ns r left right)
         (\ x ->
           Sum_Type.Inl
             (((((Term_Rewriting.showsl_literal "could not ensure " .
                   Term_Rewriting.showsl_terma s) .
                  Term_Rewriting.showsl_literal " >= ") .
                 Term_Rewriting.showsl_terma t) .
                Term_Rewriting.showsl_literal "\n") .
               x));

create_mono_af ::
  forall a b c.
    (Eq a,
      Compare.Compare_order c) => Congruence.Partial_object_ext a
                                    (Group.Monoid_ext a
                                      (Ring.Ring_ext a
(Ordered_Semiring.Ordered_semiring_ext a
  (Linear_Poly_Complexity.Lpoly_order_semiring_ext a b)))) ->
                                    [((c, Arith.Nat), (a, [a]))] ->
                                      (c, Arith.Nat) -> Arith.Set Arith.Nat;
create_mono_af r i =
  (if Linear_Poly_Complexity.plus_single_mono r
    then Map_Choice.fun_of_map_funa (Map_Choice.ceta_map_of i)
           (\ (_, a) -> Set_Interval.atLeastLessThan Arith.zero_nat a)
           (\ (c, coeffs) ->
             Arith.set
               (if Ordered_Semiring.geq r c (Ring.zero r)
                 then concatMap
                        (\ (ca, ia) ->
                          (if ca == Group.one r ||
                                Linear_Poly_Complexity.checkmono r ca
                            then [ia] else []))
                        (zip coeffs
                          (Arith.upt Arith.zero_nat (Arith.size_list coeffs)))
                 else []))
    else Term_Order.empty_af);

to_lpoly_inter ::
  forall a b c.
    (Compare.Compare_order c) => Congruence.Partial_object_ext a
                                   (Group.Monoid_ext a
                                     (Ring.Ring_ext a
                                       (Ordered_Semiring.Ordered_semiring_ext a
 (Linear_Poly_Complexity.Lpoly_order_semiring_ext a b)))) ->
                                   [((c, Arith.Nat), (a, [a]))] ->
                                     (c, Arith.Nat) -> (a, [a]);
to_lpoly_inter r i =
  Map_Choice.fun_of_map_fun (Map_Choice.ceta_map_of i)
    (\ fn ->
      (Linear_Poly_Complexity.defaulta r,
        Arith.replicate (snd fn) (Group.one r)));

check_poly_mono ::
  forall a b c.
    (Term_Rewriting.Showl a,
      Term_Rewriting.Showl c) => Congruence.Partial_object_ext a
                                   (Group.Monoid_ext a
                                     (Ring.Ring_ext a
                                       (Ordered_Semiring.Ordered_semiring_ext a
 (Linear_Poly_Complexity.Lpoly_order_semiring_ext a b)))) ->
                                   [((c, Arith.Nat), (a, [a]))] ->
                                     Sum_Type.Sum (String -> String) ();
check_poly_mono r =
  (\ xs ->
    Error_Monad.catch_error
      (Error_Monad.forallM
        (\ (a, b) ->
          (case a of {
            (f, n) ->
              (\ (c, cs) ->
                Error_Monad.catch_error
                  (Error_Monad.bind
                    (Check_Monad.check (Ordered_Semiring.geq r c (Ring.zero r))
                      ((((Term_Rewriting.showsl_literal "constant part " .
                           Term_Rewriting.showsl c) .
                          Term_Rewriting.showsl_literal " must be at least ") .
                         Term_Rewriting.showsl (Ring.zero r)) .
                        Term_Rewriting.showsl_literal "\n"))
                    (\ _ ->
                      Error_Monad.bind
                        (Check_Monad.check
                          (Arith.less_eq_nat n (Arith.size_list cs))
                          (Term_Rewriting.showsl_literal
                            "the last argument is ignored\n"))
                        (\ _ ->
                          Error_Monad.catch_error
                            (Error_Monad.forallM
                              (\ d ->
                                Check_Monad.check
                                  (Linear_Poly_Complexity.checkmono r d)
                                  ((Term_Rewriting.showsl_literal
                                      "coefficient " .
                                     Term_Rewriting.showsl d) .
                                    Term_Rewriting.showsl_literal
                                      " is not allowed\n"))
                              cs)
                            (\ x -> Sum_Type.Inl (snd x)))))
                  (\ x ->
                    Sum_Type.Inl
                      (((((Term_Rewriting.showsl_literal
                             "problem with monotonicity due to interpretation of " .
                            Term_Rewriting.showsl f) .
                           Term_Rewriting.showsl_literal "/") .
                          Term_Rewriting.showsl_nat n) .
                         Term_Rewriting.showsl_literal "\n") .
                        x)));
          })
            b)
        xs)
      (\ x -> Sum_Type.Inl (snd x)));

create_lpoly_repr ::
  forall a b.
    (Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a, Eq a, Arith.Set_impl a,
      Term_Rewriting.Showl a, Compare.Compare_order b, Eq b,
      Term_Rewriting.Showl b) => Congruence.Partial_object_ext a
                                   (Group.Monoid_ext a
                                     (Ring.Ring_ext a
                                       (Ordered_Semiring.Ordered_semiring_ext a
 (Linear_Poly_Complexity.Lpoly_order_semiring_ext a ())))) ->
                                   [((b, Arith.Nat), (a, [a]))] ->
                                     String -> String;
create_lpoly_repr c i =
  let {
    pi = to_lpoly_inter c i;
  } in ((Term_Rewriting.showsl_literal "polynomial interpretation over " .
          Linear_Poly_Complexity.description c) .
         Term_Rewriting.showsl_literal "\n") .
         Term_Rewriting.showsl_sep
           (\ (f, n) ->
             let {
               t = Term_Rewriting.Fun f
                     (map Term_Rewriting.Var
                       (Name.fresh_strings_list
                         [Arith.char_0x78, Arith.char_0x5F] Arith.one_nat []
                         n));
             } in ((Term_Rewriting.showsl_literal "Pol(" .
                     Term_Rewriting.showsl_terma t) .
                    Term_Rewriting.showsl_literal ") = ") .
                    Term_Rewriting.showsl_lpoly c (pleftI c pi t))
           (Term_Rewriting.showsl_literal "\n") (Arith.remdups (map fst i));

check_lpoly_coeffs ::
  forall a b c.
    (Arith.Ceq a, Arith.Ccompare a, Term_Rewriting.Showl a,
      Term_Rewriting.Showl c) => Congruence.Partial_object_ext a
                                   (Group.Monoid_ext a
                                     (Ring.Ring_ext a
                                       (Ordered_Semiring.Ordered_semiring_ext a
 (Linear_Poly_Complexity.Lpoly_order_semiring_ext a b)))) ->
                                   [((c, Arith.Nat), (a, [a]))] ->
                                     Sum_Type.Sum (String -> String) ();
check_lpoly_coeffs r i =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ (a, b) ->
        (case a of {
          (f, n) ->
            (\ (c, cs) ->
              Error_Monad.catch_error
                (Error_Monad.bind
                  (Check_Monad.check (Arith.member c (Congruence.carrier r))
                    ((Term_Rewriting.showsl_literal "constant part " .
                       Term_Rewriting.showsl c) .
                      Term_Rewriting.showsl_literal " is not well-formed\n"))
                  (\ _ ->
                    Error_Monad.bind
                      (Check_Monad.check
                        (Arith.less_eq_nat (Arith.size_list cs) n)
                        (Term_Rewriting.showsl_literal
                           "number of coefficients exceeds arity of symbol " .
                          Term_Rewriting.showsl f))
                      (\ _ ->
                        Error_Monad.bind
                          (Check_Monad.check
                            (Linear_Poly_Complexity.arcpos r c ||
                              any (Linear_Poly_Complexity.arcpos r) cs)
                            (Term_Rewriting.showsl_literal
                              "could not find positive entry which is required for arctic interpretations\n"))
                          (\ _ ->
                            Error_Monad.catch_error
                              (Error_Monad.forallM
                                (\ aa ->
                                  Check_Monad.check
                                    (Ordered_Semiring.geq r aa (Ring.zero r) &&
                                      Arith.member aa (Congruence.carrier r))
                                    ((Term_Rewriting.showsl_literal
"coefficient " .
                                       Term_Rewriting.showsl aa) .
                                      Term_Rewriting.showsl_literal
" is not allowed\n"))
                                cs)
                              (\ x -> Sum_Type.Inl (snd x))))))
                (\ x ->
                  Sum_Type.Inl
                    (((((Term_Rewriting.showsl_literal
                           "problem with interpretation of " .
                          Term_Rewriting.showsl f) .
                         Term_Rewriting.showsl_literal "/") .
                        Term_Rewriting.showsl_nat n) .
                       Term_Rewriting.showsl_literal "\n") .
                      x)));
        })
          b)
      i)
    (\ x -> Sum_Type.Inl (snd x));

check_poly_mono_npsm ::
  forall a b c.
    (Eq a, Term_Rewriting.Showl a, Eq c,
      Term_Rewriting.Showl c) => Congruence.Partial_object_ext a
                                   (Group.Monoid_ext a
                                     (Ring.Ring_ext a
                                       (Ordered_Semiring.Ordered_semiring_ext a
 (Linear_Poly_Complexity.Lpoly_order_semiring_ext a b)))) ->
                                   [(c, Arith.Nat)] ->
                                     [((c, Arith.Nat), (a, [a]))] ->
                                       Sum_Type.Sum (String -> String) ();
check_poly_mono_npsm r f pi =
  Error_Monad.bind
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ (a, b) ->
          (case a of {
            (fa, n) ->
              (\ (c, cs) ->
                Error_Monad.catch_error
                  (Error_Monad.bind
                    (Check_Monad.check
                      (if Arith.equal_nat n (Arith.suc Arith.zero_nat)
                        then c == Ring.zero r else True)
                      ((Term_Rewriting.showsl_literal "constant part " .
                         Term_Rewriting.showsl c) .
                        Term_Rewriting.showsl_literal " must be 0\n"))
                    (\ _ ->
                      Error_Monad.bind
                        (Check_Monad.check
                          (Arith.equal_nat n (Arith.size_list cs))
                          (Term_Rewriting.showsl_literal
                            "the arity is not the same as the number of arguments\n"))
                        (\ _ ->
                          Check_Monad.check
                            (Arith.less_eq_nat n (Arith.suc Arith.zero_nat))
                            (Term_Rewriting.showsl_literal
                              "symbol has arity larger than 1\n"))))
                  (\ x ->
                    Sum_Type.Inl
                      (((((Term_Rewriting.showsl_literal
                             "problem with monotonicity due to interpretation of " .
                            Term_Rewriting.showsl fa) .
                           Term_Rewriting.showsl_literal "/") .
                          Term_Rewriting.showsl_nat n) .
                         Term_Rewriting.showsl_literal "\n") .
                        x)));
          })
            b)
        pi)
      (\ x -> Sum_Type.Inl (snd x)))
    (\ _ ->
      Error_Monad.catch_error (Check_Monad.check_subseteq f (map fst pi))
        (\ x ->
          Sum_Type.Inl
            ((Term_Rewriting.showsl_literal "unknown interpretation for " .
               Term_Rewriting.showsl_prod x) .
              Term_Rewriting.showsl_literal "\n")));

poly_c_max_inter_bcoeff_strict ::
  forall a b c.
    Congruence.Partial_object_ext a
      (Group.Monoid_ext a
        (Ring.Ring_ext a (Ordered_Semiring.Ordered_semiring_ext a b))) ->
      [(c, Arith.Nat)] -> ((c, Arith.Nat) -> (a, [a])) -> a;
poly_c_max_inter_bcoeff_strict r f pi =
  Arith.foldr (Ordered_Semiring.max r) (concatMap (\ fn -> snd (pi fn)) f)
    (Ring.zero r);

poly_c_max_inter_bcoeff ::
  forall a b c.
    Congruence.Partial_object_ext a
      (Group.Monoid_ext a
        (Ring.Ring_ext a (Ordered_Semiring.Ordered_semiring_ext a b))) ->
      [(c, Arith.Nat)] -> ((c, Arith.Nat) -> (a, [a])) -> a;
poly_c_max_inter_bcoeff r f pi =
  Arith.foldr (Ordered_Semiring.max r)
    (concatMap
      (\ fn ->
        filter (\ b -> not (Ordered_Semiring.geq r (Group.one r) b))
          (snd (pi fn)))
      f)
    (Ring.zero r);

convert_lpoly_complexity ::
  forall a b c d.
    (Eq a) => Congruence.Partial_object_ext a
                (Group.Monoid_ext a
                  (Ring.Ring_ext a
                    (Ordered_Semiring.Ordered_semiring_ext a
                      (Linear_Poly_Complexity.Lpoly_order_semiring_ext a
                        b)))) ->
                ((c, Arith.Nat) -> (a, [a])) ->
                  Term_Rewriting.Complexity_measure c d ->
                    Term_Rewriting.Complexity_class ->
                      Sum_Type.Sum (String -> String) ();
convert_lpoly_complexity r pi cm (Term_Rewriting.Comp_Poly deg) =
  let {
    f = (case cm of {
          Term_Rewriting.Derivational_Complexity f -> f;
          Term_Rewriting.Runtime_Complexity c _ -> c;
        });
    bc = poly_c_max_inter_bcoeff r f pi;
    bca = poly_c_max_inter_bcoeff_strict r f pi;
  } in Error_Monad.bind
         (Check_Monad.check
           (Arith.less_nat Arith.zero_nat deg || bca == Ring.zero r)
           (Term_Rewriting.showsl_literal
             "constant complexity not fully supported for linear (poly/matrix)-interpretations"))
         (\ _ ->
           Linear_Poly_Complexity.check_complexity r bc
             (Arith.minus_nat deg Arith.one_nat));

create_poly_rel_impl ::
  forall a b c.
    (Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a, Eq a, Arith.Set_impl a,
      Term_Rewriting.Showl a, Compare.Compare_order b, Eq b,
      Term_Rewriting.Showl b, Eq c,
      Term_Rewriting.Showl c) => Congruence.Partial_object_ext a
                                   (Group.Monoid_ext a
                                     (Ring.Ring_ext a
                                       (Ordered_Semiring.Ordered_semiring_ext a
 (Linear_Poly_Complexity.Lpoly_order_semiring_ext a ())))) ->
                                   Sum_Type.Sum (String -> String) () ->
                                     [((b, Arith.Nat), (a, [a]))] ->
                                       Term_Rewriting.Rel_impl_ext b c ();
create_poly_rel_impl c cI i =
  let {
    pi = to_lpoly_inter c i;
    ns = check_polo_ns c pi;
  } in Term_Rewriting.Rel_impl_ext
         (Error_Monad.bind cI (\ _ -> check_lpoly_coeffs c i)) (Sum_Type.Inr ())
         (create_lpoly_repr c i) (check_polo_s c pi) ns ns (create_af c i)
         (create_af c i) (Sum_Type.Inr ()) (Sum_Type.Inr ()) (Sum_Type.Inr ())
         (Sum_Type.Inr ()) (Sum_Type.Inr ()) (Sum_Type.Inr ())
         (create_mono_af c i)
         (\ sig ->
           (if Linear_Poly_Complexity.plus_single_mono c
             then check_poly_mono c i else check_poly_mono_npsm c sig i))
         (Just (map fst i))
         (if Linear_Poly_Complexity.plus_single_mono c then Just (map fst i)
           else Nothing)
         (if Linear_Poly_Complexity.plus_single_mono c
           then convert_lpoly_complexity c pi
           else Term_Rewriting.no_complexity_check)
         ();

}
