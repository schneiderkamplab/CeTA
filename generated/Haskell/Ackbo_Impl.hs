{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Ackbo_Impl(create_ACKBO_rel_impl) where {

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
import qualified Error_Monad;
import qualified Lexicographic_Extension;
import qualified Multiset_Extension2;
import qualified AC_Weight;
import qualified AC_Aux;
import qualified Multiset;
import qualified Term_Order;
import qualified HOL;
import qualified Compare;
import qualified AC_Equivalence;
import qualified Check_Monad;
import qualified Sum_Type;
import qualified Term_Rewriting;
import qualified Arith;

prec_ext :: forall a b. (a -> Maybe (Arith.Nat, b)) -> a -> a -> Bool;
prec_ext prwm =
  (\ f g -> (case prwm f of {
              Nothing -> False;
              Just pf -> (case prwm g of {
                           Nothing -> True;
                           Just pg -> Arith.less_nat (fst pg) (fst pf);
                         });
            }));

ackbo_impl ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Eq a,
      Eq b) => ((a, Arith.Nat) -> Arith.Nat) ->
                 Arith.Nat ->
                   ((a, Arith.Nat) -> (a, Arith.Nat) -> Bool) ->
                     Arith.Set a ->
                       Term_Rewriting.Term a b ->
                         Term_Rewriting.Term a b -> Bool;
ackbo_impl w w0 pr_strict ac s t =
  (if Multiset.subseteq_mset (Term_Rewriting.vars_term_ms t)
        (Term_Rewriting.vars_term_ms s) &&
        Arith.less_eq_nat (AC_Weight.weight w w0 t) (AC_Weight.weight w w0 s)
    then (if Arith.less_nat (AC_Weight.weight w w0 t) (AC_Weight.weight w w0 s)
           then True
           else (case s of {
                  Term_Rewriting.Var _ -> False;
                  Term_Rewriting.Fun f ss ->
                    (case t of {
                      Term_Rewriting.Var _ -> True;
                      Term_Rewriting.Fun g ts ->
                        (if pr_strict (f, Arith.size_list ss)
                              (g, Arith.size_list ts)
                          then True
                          else (if (f, Arith.size_list ss) ==
                                     (g, Arith.size_list ts)
                                 then (if not (Arith.member f ac) ||
    not (Arith.equal_nat (Arith.size_list ss)
          (Arith.nat_of_integer (2 :: Integer)))
then fst (Lexicographic_Extension.lex_ext
           (\ x y ->
             (ackbo_impl w w0 pr_strict ac x y,
               AC_Equivalence.equal_acterm (AC_Equivalence.acnf ac x)
                 (AC_Equivalence.acnf ac y)))
           (Arith.size_list ss) ss ts)
else (case (AC_Equivalence.actop f (Term_Rewriting.Fun f ss),
             AC_Equivalence.actop f (Term_Rewriting.Fun g ts))
       of {
       (sa, ta) ->
         (case Multiset_Extension2.mulextp
                 (\ tb u ->
                   (ackbo_impl w w0 pr_strict ac tb u,
                     AC_Equivalence.equal_acterm (AC_Equivalence.acnf ac tb)
                       (AC_Equivalence.acnf ac u)))
                 (AC_Aux.filter_fun sa (\ x y -> not (pr_strict y x))
                   (f, Arith.nat_of_integer (2 :: Integer)))
                 (Multiset.plus_multiset
                   (AC_Aux.filter_fun ta (\ x y -> not (pr_strict y x))
                     (f, Arith.nat_of_integer (2 :: Integer)))
                   (Multiset.minus_multiset
                     (Multiset.filter_mset Term_Rewriting.is_Var ta)
                     (Multiset.filter_mset Term_Rewriting.is_Var sa)))
           of {
           (True, _) -> True;
           (False, ns) ->
             (if ns && Arith.less_nat (Multiset.size_multiset ta)
                         (Multiset.size_multiset sa)
               then True
               else (if ns && Arith.equal_nat (Multiset.size_multiset sa)
                                (Multiset.size_multiset ta)
                      then Multiset_Extension2.smulextp
                             (\ tb u ->
                               (ackbo_impl w w0 pr_strict ac tb u,
                                 AC_Equivalence.equal_acterm
                                   (AC_Equivalence.acnf ac tb)
                                   (AC_Equivalence.acnf ac u)))
                             (AC_Aux.filter_fun sa (\ x y -> pr_strict y x)
                               (f, Arith.nat_of_integer (2 :: Integer)))
                             (AC_Aux.filter_fun ta (\ x y -> pr_strict y x)
                               (f, Arith.nat_of_integer (2 :: Integer)))
                      else False));
         });
     }))
                                 else False));
                    });
                }))
    else False);

ackbo_strict ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Eq a, Term_Rewriting.Showl a, Eq b,
      Term_Rewriting.Showl b) => ((a, Arith.Nat) -> (a, Arith.Nat) -> Bool) ->
                                   ((a, Arith.Nat) -> Arith.Nat) ->
                                     Arith.Nat ->
                                       Arith.Set a ->
 (Term_Rewriting.Term a b, Term_Rewriting.Term a b) ->
   Sum_Type.Sum (String -> String) ();
ackbo_strict pr w w0 acset =
  (\ (s, t) ->
    Check_Monad.check (ackbo_impl w w0 pr acset s t)
      ((((Term_Rewriting.showsl_lit "could not orient " .
           Term_Rewriting.showsl_terma s) .
          Term_Rewriting.showsl_lit " >ACKBO ") .
         Term_Rewriting.showsl_terma t) .
        Term_Rewriting.showsl_literal "\n"));

ackbo_nstrict ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Eq a, Term_Rewriting.Showl a, Eq b,
      Term_Rewriting.Showl b) => ((a, Arith.Nat) -> (a, Arith.Nat) -> Bool) ->
                                   ((a, Arith.Nat) -> Arith.Nat) ->
                                     Arith.Nat ->
                                       Arith.Set a ->
 (Term_Rewriting.Term a b, Term_Rewriting.Term a b) ->
   Sum_Type.Sum (String -> String) ();
ackbo_nstrict pr w w0 acset =
  (\ (s, t) ->
    Check_Monad.check
      (ackbo_impl w w0 pr acset s t ||
        AC_Equivalence.equal_acterm (AC_Equivalence.acnf acset s)
          (AC_Equivalence.acnf acset t))
      ((((Term_Rewriting.showsl_lit "could not orient " .
           Term_Rewriting.showsl_terma s) .
          Term_Rewriting.showsl_lit " >=ACKBO ") .
         Term_Rewriting.showsl_terma t) .
        Term_Rewriting.showsl_literal "\n"));

showsl_ackbo_repr ::
  forall a.
    (Term_Rewriting.Showl a) => ([((a, Arith.Nat),
                                    (Arith.Nat, (Arith.Nat, Bool)))],
                                  Arith.Nat) ->
                                  String -> String;
showsl_ackbo_repr (prs, w0) =
  ((((((((((((Term_Rewriting.showsl_lit
                "ACKBO with the following precedence and weight function:\n" .
               Arith.foldr
                 (\ (fn, (pr, (_, _))) ->
                   (((Term_Rewriting.showsl_lit "precedence(" .
                       Term_Rewriting.showsl_funa fn) .
                      Term_Rewriting.showsl_lit ") = ") .
                     Term_Rewriting.showsl_nat pr) .
                     Term_Rewriting.showsl_literal "\n")
                 prs) .
              Term_Rewriting.showsl_lit "precedence(_) = 0\n\n") .
             Arith.foldr
               (\ (fn, (_, (w, _))) ->
                 (((Term_Rewriting.showsl_lit "weight(" .
                     Term_Rewriting.showsl_funa fn) .
                    Term_Rewriting.showsl_lit ") = ") .
                   Term_Rewriting.showsl_nat w) .
                   Term_Rewriting.showsl_literal "\n")
               prs) .
            Term_Rewriting.showsl_lit "weight(_) = ") .
           Term_Rewriting.showsl_nat (Arith.suc w0)) .
          Term_Rewriting.showsl_lit "\nw0 = ") .
         Term_Rewriting.showsl_nat w0) .
        Term_Rewriting.showsl_literal "\n") .
       Term_Rewriting.showsl_literal "\n") .
      Term_Rewriting.showsl_list_gen
        (\ (fn, _) -> Term_Rewriting.showsl_funa fn) "no AC function symbols"
        "AC function symbols: " ", " ""
        (filter (\ (_, (_, (_, ac))) -> ac) prs)) .
     Term_Rewriting.showsl_literal "\n") .
    Term_Rewriting.showsl_list_gen (\ (fn, _) -> Term_Rewriting.showsl_funa fn)
      "no non AC function symbols" "non AC function symbols: " ", " ""
      (filter (\ (_, (_, (_, a))) -> not a) prs)) .
    Term_Rewriting.showsl_literal "\n";

prec_weight_ac_repr_to_prec_weight_funs ::
  forall a.
    (Arith.Ceq a, Arith.Ccompare a, Compare.Compare_order a,
      Arith.Set_impl a) => ([((a, Arith.Nat), (Arith.Nat, (Arith.Nat, Bool)))],
                             Arith.Nat) ->
                             ((a, Arith.Nat) -> (a, Arith.Nat) -> Bool,
                               ((a, Arith.Nat) -> Arith.Nat,
                                 (Arith.Nat, Arith.Set a)));
prec_weight_ac_repr_to_prec_weight_funs prw_w0 =
  (case prw_w0 of {
    (prw, w0) ->
      let {
        prwm = Map_Choice.ceta_map_of prw;
        w_fun =
          Map_Choice.fun_of_map_funa prwm (\ _ -> Arith.suc w0) (fst . snd);
        p_fun = prec_ext prwm;
        acset =
          Arith.set
            (Arith.map_filter
              (\ x ->
                (if (case x of {
                      (a, b) -> (case a of {
                                  (_, _) -> (\ (_, (_, ac)) -> ac);
                                })
                                  b;
                    })
                  then Just ((fst . fst) x) else Nothing))
              prw);
      } in (p_fun, (w_fun, (w0, acset)));
  });

prec_weight_ac_repr_to_prec_weight ::
  forall a.
    (Arith.Ceq a, Arith.Ccompare a, Compare.Compare_order a, Eq a,
      Arith.Set_impl a,
      Term_Rewriting.Showl a) => ([((a, Arith.Nat),
                                     (Arith.Nat, (Arith.Nat, Bool)))],
                                   Arith.Nat) ->
                                   (Sum_Type.Sum (String -> String) (),
                                     ((a, Arith.Nat) -> (a, Arith.Nat) -> Bool,
                                       ((a, Arith.Nat) -> Arith.Nat,
 (Arith.Nat, Arith.Set a))));
prec_weight_ac_repr_to_prec_weight prw_w0 =
  (case prec_weight_ac_repr_to_prec_weight_funs prw_w0 of {
    (p_fun, (w_fun, (_, acset))) ->
      (case prw_w0 of {
        (prw, w0) ->
          let {
            fs = map fst prw;
            cw_okay =
              Error_Monad.catch_error
                (Error_Monad.forallM
                  (\ fn ->
                    Check_Monad.check
                      (if Arith.equal_nat (snd fn) Arith.zero_nat
                        then Arith.less_eq_nat w0 (w_fun fn) else True)
                      ((Term_Rewriting.showsl_lit "weight of constant " .
                         Term_Rewriting.showsl (fst fn)) .
                        Term_Rewriting.showsl_lit " must be at least w0"))
                  fs)
                (\ x -> Sum_Type.Inl (snd x));
            adm = Error_Monad.catch_error
                    (Error_Monad.forallM
                      (\ fn ->
                        Check_Monad.check
                          (if Arith.equal_nat (snd fn) Arith.one_nat
                            then (if Arith.equal_nat (w_fun fn) Arith.zero_nat
                                   then all (\ x -> p_fun fn x || x == fn) fs
                                   else True)
                            else True)
                          ((Term_Rewriting.showsl_lit "unary symbol " .
                             Term_Rewriting.showsl (fst fn)) .
                            Term_Rewriting.showsl_lit
                              " with weight 0 does not have maximal precedence"))
                      (map fst prw))
                    (\ x -> Sum_Type.Inl (snd x));
            irr = Error_Monad.catch_error
                    (Error_Monad.forallM
                      (\ fn ->
                        Check_Monad.check (not (p_fun fn fn))
                          ((Term_Rewriting.showsl_lit "function symbol " .
                             Term_Rewriting.showsl (fst fn)) .
                            Term_Rewriting.showsl_lit
                              " violates irreflexibity"))
                      fs)
                    (\ x -> Sum_Type.Inl (snd x));
            ok = Error_Monad.bind
                   (Check_Monad.check (Arith.less_nat Arith.zero_nat w0)
                     (Term_Rewriting.showsl_lit "w0 must be larger than 0"))
                   (\ _ ->
                     Error_Monad.bind adm
                       (\ _ -> Error_Monad.bind cw_okay (\ _ -> irr)));
          } in (ok, (p_fun, (w_fun, (w0, acset))));
      });
  });

create_ACKBO_rel_impl ::
  forall a b c.
    (Term_Rewriting.Showl a, Arith.Ceq b, Arith.Ccompare b,
      Compare.Compare_order b, Eq b, Arith.Set_impl b, Term_Rewriting.Showl b,
      Eq c,
      Term_Rewriting.Showl c) => (([((a, Arith.Nat),
                                      (Arith.Nat, (Arith.Nat, Bool)))],
                                    Arith.Nat) ->
                                   ([((b, Arith.Nat),
                                       (Arith.Nat, (Arith.Nat, Bool)))],
                                     Arith.Nat)) ->
                                   ([((a, Arith.Nat),
                                       (Arith.Nat, (Arith.Nat, Bool)))],
                                     Arith.Nat) ->
                                     Term_Rewriting.Rel_impl_ext b c ();
create_ACKBO_rel_impl f_to_g pr =
  (case prec_weight_ac_repr_to_prec_weight (f_to_g pr) of {
    (ch, (p, (w, (w0, ac)))) ->
      let {
        ns = ackbo_nstrict p w w0 ac;
        s = ackbo_strict p w w0 ac;
      } in Term_Rewriting.Rel_impl_ext ch (Sum_Type.Inr ())
             (showsl_ackbo_repr pr) s ns ns Term_Order.full_af
             Term_Order.full_af (Sum_Type.Inr ()) (Sum_Type.Inr ())
             (Sum_Type.Inr ()) (Sum_Type.Inr ()) (Sum_Type.Inr ())
             (Sum_Type.Inr ()) Term_Order.full_af (\ _ -> Sum_Type.Inr ())
             (Just []) (Just []) Term_Rewriting.no_complexity_check ();
  });

}
