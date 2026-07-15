{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Ifrit_Impl(check_Ifrit_rules_iff) where {

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
import qualified Tcap_Impl;
import qualified HOL;
import qualified Gtcap_Impl;
import qualified Term_Rewriting;
import qualified Arith;

gT_impl ::
  forall a b c d e.
    (Eq a) => [(Term_Rewriting.Term a b, Term_Rewriting.Term a c)] ->
                Term_Rewriting.Term a d -> Term_Rewriting.Term a e -> Bool;
gT_impl r s t =
  Term_Rewriting.is_Var s ||
    (Term_Rewriting.is_Var t ||
      (Gtcap_Impl.mk_gt_fun r (Term_Rewriting.root s) (Term_Rewriting.root t) ||
        (Gtcap_Impl.mk_gt_fun r (Term_Rewriting.root s) Nothing ||
          (Gtcap_Impl.mk_gt_fun r Nothing (Term_Rewriting.root t) ||
            Gtcap_Impl.mk_gt_fun r Nothing Nothing))));

p_gt_impl ::
  forall a b c.
    (Eq a,
      Eq b) => [((Term_Rewriting.Term a b, Term_Rewriting.Term a b), c)] ->
                 Term_Rewriting.Term a b -> Term_Rewriting.Term a b -> Bool;
p_gt_impl sa s t =
  (case (s, t) of {
    (Term_Rewriting.Var _, _) -> True;
    (Term_Rewriting.Fun _ _, Term_Rewriting.Var _) -> True;
    (Term_Rewriting.Fun f ss, Term_Rewriting.Fun g ts) ->
      let {
        r = map fst sa;
      } in Term_Rewriting.matcha (Tcap_Impl.tcapI r s) t &&
             ((f, Arith.size_list ss) == (g, Arith.size_list ts) ||
               gT_impl r s t &&
                 any (\ (l, _) -> Term_Rewriting.matcha (Tcap_Impl.tcapI r s) l)
                   r);
  });

ifrit_impl ::
  forall a b. ([(a, b)] -> b -> Bool) -> [(a, b)] -> Arith.Nat -> [(a, b)];
ifrit_impl p r n =
  (if Arith.equal_nat n Arith.zero_nat then []
    else filter
           (\ (_, a) -> p (ifrit_impl p r (Arith.minus_nat n Arith.one_nat)) a)
           r);

p_Join_impl ::
  forall a b.
    (Eq a,
      Eq b) => [((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                  [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)])] ->
                 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] -> Bool;
p_Join_impl r cs =
  all (\ (s, u) ->
        all (\ (t, v) ->
              (if not (Term_Rewriting.equal_term s t) &&
                    Term_Rewriting.equal_term u v
                then Term_Rewriting.unifiable (Tcap_Impl.tcapI (map fst r) s)
                       (Tcap_Impl.tcapI (map fst r) t)
                else True))
          cs)
    cs;

p_gt_cs_impl ::
  forall a b.
    (Eq a,
      Eq b) => [((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                  [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)])] ->
                 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] -> Bool;
p_gt_cs_impl s cs = all (\ (a, b) -> p_gt_impl s a b) cs;

p_full_impl ::
  forall a b.
    (Eq a,
      Eq b) => [((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                  [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)])] ->
                 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] -> Bool;
p_full_impl r cs = p_gt_cs_impl r cs && p_Join_impl r cs;

ifrit_impl_full :: forall a b. ([(a, b)] -> b -> Bool) -> [(a, b)] -> [(a, b)];
ifrit_impl_full p r = ifrit_impl p r (Arith.size_list r);

ifrit_full_impl ::
  forall a b.
    (Eq a,
      Eq b) => [((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                  [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)])] ->
                 [((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                    [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)])];
ifrit_full_impl r = ifrit_impl_full p_full_impl r;

check_Ifrit_rules_iff ::
  forall a b.
    (Eq a,
      Eq b) => [((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                  [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)])] ->
                 [((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                    [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)])] ->
                   Bool;
check_Ifrit_rules_iff r s =
  Arith.superset r s && Arith.superset s (ifrit_full_impl r);

}
