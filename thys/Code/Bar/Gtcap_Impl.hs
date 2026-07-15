{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Gtcap_Impl(mk_gt_fun, nonreachable_gtcapRM) where {

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
import qualified Compare;
import qualified Transitive_Closure_List_Impl;
import qualified Tcap_Impl;
import qualified HOL;
import qualified Term_Rewriting;
import qualified Arith;

gt1 ::
  forall a b c d.
    [(Term_Rewriting.Term a b, Term_Rewriting.Term c d)] ->
      [(Maybe (a, Arith.Nat), Maybe (c, Arith.Nat))];
gt1 = map (\ (s, t) -> (Term_Rewriting.root s, Term_Rewriting.root t));

gt_term ::
  forall a b c d.
    (Eq a,
      Eq c) => Bool ->
                 Bool ->
                   (Maybe (a, Arith.Nat) -> Maybe (b, Arith.Nat) -> Bool) ->
                     ((a, Arith.Nat) ->
                       [(Term_Rewriting.Term a c, Term_Rewriting.Term a c)]) ->
                       Term_Rewriting.Term a c ->
                         Term_Rewriting.Term b d -> Bool;
gt_term nlv ne gt_fun rm s t =
  ne && let {
          root1 = Term_Rewriting.root s;
          root2 = Term_Rewriting.root t;
        } in (Term_Rewriting.is_Var s ||
               (Term_Rewriting.is_Var t ||
                 (gt_fun Nothing Nothing ||
                   (gt_fun root1 root2 ||
                     (gt_fun root1 Nothing || gt_fun Nothing root2))))) &&
               (if nlv
                 then (case root1 of {
                        Nothing -> True;
                        Just fn ->
                          any (\ r ->
                                Term_Rewriting.matcha
                                  (Tcap_Impl.tcapRM nlv rm s) (fst r))
                            (rm fn);
                      })
                 else True);

rd_impl ::
  forall a b c.
    (Eq a) => (Term_Rewriting.Term a b -> Term_Rewriting.Term a c -> Bool) ->
                (Term_Rewriting.Term a b, Term_Rewriting.Term a c) ->
                  [(Term_Rewriting.Term a b, Term_Rewriting.Term a c)];
rd_impl gt (Term_Rewriting.Fun f ss, Term_Rewriting.Fun g ts) =
  (if f == g &&
        Arith.equal_nat (Arith.size_list ss) (Arith.size_list ts) &&
          not (gt (Term_Rewriting.Fun f ss) (Term_Rewriting.Fun g ts))
    then concatMap (rd_impl gt) (zip ss ts)
    else [(Term_Rewriting.Fun f ss, Term_Rewriting.Fun g ts)]);
rd_impl uu (Term_Rewriting.Var v, t) = [(Term_Rewriting.Var v, t)];
rd_impl uu (s, Term_Rewriting.Var v) = [(s, Term_Rewriting.Var v)];

nonreach ::
  forall a b c.
    (Eq a) => (Term_Rewriting.Term a b -> Term_Rewriting.Term a c -> Bool) ->
                Term_Rewriting.Term a b -> Term_Rewriting.Term a c -> Bool;
nonreach gt s t =
  (case (s, t) of {
    (Term_Rewriting.Var _, _) -> False;
    (Term_Rewriting.Fun _ _, Term_Rewriting.Var _) -> False;
    (Term_Rewriting.Fun f ss, Term_Rewriting.Fun g ts) ->
      not ((f, Arith.size_list ss) == (g, Arith.size_list ts)) && not (gt s t);
  });

group_key :: forall a b. (Eq b) => (a -> b) -> [a] -> [[a]];
group_key f [] = [];
group_key f (x : xs) =
  (x : takeWhile (\ y -> f x == f y) xs) :
    group_key f (dropWhile (\ y -> f x == f y) xs);

mk_gt_fun ::
  forall a b c.
    (Eq a) => [(Term_Rewriting.Term a b, Term_Rewriting.Term a c)] ->
                Maybe (a, Arith.Nat) -> Maybe (a, Arith.Nat) -> Bool;
mk_gt_fun rs =
  let {
    in_trancl = Transitive_Closure_List_Impl.memo_list_trancl (gt1 rs);
  } in (\ f -> Arith.membera (in_trancl f));

nonlinear_var_nonreach ::
  forall a b c d.
    (Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a, Eq a, Arith.Set_impl a,
      Compare.Compare b, Eq b, Compare.Compare c,
      Eq c) => [(a, Arith.Nat)] ->
                 (Maybe (a, Arith.Nat) -> Maybe (a, Arith.Nat) -> Bool) ->
                   [(Term_Rewriting.Term b c, Term_Rewriting.Term a d)] -> Bool;
nonlinear_var_nonreach f gt_fun xs =
  let {
    xs1 = filter (Term_Rewriting.is_Var . fst) xs;
    xs2 = Arith.sort_key fst xs1;
    a = group_key fst xs2;
  } in any (\ xts ->
             Arith.less_nat Arith.one_nat (Arith.size_list xts) &&
               all (\ fa ->
                     not (gt_fun (Just fa) Nothing) &&
                       any (\ (_, v) ->
                             not (Term_Rewriting.is_Var v) &&
                               Arith.less_eq_set (Term_Rewriting.funas_term v)
                                 (Arith.set f) &&
                                 not (Term_Rewriting.root v == Just fa) &&
                                   not (gt_fun (Just fa)
 (Term_Rewriting.root v)))
                         xts)
                 f)
         a;

nonreachable_gtcapRM ::
  forall a b c.
    (Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a, Compare.Compare a, Eq a,
      Arith.Set_impl a, Compare.Compare b,
      Eq b) => [(a, Arith.Nat)] ->
                 Bool ->
                   Bool ->
                     (Maybe (a, Arith.Nat) -> Maybe (a, Arith.Nat) -> Bool) ->
                       ((a, Arith.Nat) ->
                         [(Term_Rewriting.Term a b,
                            Term_Rewriting.Term a b)]) ->
                         Term_Rewriting.Term a b ->
                           Term_Rewriting.Term a c -> Bool;
nonreachable_gtcapRM fs nlv ne gt_fun rm s t =
  let {
    gt = gt_term nlv ne gt_fun rm;
    rs = rd_impl gt (s, t);
  } in any (\ (a, b) -> nonreach gt a b) rs ||
         nlv && ne && nonlinear_var_nonreach fs gt_fun rs;

}
