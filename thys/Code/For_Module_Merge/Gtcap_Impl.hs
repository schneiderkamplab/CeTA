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
import qualified Subterm_and_Context;
import qualified Set;
import qualified Term_Impl;
import qualified Collection_Order;
import qualified Collection_Enum;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Compare;
import qualified Transitive_Closure_List_Impl;
import qualified List;
import qualified Option;
import qualified Tcap_Impl;
import qualified HOL;
import qualified Ground_Context;
import qualified Product_Type;
import qualified Term;
import qualified Arith;

gt1 ::
  forall a b c d.
    [(Term.Term a b, Term.Term c d)] ->
      [(Maybe (a, Arith.Nat), Maybe (c, Arith.Nat))];
gt1 = map (\ (s, t) -> (Term.root s, Term.root t));

gt_term ::
  forall a b c d.
    (Eq a,
      Eq c) => Bool ->
                 Bool ->
                   (Maybe (a, Arith.Nat) -> Maybe (b, Arith.Nat) -> Bool) ->
                     ((a, Arith.Nat) -> [(Term.Term a c, Term.Term a c)]) ->
                       Term.Term a c -> Term.Term b d -> Bool;
gt_term nlv ne gt_fun rm s t =
  ne && let {
          root1 = Term.root s;
          root2 = Term.root t;
        } in (Term.is_Var s ||
               (Term.is_Var t ||
                 (gt_fun Nothing Nothing ||
                   (gt_fun root1 root2 ||
                     (gt_fun root1 Nothing || gt_fun Nothing root2))))) &&
               (if nlv
                 then (case root1 of {
                        Nothing -> True;
                        Just fn ->
                          any (\ r ->
                                Ground_Context.match (Tcap_Impl.tcapRM nlv rm s)
                                  (fst r))
                            (rm fn);
                      })
                 else True);

rd_impl ::
  forall a b c.
    (Eq a) => (Term.Term a b -> Term.Term a c -> Bool) ->
                (Term.Term a b, Term.Term a c) ->
                  [(Term.Term a b, Term.Term a c)];
rd_impl gt (Term.Fun f ss, Term.Fun g ts) =
  (if f == g &&
        Arith.equal_nat (List.size_list ss) (List.size_list ts) &&
          not (gt (Term.Fun f ss) (Term.Fun g ts))
    then concatMap (rd_impl gt) (zip ss ts)
    else [(Term.Fun f ss, Term.Fun g ts)]);
rd_impl uu (Term.Var v, t) = [(Term.Var v, t)];
rd_impl uu (s, Term.Var v) = [(s, Term.Var v)];

nonreach ::
  forall a b c.
    (Eq a) => (Term.Term a b -> Term.Term a c -> Bool) ->
                Term.Term a b -> Term.Term a c -> Bool;
nonreach gt s t =
  (case (s, t) of {
    (Term.Var _, _) -> False;
    (Term.Fun _ _, Term.Var _) -> False;
    (Term.Fun f ss, Term.Fun g ts) ->
      not ((f, List.size_list ss) == (g, List.size_list ts)) && not (gt s t);
  });

group_key :: forall a b. (Eq b) => (a -> b) -> [a] -> [[a]];
group_key f [] = [];
group_key f (x : xs) =
  (x : takeWhile (\ y -> f x == f y) xs) :
    group_key f (dropWhile (\ y -> f x == f y) xs);

mk_gt_fun ::
  forall a b c.
    (Eq a) => [(Term.Term a b, Term.Term a c)] ->
                Maybe (a, Arith.Nat) -> Maybe (a, Arith.Nat) -> Bool;
mk_gt_fun rs =
  let {
    in_trancl = Transitive_Closure_List_Impl.memo_list_trancl (gt1 rs);
  } in (\ f -> List.member (in_trancl f));

nonlinear_var_nonreach ::
  forall a b c d.
    (Collection_Enum.Cenum a, Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Eq a, Set_Impl.Set_impl a, Compare.Compare b, Eq b, Compare.Compare c,
      Eq c) => [(a, Arith.Nat)] ->
                 (Maybe (a, Arith.Nat) -> Maybe (a, Arith.Nat) -> Bool) ->
                   [(Term.Term b c, Term.Term a d)] -> Bool;
nonlinear_var_nonreach f gt_fun xs =
  let {
    xs1 = filter (Term.is_Var . fst) xs;
    xs2 = List.sort_key fst xs1;
    a = group_key fst xs2;
  } in any (\ xts ->
             Arith.less_nat Arith.one_nat (List.size_list xts) &&
               all (\ fa ->
                     not (gt_fun (Just fa) Nothing) &&
                       any (\ (_, v) ->
                             not (Term.is_Var v) &&
                               Set.less_eq_set
                                 (Subterm_and_Context.funas_term v)
                                 (List.set f) &&
                                 not (Term.root v == Just fa) &&
                                   not (gt_fun (Just fa) (Term.root v)))
                         xts)
                 f)
         a;

nonreachable_gtcapRM ::
  forall a b c.
    (Collection_Enum.Cenum a, Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Compare.Compare a, Eq a, Set_Impl.Set_impl a, Compare.Compare b,
      Eq b) => [(a, Arith.Nat)] ->
                 Bool ->
                   Bool ->
                     (Maybe (a, Arith.Nat) -> Maybe (a, Arith.Nat) -> Bool) ->
                       ((a, Arith.Nat) -> [(Term.Term a b, Term.Term a b)]) ->
                         Term.Term a b -> Term.Term a c -> Bool;
nonreachable_gtcapRM fs nlv ne gt_fun rm s t =
  let {
    gt = gt_term nlv ne gt_fun rm;
    rs = rd_impl gt (s, t);
  } in any (\ (a, b) -> nonreach gt a b) rs ||
         nlv && ne && nonlinear_var_nonreach fs gt_fun rs;

}
