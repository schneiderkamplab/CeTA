{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Ground_Context_Impl(merge, match, gc_matcher, showsl_gctxt, compare_gctxt)
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
import qualified Compare;
import qualified Shows_Literal;
import qualified HOL;
import qualified Compare_Instances;
import qualified Comparator;
import qualified Option_Monad;
import qualified Show_Instances;
import qualified Unification_String;
import qualified Str;
import qualified Product_Type;
import qualified List;
import qualified Arith;
import qualified Option;
import qualified Ground_Context;
import qualified Term;

match_list ::
  forall a b.
    (Eq a) => [(Ground_Context.Gctxt a b, Term.Term a b)] ->
                Maybe [(Ground_Context.Gctxt a b, b)];
match_list [] = Just [];
match_list ((Ground_Context.GCHole, t) : ps) = match_list ps;
match_list ((Ground_Context.GCFun f ss, Term.Fun g ts) : ps) =
  Option.bind (Option_Monad.guard (f == g))
    (\ _ ->
      Option.bind (Option_Monad.zip_option ss ts)
        (\ psa -> match_list (psa ++ ps)));
match_list ((Ground_Context.GCFun f ss, Term.Var x) : ps) =
  Option.bind (match_list ps)
    (\ psa -> Just ((Ground_Context.GCFun f ss, x) : psa));

merge_lists ::
  forall a b.
    (Eq a) => [Ground_Context.Gctxt a b] ->
                [Ground_Context.Gctxt a b] -> Maybe [Ground_Context.Gctxt a b];
merge_lists [] [] = Just [];
merge_lists (Ground_Context.GCHole : cs) (d : ds) =
  Option.bind (merge_lists cs ds) (\ es -> Just (d : es));
merge_lists (c : cs) (Ground_Context.GCHole : ds) =
  Option.bind (merge_lists cs ds) (\ es -> Just (c : es));
merge_lists (Ground_Context.GCFun f ss : cs) (Ground_Context.GCFun g ts : ds) =
  Option.bind (Option_Monad.guard (f == g))
    (\ _ ->
      Option.bind (merge_lists ss ts)
        (\ us ->
          Option.bind (merge_lists cs ds)
            (\ es -> Just (Ground_Context.GCFun f us : es))));
merge_lists [] (d : ds) = Nothing;
merge_lists (c : cs) [] = Nothing;

merge ::
  forall a b.
    (Eq a) => Ground_Context.Gctxt a b ->
                Ground_Context.Gctxt a b -> Maybe (Ground_Context.Gctxt a b);
merge c d =
  Option.bind (merge_lists [c] [d]) (\ es -> Just (List.nth es Arith.zero_nat));

merge_var ::
  forall a b.
    (Eq a,
      Eq b) => a -> Ground_Context.Gctxt b a ->
                      [(Ground_Context.Gctxt b a, a)] ->
                        Maybe ((Ground_Context.Gctxt b a, a),
                                [(Ground_Context.Gctxt b a, a)]);
merge_var x c [] = Just ((c, x), []);
merge_var x c ((d, y) : ps) =
  (if x == y then Option.bind (merge c d) (\ e -> merge_var x e ps)
    else Option.bind (merge_var x c ps) (\ (b, psa) -> Just (b, (d, y) : psa)));

merge_all ::
  forall a b.
    (Eq a,
      Eq b) => [(Ground_Context.Gctxt a b, b)] ->
                 Maybe [(Ground_Context.Gctxt a b, b)];
merge_all [] = Just [];
merge_all ((c, x) : ps) =
  Option.bind (merge_var x c ps)
    (\ (cx, psa) -> Option.bind (merge_all psa) (\ psb -> Just (cx : psb)));

match ::
  forall a b.
    (Eq a,
      Eq b) => (Ground_Context.Gctxt a b, Term.Term a b) ->
                 Maybe [(Ground_Context.Gctxt a b, b)];
match (c, t) = Option.bind (match_list [(c, t)]) merge_all;

gctxts_to_terms_intern ::
  forall a b.
    (Arith.Nat -> a) ->
      Arith.Nat -> [Ground_Context.Gctxt b a] -> (Arith.Nat, [Term.Term b a]);
gctxts_to_terms_intern iv i (Ground_Context.GCFun f ts : cs) =
  (case gctxts_to_terms_intern iv i ts of {
    (i1, res1) -> (case gctxts_to_terms_intern iv i1 cs of {
                    (i2, res2) -> (i2, Term.Fun f res1 : res2);
                  });
  });
gctxts_to_terms_intern iv i (Ground_Context.GCHole : cs) =
  (case gctxts_to_terms_intern iv (Arith.plus_nat i Arith.one_nat) cs of {
    (ia, res) -> (ia, Term.Var (iv i) : res);
  });
gctxts_to_terms_intern iv i [] = (i, []);

gc_matcher ::
  forall a.
    (Eq a) => Ground_Context.Gctxt a [Str.Char] ->
                Term.Term a [Str.Char] ->
                  Maybe ([Str.Char] -> Term.Term a [Str.Char]);
gc_matcher c l =
  Option.map_option fst
    (Unification_String.mgu_vd_string l
      (List.hd
        (snd (gctxts_to_terms_intern
               (\ i ->
                 Str.char_0x78 :
                   Show_Instances.shows_prec_nat Arith.zero_nat i [])
               Arith.zero_nat [c]))));

comparator_gctxt ::
  forall a b.
    (a -> a -> Comparator.Order) ->
      Ground_Context.Gctxt a b -> Ground_Context.Gctxt a b -> Comparator.Order;
comparator_gctxt comp_f Ground_Context.GCHole Ground_Context.GCHole =
  Comparator.Eqa;
comparator_gctxt comp_f Ground_Context.GCHole (Ground_Context.GCFun y ya) =
  Comparator.Lt;
comparator_gctxt comp_f (Ground_Context.GCFun x xa) Ground_Context.GCHole =
  Comparator.Gt;
comparator_gctxt comp_f (Ground_Context.GCFun x xa) (Ground_Context.GCFun y ya)
  = (case comp_f x y of {
      Comparator.Eqa ->
        Compare_Instances.comparator_list (comparator_gctxt comp_f) xa ya;
      Comparator.Lt -> Comparator.Lt;
      Comparator.Gt -> Comparator.Gt;
    });

showsl_gctxt ::
  forall a b.
    (Shows_Literal.Showl a) => Ground_Context.Gctxt a b -> String -> String;
showsl_gctxt Ground_Context.GCHole = Shows_Literal.showsl_literal "_";
showsl_gctxt (Ground_Context.GCFun f ts) =
  Shows_Literal.showsl f .
    Shows_Literal.showsl_list_gen id "" "(" ", " ")" (map showsl_gctxt ts);

compare_gctxt ::
  forall a b.
    (Compare.Compare a) => Ground_Context.Gctxt a b ->
                             Ground_Context.Gctxt a b -> Comparator.Order;
compare_gctxt = comparator_gctxt Compare.compare;

}
