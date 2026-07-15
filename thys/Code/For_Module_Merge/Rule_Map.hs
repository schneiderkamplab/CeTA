{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Rule_Map(rules_with, delete_rules, insert_rules, intersect_rules) where {

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
import qualified Compare_Order_Instances;
import qualified Compare_Instances;
import qualified Multimap;
import qualified RBT;
import qualified Orderings;
import qualified Product_Lexorder;
import qualified List;
import qualified Term;
import qualified Arith;

key ::
  forall a b c. (a, (Term.Term b c, Term.Term b c)) -> Maybe (b, Arith.Nat);
key (uu, (Term.Fun f ts, uv)) = Just (f, List.size_list ts);
key (uw, (Term.Var ux, uy)) = Nothing;

rules_with ::
  forall a b c.
    (Orderings.Linorder b) => (a -> Bool) ->
                                RBT.Rbt (b, Arith.Nat)
                                  [(a, (Term.Term b c, Term.Term b c))] ->
                                  [(Term.Term b c, Term.Term b c)];
rules_with p m =
  List.map_filter (\ x -> (if (p . fst) x then Just (snd x) else Nothing))
    (Multimap.values m);

delete_rules ::
  forall a b c.
    (Eq a, Compare.Compare_order b, Eq b,
      Eq c) => a -> [(Term.Term b c, Term.Term b c)] ->
                      RBT.Rbt (b, Arith.Nat)
                        [(a, (Term.Term b c, Term.Term b c))] ->
                        RBT.Rbt (b, Arith.Nat)
                          [(a, (Term.Term b c, Term.Term b c))];
delete_rules a rs = Multimap.delete_values key (map (\ b -> (a, b)) rs);

insert_rules ::
  forall a b c.
    (Eq a, Compare.Compare_order b, Eq b,
      Eq c) => a -> [(Term.Term b c, Term.Term b c)] ->
                      RBT.Rbt (b, Arith.Nat)
                        [(a, (Term.Term b c, Term.Term b c))] ->
                        RBT.Rbt (b, Arith.Nat)
                          [(a, (Term.Term b c, Term.Term b c))];
insert_rules a rs = Multimap.insert_values key (map (\ b -> (a, b)) rs);

intersect_rules ::
  forall a b.
    (Compare.Compare_order a, Eq a,
      Eq b) => [(Term.Term a b, Term.Term a b)] ->
                 RBT.Rbt (a, Arith.Nat)
                   [(Bool, (Term.Term a b, Term.Term a b))] ->
                   RBT.Rbt (a, Arith.Nat)
                     [(Bool, (Term.Term a b, Term.Term a b))];
intersect_rules rs =
  Multimap.intersect_values key
    (map (\ a -> (True, a)) rs ++ map (\ a -> (False, a)) rs);

}
