{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Position(is_left_of, showsl_pos, proper_prefix_list, prefix_list,
            remove_prefix, remove_suffix, bounded_postfixes)
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
import qualified Shows_Literal;
import qualified Arith;

one_list :: forall a. [a];
one_list = [];

instance Arith.One [a] where {
  one = one_list;
};

times_list :: forall a. [a] -> [a] -> [a];
times_list p q = p ++ q;

instance Arith.Times [a] where {
  times = times_list;
};

instance Arith.Power [a] where {
};

is_left_of :: [Arith.Nat] -> [Arith.Nat] -> Bool;
is_left_of [] q = False;
is_left_of (i : p) q =
  (case q of {
    [] -> False;
    j : qa ->
      (if Arith.less_nat i j then True
        else (if Arith.less_nat j i then False else is_left_of p qa));
  });

showsl_pos :: [Arith.Nat] -> String -> String;
showsl_pos =
  Shows_Literal.showsl_list_gen (\ i -> Shows_Literal.showsl_nat (Arith.suc i))
    "empty" "" "." "";

proper_prefix_list :: [Arith.Nat] -> [[Arith.Nat]];
proper_prefix_list [] = [];
proper_prefix_list (i : p) = [] : map (\ a -> i : a) (proper_prefix_list p);

prefix_list :: [Arith.Nat] -> [[Arith.Nat]];
prefix_list p = p : proper_prefix_list p;

remove_prefix :: forall a. (Eq a) => [a] -> [a] -> Maybe [a];
remove_prefix [] ys = Just ys;
remove_prefix (x : xs) (y : ys) =
  (if x == y then remove_prefix xs ys else Nothing);
remove_prefix (v : va) [] = Nothing;

remove_suffix :: forall a. (Eq a) => [a] -> [a] -> Maybe [a];
remove_suffix p q = (case remove_prefix (reverse p) (reverse q) of {
                      Nothing -> Nothing;
                      Just r -> Just (reverse r);
                    });

bounded_postfixes :: [Arith.Nat] -> [[Arith.Nat]] -> [[Arith.Nat]];
bounded_postfixes p ps =
  Arith.map_filter
    (\ x -> (if not (Arith.is_none x) then Just (Arith.the x) else Nothing))
    (map (remove_prefix p) ps);

}
