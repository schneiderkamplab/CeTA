{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Efficient_Sort(msort_key) where {

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
import qualified Orderings;

asc ::
  forall a b.
    (Orderings.Linorder b) => (a -> b) -> a -> ([a] -> [a]) -> [a] -> [[a]];
asc key a asa (b : bs) =
  (if Orderings.less_eq (key a) (key b) then asc key b (\ ys -> asa (a : ys)) bs
    else asa [a] : sequences key (b : bs));
asc key a asa [] = [asa [a]];

sequences :: forall a b. (Orderings.Linorder b) => (a -> b) -> [a] -> [[a]];
sequences key (a : b : xs) =
  (if Orderings.less (key b) (key a) then desc key b [a] xs
    else asc key b (\ ba -> a : ba) xs);
sequences key [x] = [[x]];
sequences key [] = [];

desc ::
  forall a b. (Orderings.Linorder b) => (a -> b) -> a -> [a] -> [a] -> [[a]];
desc key a asa (b : bs) =
  (if Orderings.less (key b) (key a) then desc key b (a : asa) bs
    else (a : asa) : sequences key (b : bs));
desc key a asa [] = [a : asa];

merge :: forall a b. (Orderings.Linorder b) => (a -> b) -> [a] -> [a] -> [a];
merge key (a : asa) (b : bs) =
  (if Orderings.less (key b) (key a) then b : merge key (a : asa) bs
    else a : merge key asa (b : bs));
merge key [] bs = bs;
merge key (v : va) [] = v : va;

merge_pairs :: forall a b. (Orderings.Linorder b) => (a -> b) -> [[a]] -> [[a]];
merge_pairs key (a : b : xs) = merge key a b : merge_pairs key xs;
merge_pairs key [] = [];
merge_pairs key [v] = [v];

merge_all :: forall a b. (Orderings.Linorder b) => (a -> b) -> [[a]] -> [a];
merge_all key [] = [];
merge_all key [x] = x;
merge_all key (v : vb : vc) = merge_all key (merge_pairs key (v : vb : vc));

msort_key :: forall a b. (Orderings.Linorder b) => (a -> b) -> [a] -> [a];
msort_key key xs = merge_all key (sequences key xs);

}
