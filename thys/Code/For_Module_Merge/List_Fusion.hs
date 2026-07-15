{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  List_Fusion(Generator(..), next, has_next, fold_fusion, length_fusion,
               list_all_fusion, list_all2_fusion)
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
import qualified Arith;
import qualified Product_Type;
import qualified HOL;

newtype Generator a b = Generator (b -> Bool, b -> (a, b));

generator :: forall a b. Generator a b -> (b -> Bool, b -> (a, b));
generator (Generator x) = x;

next :: forall a b. Generator a b -> b -> (a, b);
next g = snd (generator g);

has_next :: forall a b. Generator a b -> b -> Bool;
has_next g = fst (generator g);

fold_fusion :: forall a b c. Generator a b -> (a -> c -> c) -> b -> c -> c;
fold_fusion g f s b =
  (if has_next g s then (case next g s of {
                          (x, sa) -> fold_fusion g f sa (f x b);
                        })
    else b);

gen_length_fusion :: forall a b. Generator a b -> Arith.Nat -> b -> Arith.Nat;
gen_length_fusion g n s =
  (if has_next g s then gen_length_fusion g (Arith.suc n) (snd (next g s))
    else n);

length_fusion :: forall a b. Generator a b -> b -> Arith.Nat;
length_fusion g = gen_length_fusion g Arith.zero_nat;

list_all_fusion :: forall a b. Generator a b -> (a -> Bool) -> b -> Bool;
list_all_fusion g p s =
  (if has_next g s then (case next g s of {
                          (x, sa) -> p x && list_all_fusion g p sa;
                        })
    else True);

list_all2_fusion ::
  forall a b c d.
    (a -> b -> Bool) -> Generator a c -> Generator b d -> c -> d -> Bool;
list_all2_fusion p g1 g2 s1 s2 =
  (if has_next g1 s1
    then has_next g2 s2 &&
           (case next g1 s1 of {
             (x, s1a) ->
               (case next g2 s2 of {
                 (y, s2a) -> p x y && list_all2_fusion p g1 g2 s1a s2a;
               });
           })
    else not (has_next g2 s2));

}
