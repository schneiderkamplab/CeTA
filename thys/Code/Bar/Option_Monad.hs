{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Option_Monad(mapM, guard, zip_option) where {

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

mapM :: forall a b. (a -> Maybe b) -> [a] -> Maybe [b];
mapM f [] = Just [];
mapM f (x : xs) =
  Arith.bind (f x) (\ y -> Arith.bind (mapM f xs) (\ ys -> Just (y : ys)));

guard :: Bool -> Maybe ();
guard b = (if b then Just () else Nothing);

zip_option :: forall a b. [a] -> [b] -> Maybe [(a, b)];
zip_option [] [] = Just [];
zip_option (x : xs) (y : ys) =
  Arith.bind (zip_option xs ys) (\ zs -> Just ((x, y) : zs));
zip_option (x : xs) [] = Nothing;
zip_option [] (y : ys) = Nothing;

}
