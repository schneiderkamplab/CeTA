{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Pointwise_Extension(pointwise_ext) where {

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
import qualified Product_Type;
import qualified HOL;

pointwise_ext ::
  forall a. (a -> a -> (Bool, Bool)) -> [a] -> [a] -> (Bool, Bool);
pointwise_ext f [] [] = (False, True);
pointwise_ext f (uu : uv) [] = (False, False);
pointwise_ext f [] (uw : ux) = (False, False);
pointwise_ext f (a : asa) (b : bs) =
  (case f a b of {
    (stri, True) -> (case pointwise_ext f asa bs of {
                      (strir, True) -> (stri || strir, True);
                      (_, False) -> (False, False);
                    });
    (_, False) -> (False, False);
  });

}
