{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Autoref_Bindings_HOL(is_Nil, is_None, list_eq, prod_eq) where {

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

is_Nil :: forall a. [a] -> Bool;
is_Nil a = (case a of {
             [] -> True;
             _ : _ -> False;
           });

is_None :: forall a. Maybe a -> Bool;
is_None a = (case a of {
              Nothing -> True;
              Just _ -> False;
            });

list_eq :: forall a. (a -> a -> Bool) -> [a] -> [a] -> Bool;
list_eq eq [] [] = True;
list_eq eq (aa : la) (a : l) = (if eq aa a then list_eq eq la l else False);
list_eq uu (v : va) [] = False;
list_eq uu [] (v : va) = False;

prod_eq ::
  forall a b c d.
    (a -> b -> Bool) -> (c -> d -> Bool) -> (a, c) -> (b, d) -> Bool;
prod_eq eqa eqb x1 x2 = (case x1 of {
                          (a1, b1) -> (case x2 of {
(a2, b2) -> eqa a1 a2 && eqb b1 b2;
                                      });
                        });

}
