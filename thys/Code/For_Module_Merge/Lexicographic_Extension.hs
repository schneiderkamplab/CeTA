{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Lexicographic_Extension(lex_ext_unbounded, lex_ext) where {

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
import qualified List;
import qualified HOL;
import qualified Arith;

lex_ext_unbounded ::
  forall a. (a -> a -> (Bool, Bool)) -> [a] -> [a] -> (Bool, Bool);
lex_ext_unbounded f [] [] = (False, True);
lex_ext_unbounded f (uu : uv) [] = (True, True);
lex_ext_unbounded f [] (uw : ux) = (False, False);
lex_ext_unbounded f (a : asa) (b : bs) =
  (case f a b of {
    (True, _) -> (True, True);
    (False, True) -> lex_ext_unbounded f asa bs;
    (False, False) -> (False, False);
  });

lex_ext ::
  forall a. (a -> a -> (Bool, Bool)) -> Arith.Nat -> [a] -> [a] -> (Bool, Bool);
lex_ext f n ss ts =
  let {
    lts = List.size_list ts;
  } in (if Arith.equal_nat (List.size_list ss) lts || Arith.less_eq_nat lts n
         then lex_ext_unbounded f ss ts else (False, False));

}
