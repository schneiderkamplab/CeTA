{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Shows_Literal_Matrix(showsl_mat) where {

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
import qualified Matrix;
import qualified Shows_Literal;

showsl_mat ::
  forall a. (Shows_Literal.Showl a) => Matrix.Mat a -> String -> String;
showsl_mat a =
  Shows_Literal.default_showsl_list id
    (map Shows_Literal.showsl_list (Matrix.mat_to_list a));

showsl_list_mat ::
  forall a. (Shows_Literal.Showl a) => [Matrix.Mat a] -> String -> String;
showsl_list_mat xs = Shows_Literal.default_showsl_list showsl_mat xs;

instance (Shows_Literal.Showl a) => Shows_Literal.Showl (Matrix.Mat a) where {
  showsl = showsl_mat;
  showsl_list = showsl_list_mat;
};

}
