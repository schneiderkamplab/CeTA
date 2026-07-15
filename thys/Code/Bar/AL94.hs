{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module AL94(skol) where {

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
import qualified Sum_Type;
import qualified Term_Rewriting;
import qualified Arith;

skol ::
  forall a b.
    (Arith.Ceq a,
      Arith.Ccompare a) => Arith.Set a ->
                             Term_Rewriting.Term b a ->
                               Term_Rewriting.Term (Sum_Type.Sum b a) a;
skol v (Term_Rewriting.Var x) =
  (if Arith.member x v then Term_Rewriting.Fun (Sum_Type.Inr x) []
    else Term_Rewriting.Var x);
skol v (Term_Rewriting.Fun f ts) =
  Term_Rewriting.Fun (Sum_Type.Inl f) (map (skol v) ts);

}
