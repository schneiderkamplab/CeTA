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
import qualified Term;
import qualified Set;
import qualified Collection_Order;
import qualified Collection_Eq;

skol ::
  forall a b.
    (Collection_Eq.Ceq a,
      Collection_Order.Ccompare a) => Set.Set a ->
Term.Term b a -> Term.Term (Sum_Type.Sum b a) a;
skol v (Term.Var x) =
  (if Set.member x v then Term.Fun (Sum_Type.Inr x) [] else Term.Var x);
skol v (Term.Fun f ts) = Term.Fun (Sum_Type.Inl f) (map (skol v) ts);

}
