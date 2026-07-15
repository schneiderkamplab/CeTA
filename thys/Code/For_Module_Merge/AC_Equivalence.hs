{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module AC_Equivalence(Acterm, equal_acterm, actop, aocnf) where {

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
import qualified HOL;
import qualified Set;
import qualified Collection_Order;
import qualified Collection_Eq;
import qualified Term;
import qualified Multiset;

data Acterm a b = AVar b | AFun a [Acterm a b]
  | AAC a (Multiset.Multiset (Acterm a b));

instance (Eq a, Eq b) => Eq (Acterm a b) where {
  a == b = equal_acterm a b;
};

equal_acterm :: forall a b. (Eq a, Eq b) => Acterm a b -> Acterm a b -> Bool;
equal_acterm (AFun x21 x22) (AAC x31 x32) = False;
equal_acterm (AAC x31 x32) (AFun x21 x22) = False;
equal_acterm (AVar x1) (AAC x31 x32) = False;
equal_acterm (AAC x31 x32) (AVar x1) = False;
equal_acterm (AVar x1) (AFun x21 x22) = False;
equal_acterm (AFun x21 x22) (AVar x1) = False;
equal_acterm (AAC x31 x32) (AAC y31 y32) =
  x31 == y31 && Multiset.equal_multiset x32 y32;
equal_acterm (AFun x21 x22) (AFun y21 y22) = x21 == y21 && x22 == y22;
equal_acterm (AVar x1) (AVar y1) = x1 == y1;

aABin :: forall a b. (Eq a) => a -> Acterm a b -> Acterm a b -> Acterm a b;
aABin f (AFun g [s, t]) u =
  (if f == g then AFun f [s, aABin f t u] else AFun f [AFun g [s, t], u]);
aABin f (AVar v) t = AFun f [AVar v, t];
aABin f (AFun v []) t = AFun f [AFun v [], t];
aABin f (AFun v [vb]) t = AFun f [AFun v [vb], t];
aABin f (AFun v (vb : vd : vf : vg)) t = AFun f [AFun v (vb : vd : vf : vg), t];
aABin f (AAC v va) t = AFun f [AAC v va, t];

actop ::
  forall a b.
    (Eq a, Eq b) => a -> Term.Term a b -> Multiset.Multiset (Term.Term a b);
actop f (Term.Fun g [s, t]) =
  (if f == g then Multiset.plus_multiset (actop f s) (actop f t)
    else Multiset.add_mset (Term.Fun g [s, t]) Multiset.zero_multiset);
actop f (Term.Var v) = Multiset.add_mset (Term.Var v) Multiset.zero_multiset;
actop f (Term.Fun v []) =
  Multiset.add_mset (Term.Fun v []) Multiset.zero_multiset;
actop f (Term.Fun v [vb]) =
  Multiset.add_mset (Term.Fun v [vb]) Multiset.zero_multiset;
actop f (Term.Fun v (vb : vd : vf : vg)) =
  Multiset.add_mset (Term.Fun v (vb : vd : vf : vg)) Multiset.zero_multiset;

aocnf ::
  forall a b.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Eq a,
      Eq b) => Set.Set a -> Set.Set a -> Term.Term a b -> Acterm a b;
aocnf f_A f_C (Term.Var x) = AVar x;
aocnf f_A f_C (Term.Fun f [s, t]) =
  let {
    a = Set.member f f_A;
    c = Set.member f f_C;
  } in (if a && c
         then AAC f (Multiset.image_mset (aocnf f_A f_C)
                      (actop f (Term.Fun f [s, t])))
         else (if a then aABin f (aocnf f_A f_C s) (aocnf f_A f_C t)
                else (if c then AAC f (Multiset.add_mset (aocnf f_A f_C s)
(Multiset.add_mset (aocnf f_A f_C t) Multiset.zero_multiset))
                       else AFun f [aocnf f_A f_C s, aocnf f_A f_C t])));
aocnf f_A f_C (Term.Fun f []) = AFun f [];
aocnf f_A f_C (Term.Fun f [t]) = AFun f [aocnf f_A f_C t];
aocnf f_A f_C (Term.Fun f (s : t : u : us)) =
  AFun f
    (aocnf f_A f_C s :
      aocnf f_A f_C t : aocnf f_A f_C u : map (aocnf f_A f_C) us);

}
