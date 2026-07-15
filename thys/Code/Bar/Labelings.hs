{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Labelings(Lab(..), equal_lab, label, gen_label, label_depth, label_decomp)
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
import qualified Sum_Type;
import qualified Arith;

data Lab a b = Lab (Lab a b) b | FunLab (Lab a b) [Lab a b] | UnLab a
  | Sharp (Lab a b);

instance (Eq a, Eq b) => Eq (Lab a b) where {
  a == b = equal_lab a b;
};

equal_lab :: forall a b. (Eq a, Eq b) => Lab a b -> Lab a b -> Bool;
equal_lab (UnLab x3) (Sharp x4) = False;
equal_lab (Sharp x4) (UnLab x3) = False;
equal_lab (FunLab x21 x22) (Sharp x4) = False;
equal_lab (Sharp x4) (FunLab x21 x22) = False;
equal_lab (FunLab x21 x22) (UnLab x3) = False;
equal_lab (UnLab x3) (FunLab x21 x22) = False;
equal_lab (Lab x11 x12) (Sharp x4) = False;
equal_lab (Sharp x4) (Lab x11 x12) = False;
equal_lab (Lab x11 x12) (UnLab x3) = False;
equal_lab (UnLab x3) (Lab x11 x12) = False;
equal_lab (Lab x11 x12) (FunLab x21 x22) = False;
equal_lab (FunLab x21 x22) (Lab x11 x12) = False;
equal_lab (Sharp x4) (Sharp y4) = equal_lab x4 y4;
equal_lab (UnLab x3) (UnLab y3) = x3 == y3;
equal_lab (FunLab x21 x22) (FunLab y21 y22) = equal_lab x21 y21 && x22 == y22;
equal_lab (Lab x11 x12) (Lab y11 y12) = equal_lab x11 y11 && x12 == y12;

label ::
  forall a b. Lab a b -> Arith.Nat -> Sum_Type.Sum b [Lab a b] -> Lab a b;
label f n (Sum_Type.Inl l) = Lab f l;
label f n (Sum_Type.Inr l) = FunLab f l;

gen_label :: forall a b. Lab a b -> Arith.Nat -> Lab a b;
gen_label f n =
  (if Arith.equal_nat n Arith.zero_nat then f
    else FunLab (gen_label f (Arith.minus_nat n Arith.one_nat)) []);

label_depth :: forall a b. Lab a b -> Arith.Nat;
label_depth (UnLab uu) = Arith.zero_nat;
label_depth (Lab f uv) = Arith.suc (label_depth f);
label_depth (FunLab f uw) = Arith.suc (label_depth f);
label_depth (Sharp f) = Arith.suc (label_depth f);

label_decomp :: forall a b. Lab a b -> (Lab a b, Sum_Type.Sum b [Lab a b]);
label_decomp (Lab f l) = (f, Sum_Type.Inl l);
label_decomp (FunLab f l) = (f, Sum_Type.Inr l);

}
