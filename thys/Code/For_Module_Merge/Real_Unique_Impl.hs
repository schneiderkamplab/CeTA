{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Real_Unique_Impl(Mini_alg_unique, real_lt, mau_ge_0, mau_plus, mau_sqrt,
                    mau_coeff, mau_equal, mau_floor, mau_times, mau_of_rat,
                    mau_uminus, mau_inverse, mau_show_real, mau_compatible)
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
import qualified Show_Instances;
import qualified Str;
import qualified Showa;
import qualified Prime_Product;
import qualified Product_Type;
import qualified HOL;
import qualified Real;
import qualified Rat;
import qualified Arith;
import qualified Real_Impl;

newtype Mini_alg_unique = Abs_mini_alg_unique Real_Impl.Mini_alg;

real_lt :: Real.Real -> Real.Real -> Bool;
real_lt x y =
  let {
    fx = Real.floor_real x;
    fy = Real.floor_real y;
  } in (if Arith.less_int fx fy then True
         else (if Arith.less_int fy fx then False
                else real_lt
                       (Real.times_real x
                         (Real.ratreal
                           (Rat.of_int
                             (Arith.Int_of_integer (1024 :: Integer)))))
                       (Real.times_real y
                         (Real.ratreal
                           (Rat.of_int
                             (Arith.Int_of_integer (1024 :: Integer)))))));

rep_mini_alg_unique :: Mini_alg_unique -> Real_Impl.Mini_alg;
rep_mini_alg_unique (Abs_mini_alg_unique x) = x;

mau_ge_0 :: Mini_alg_unique -> Bool;
mau_ge_0 xa = Real_Impl.ma_ge_0 (rep_mini_alg_unique xa);

mau_plus :: Mini_alg_unique -> Mini_alg_unique -> Mini_alg_unique;
mau_plus xb xc =
  Abs_mini_alg_unique
    (Real_Impl.ma_plus (rep_mini_alg_unique xb) (rep_mini_alg_unique xc));

mau_sqrt :: Mini_alg_unique -> Mini_alg_unique;
mau_sqrt xa =
  Abs_mini_alg_unique
    (case Rat.quotient_of (Real_Impl.ma_rat (rep_mini_alg_unique xa)) of {
      (a, b) ->
        (case Prime_Product.prime_product_factor
                (Arith.nat (Arith.times_int (Arith.abs_int a) b))
          of {
          (sq, fact) ->
            let {
              ma = Real_Impl.ma_of_rat
                     (Rat.divide_rat
                       (Rat.times_rat (Rat.of_int (Arith.sgn_int a))
                         (Arith.of_nat sq))
                       (Rat.of_int b));
            } in Real_Impl.ma_times ma
                   (Real_Impl.ma_sqrt
                     (Real_Impl.ma_of_rat (Arith.of_nat fact)));
        });
    });

mau_coeff :: Mini_alg_unique -> Rat.Rat;
mau_coeff xa = Real_Impl.ma_coeff (rep_mini_alg_unique xa);

ma_identity :: Real_Impl.Mini_alg -> Real_Impl.Mini_alg -> Bool;
ma_identity xa xc = Real_Impl.rep_mini_alg xa == Real_Impl.rep_mini_alg xc;

mau_equal :: Mini_alg_unique -> Mini_alg_unique -> Bool;
mau_equal xa xc = ma_identity (rep_mini_alg_unique xa) (rep_mini_alg_unique xc);

mau_floor :: Mini_alg_unique -> Arith.Int;
mau_floor xa = Real_Impl.ma_floor (rep_mini_alg_unique xa);

mau_times :: Mini_alg_unique -> Mini_alg_unique -> Mini_alg_unique;
mau_times xb xc =
  Abs_mini_alg_unique
    (Real_Impl.ma_times (rep_mini_alg_unique xb) (rep_mini_alg_unique xc));

mau_of_rat :: Rat.Rat -> Mini_alg_unique;
mau_of_rat xa = Abs_mini_alg_unique (Real_Impl.ma_of_rat xa);

mau_uminus :: Mini_alg_unique -> Mini_alg_unique;
mau_uminus xa =
  Abs_mini_alg_unique (Real_Impl.ma_uminus (rep_mini_alg_unique xa));

mau_inverse :: Mini_alg_unique -> Mini_alg_unique;
mau_inverse xa =
  Abs_mini_alg_unique (Real_Impl.ma_inverse (rep_mini_alg_unique xa));

ma_show_real :: Real_Impl.Mini_alg -> [Str.Char];
ma_show_real xa =
  (case Real_Impl.rep_mini_alg xa of {
    (p, (q, b)) ->
      let {
        sb = (Showa.shows_prec_list Arith.zero_nat
                [Str.char_0x73, Str.char_0x71, Str.char_0x72, Str.char_0x74,
                  Str.char_0x28] .
               Show_Instances.shows_prec_nat Arith.zero_nat b) .
               Showa.shows_prec_list Arith.zero_nat [Str.char_0x29];
        qb = (if Rat.equal_rat q Rat.one_rat then sb
               else (if Rat.equal_rat q (Rat.uminus_rat Rat.one_rat)
                      then Showa.shows_prec_list Arith.zero_nat
                             [Str.char_0x2D] .
                             sb
                      else (Show_Instances.shows_prec_rat Arith.zero_nat q .
                             Showa.shows_prec_list Arith.zero_nat
                               [Str.char_0x2A]) .
                             sb));
      } in (if Rat.equal_rat q Rat.zero_rat
             then Show_Instances.shows_prec_rat Arith.zero_nat p []
             else (if Rat.equal_rat p Rat.zero_rat then qb []
                    else (if Rat.less_rat q Rat.zero_rat
                           then Show_Instances.shows_prec_rat Arith.zero_nat p
                                  (qb [])
                           else Show_Instances.shows_prec_rat Arith.zero_nat p
                                  (Showa.shows_prec_list Arith.zero_nat
                                    [Str.char_0x2B] (qb [])))));
  });

mau_show_real :: Mini_alg_unique -> [Str.Char];
mau_show_real xa = ma_show_real (rep_mini_alg_unique xa);

mau_compatible :: Mini_alg_unique -> Mini_alg_unique -> Bool;
mau_compatible xa xc =
  Real_Impl.ma_compatible (rep_mini_alg_unique xa) (rep_mini_alg_unique xc);

}
