{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Real_Impl(Mini_alg, ge_0, rep_mini_alg, ma_rat, ma_ge_0, ma_plus, ma_sqrt,
             ma_coeff, ma_floor, ma_times, ma_of_rat, ma_uminus, ma_inverse,
             ma_compatible)
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
import qualified Sqrt_Babylonian;
import qualified List;
import qualified Product_Type;
import qualified HOL;
import qualified Real_Unique_Impl;
import qualified Real;
import qualified Rat;
import qualified Arith;

newtype Mini_alg = Abs_mini_alg (Rat.Rat, (Rat.Rat, Arith.Nat));

ge_0 :: Real.Real -> Bool;
ge_0 (Real.Real_of_u x) = Real_Unique_Impl.mau_ge_0 x;

rep_mini_alg :: Mini_alg -> (Rat.Rat, (Rat.Rat, Arith.Nat));
rep_mini_alg (Abs_mini_alg x) = x;

ma_rat :: Mini_alg -> Rat.Rat;
ma_rat xa = fst (rep_mini_alg xa);

ma_ge_0 :: Mini_alg -> Bool;
ma_ge_0 xa =
  (case rep_mini_alg xa of {
    (p, (q, b)) ->
      let {
        bqq = Rat.times_rat (Rat.times_rat (Arith.of_nat b) q) q;
        pp = Rat.times_rat p p;
      } in Rat.less_eq_rat Rat.zero_rat p && Rat.less_eq_rat bqq pp ||
             Rat.less_eq_rat Rat.zero_rat q && Rat.less_eq_rat pp bqq;
  });

ma_normalize ::
  (Rat.Rat, (Rat.Rat, Arith.Nat)) -> (Rat.Rat, (Rat.Rat, Arith.Nat));
ma_normalize x =
  (case x of {
    (a, (b, c)) ->
      (if Rat.equal_rat b Rat.zero_rat then (a, (Rat.zero_rat, Arith.zero_nat))
        else (a, (b, c)));
  });

ma_plus :: Mini_alg -> Mini_alg -> Mini_alg;
ma_plus xb xc =
  Abs_mini_alg
    ((case rep_mini_alg xb of {
       (p1, (q1, b1)) ->
         (\ (p2, (q2, b2)) ->
           (if Rat.equal_rat q1 Rat.zero_rat then (Rat.plus_rat p1 p2, (q2, b2))
             else ma_normalize (Rat.plus_rat p1 p2, (Rat.plus_rat q1 q2, b1))));
     })
      (rep_mini_alg xc));

ma_sqrt :: Mini_alg -> Mini_alg;
ma_sqrt xa =
  Abs_mini_alg
    (case rep_mini_alg xa of {
      (p, (_, _)) ->
        (case Rat.quotient_of p of {
          (a, b) ->
            let {
              aa = Arith.abs_int (Arith.times_int a b);
            } in (case Sqrt_Babylonian.sqrt_int aa of {
                   [] -> (Rat.zero_rat,
                           (Rat.inverse_rat (Rat.of_int b), Arith.nat aa));
                   s : _ ->
                     (Rat.divide_rat (Rat.of_int s) (Rat.of_int b),
                       (Rat.zero_rat, Arith.zero_nat));
                 });
        });
    });

ma_coeff :: Mini_alg -> Rat.Rat;
ma_coeff xa = fst (snd (rep_mini_alg xa));

ma_floor :: Mini_alg -> Arith.Int;
ma_floor xa =
  (case rep_mini_alg xa of {
    (p, (q, b)) ->
      (case (Rat.quotient_of p, Rat.quotient_of q) of {
        ((z1, n1), (z2, n2)) ->
          let {
            z2n1 = Arith.times_int z2 n1;
            z1n2 = Arith.times_int z1 n2;
            n12 = Arith.times_int n1 n2;
            prod =
              Arith.times_int (Arith.times_int z2n1 z2n1) (Arith.int_of_nat b);
          } in Arith.divide_int
                 (Arith.plus_int z1n2
                   (if Arith.less_eq_int Arith.zero_int z2n1
                     then Sqrt_Babylonian.sqrt_int_floor_pos prod
                     else Arith.uminus_int
                            (Sqrt_Babylonian.sqrt_int_ceiling_pos prod)))
                 n12;
      });
  });

ma_times :: Mini_alg -> Mini_alg -> Mini_alg;
ma_times xb xc =
  Abs_mini_alg
    ((case rep_mini_alg xb of {
       (p1, (q1, b1)) ->
         (\ (p2, (q2, b2)) ->
           (if Rat.equal_rat q1 Rat.zero_rat
             then ma_normalize (Rat.times_rat p1 p2, (Rat.times_rat p1 q2, b2))
             else ma_normalize
                    (Rat.plus_rat (Rat.times_rat p1 p2)
                       (Rat.times_rat (Rat.times_rat (Arith.of_nat b2) q1) q2),
                      (Rat.plus_rat (Rat.times_rat p1 q2) (Rat.times_rat q1 p2),
                        b1))));
     })
      (rep_mini_alg xc));

ma_of_rat :: Rat.Rat -> Mini_alg;
ma_of_rat xa = Abs_mini_alg (xa, (Rat.zero_rat, Arith.zero_nat));

ma_uminus :: Mini_alg -> Mini_alg;
ma_uminus xa =
  Abs_mini_alg
    (case rep_mini_alg xa of {
      (p1, (q1, b1)) -> (Rat.uminus_rat p1, (Rat.uminus_rat q1, b1));
    });

ma_inverse :: Mini_alg -> Mini_alg;
ma_inverse xa =
  Abs_mini_alg
    (case rep_mini_alg xa of {
      (p, (q, b)) ->
        let {
          d = Rat.inverse_rat
                (Rat.minus_rat (Rat.times_rat p p)
                  (Rat.times_rat (Rat.times_rat (Arith.of_nat b) q) q));
        } in ma_normalize
               (Rat.times_rat p d, (Rat.times_rat (Rat.uminus_rat q) d, b));
    });

ma_compatible :: Mini_alg -> Mini_alg -> Bool;
ma_compatible xa xc =
  (case rep_mini_alg xa of {
    (_, (q1, b1)) ->
      (\ (_, (q2, b2)) ->
        Rat.equal_rat q1 Rat.zero_rat ||
          (Rat.equal_rat q2 Rat.zero_rat || Arith.equal_nat b1 b2));
  })
    (rep_mini_alg xc);

}
