{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Real_Vector_Spaces(open_real, Dist_norm, Real_vector, Metric_space,
                      Sgn_div_norm, Real_normed_vector)
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
import qualified Transcendental;
import qualified Filter;
import qualified Limits;
import qualified Arith;
import qualified Set;
import qualified Topological_Spaces;
import qualified Real;

dist_real :: Real.Real -> Real.Real -> Real.Real;
dist_real x y = Real.abs_real (Real.minus_real x y);

class Dist a where {
  dist :: a -> a -> Real.Real;
};

instance Dist Real.Real where {
  dist = dist_real;
};

norm_real :: Real.Real -> Real.Real;
norm_real r = Real.abs_real r;

class Norm a where {
  norm :: a -> Real.Real;
};

instance Norm Real.Real where {
  norm = norm_real;
};

open_real :: Set.Set Real.Real -> Bool;
open_real _ = error "Real_Vector_Spaces.open_real_inst.open_real";

instance Topological_Spaces.Open Real.Real where {
  open = open_real;
};

scaleR_real :: Real.Real -> Real.Real -> Real.Real;
scaleR_real a x = Real.times_real a x;

class ScaleR a where {
  scaleR :: Real.Real -> a -> a;
};

instance ScaleR Real.Real where {
  scaleR = scaleR_real;
};

instance Topological_Spaces.Topological_space Real.Real where {
};

instance Topological_Spaces.T0_space Real.Real where {
};

instance Topological_Spaces.T1_space Real.Real where {
};

instance Topological_Spaces.T2_space Real.Real where {
};

instance Limits.Topological_monoid_add Real.Real where {
};

instance Limits.Topological_group_add Real.Real where {
};

class (Arith.Minus a, Dist a, Norm a) => Dist_norm a where {
};

instance Dist_norm Real.Real where {
};

uniformity_real :: Filter.Filter (Real.Real, Real.Real);
uniformity_real =
  Filter.Abstract_filter
    (\ _ ->
      (error :: forall a. String -> (() -> a) -> a)
        "uniformity is not executable" (\ _ -> uniformity_real));

instance Topological_Spaces.Uniformity Real.Real where {
  uniformity = uniformity_real;
};

class (Arith.Ab_group_add a, ScaleR a) => Real_vector a where {
};

instance Real_vector Real.Real where {
};

instance Limits.Topological_comm_monoid_add Real.Real where {
};

instance Limits.Topological_ab_group_add Real.Real where {
};

class (Dist a, Topological_Spaces.Uniformity a) => Uniformity_dist a where {
};

class (Uniformity_dist a, Topological_Spaces.First_countable_topology a,
        Topological_Spaces.T4_space a,
        Topological_Spaces.Uniform_space a) => Metric_space a where {
};

instance Topological_Spaces.First_countable_topology Real.Real where {
};

instance Uniformity_dist Real.Real where {
};

instance Topological_Spaces.Open_uniformity Real.Real where {
};

instance Topological_Spaces.Uniform_space Real.Real where {
};

instance Metric_space Real.Real where {
};

class (Arith.Sgn a, Norm a, ScaleR a) => Sgn_div_norm a where {
};

instance Sgn_div_norm Real.Real where {
};

class (Limits.Topological_ab_group_add a, Dist_norm a, Metric_space a,
        Real_vector a, Sgn_div_norm a) => Real_normed_vector a where {
};

instance Real_normed_vector Real.Real where {
};

}
