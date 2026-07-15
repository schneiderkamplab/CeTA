{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Transcendental(Dist_norm, Real_vector, Metric_space, Sgn_div_norm,
                  Real_normed_vector)
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
import qualified Filter;
import qualified Limits;
import qualified Arith;
import qualified Topological_Spaces;
import qualified Term_Rewriting;

dist_real :: Term_Rewriting.Real -> Term_Rewriting.Real -> Term_Rewriting.Real;
dist_real x y = Term_Rewriting.abs_real (Term_Rewriting.minus_real x y);

class Dist a where {
  dist :: a -> a -> Term_Rewriting.Real;
};

instance Dist Term_Rewriting.Real where {
  dist = dist_real;
};

norm_real :: Term_Rewriting.Real -> Term_Rewriting.Real;
norm_real r = Term_Rewriting.abs_real r;

class Norm a where {
  norm :: a -> Term_Rewriting.Real;
};

instance Norm Term_Rewriting.Real where {
  norm = norm_real;
};

open_real :: Arith.Set Term_Rewriting.Real -> Bool;
open_real _ = error "Real_Vector_Spaces.open_real_inst.open_real";

instance Topological_Spaces.Open Term_Rewriting.Real where {
  open = open_real;
};

scaleR_real ::
  Term_Rewriting.Real -> Term_Rewriting.Real -> Term_Rewriting.Real;
scaleR_real a x = Term_Rewriting.times_real a x;

class ScaleR a where {
  scaleR :: Term_Rewriting.Real -> a -> a;
};

instance ScaleR Term_Rewriting.Real where {
  scaleR = scaleR_real;
};

instance Topological_Spaces.Topological_space Term_Rewriting.Real where {
};

instance Topological_Spaces.T0_space Term_Rewriting.Real where {
};

instance Topological_Spaces.T1_space Term_Rewriting.Real where {
};

instance Topological_Spaces.T2_space Term_Rewriting.Real where {
};

instance Topological_Spaces.T3_space Term_Rewriting.Real where {
};

instance Topological_Spaces.T4_space Term_Rewriting.Real where {
};

instance Limits.Topological_monoid_add Term_Rewriting.Real where {
};

instance Limits.Topological_group_add Term_Rewriting.Real where {
};

class (Arith.Minus a, Dist a, Norm a) => Dist_norm a where {
};

instance Dist_norm Term_Rewriting.Real where {
};

uniformity_real :: Filter.Filter (Term_Rewriting.Real, Term_Rewriting.Real);
uniformity_real =
  Filter.Abstract_filter
    (\ _ ->
      (error :: forall a. String -> (() -> a) -> a)
        "uniformity is not executable" (\ _ -> uniformity_real));

instance Topological_Spaces.Uniformity Term_Rewriting.Real where {
  uniformity = uniformity_real;
};

class (Arith.Ab_group_add a, ScaleR a) => Real_vector a where {
};

instance Real_vector Term_Rewriting.Real where {
};

instance Limits.Topological_comm_monoid_add Term_Rewriting.Real where {
};

instance Limits.Topological_ab_group_add Term_Rewriting.Real where {
};

class (Dist a, Topological_Spaces.Uniformity a) => Uniformity_dist a where {
};

class (Uniformity_dist a, Topological_Spaces.First_countable_topology a,
        Topological_Spaces.T4_space a,
        Topological_Spaces.Uniform_space a) => Metric_space a where {
};

instance Topological_Spaces.First_countable_topology Term_Rewriting.Real where {
};

instance Uniformity_dist Term_Rewriting.Real where {
};

instance Topological_Spaces.Open_uniformity Term_Rewriting.Real where {
};

instance Topological_Spaces.Uniform_space Term_Rewriting.Real where {
};

instance Metric_space Term_Rewriting.Real where {
};

class (Arith.Sgn a, Norm a, ScaleR a) => Sgn_div_norm a where {
};

instance Sgn_div_norm Term_Rewriting.Real where {
};

class (Limits.Topological_ab_group_add a, Dist_norm a, Metric_space a,
        Real_vector a, Sgn_div_norm a) => Real_normed_vector a where {
};

instance Real_normed_vector Term_Rewriting.Real where {
};

}
