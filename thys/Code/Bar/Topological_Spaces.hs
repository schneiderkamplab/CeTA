{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Topological_Spaces(Open(..), Topological_space, T0_space, T1_space, T2_space,
                      T3_space, T4_space, Uniformity(..), Open_uniformity,
                      Uniform_space, First_countable_topology)
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
import qualified Arith;

class Open a where {
  open :: Arith.Set a -> Bool;
};

class (Open a) => Topological_space a where {
};

class (Topological_space a) => T0_space a where {
};

class (T0_space a) => T1_space a where {
};

class (T1_space a) => T2_space a where {
};

class (T2_space a) => T3_space a where {
};

class (T3_space a) => T4_space a where {
};

class Uniformity a where {
  uniformity :: Filter.Filter (a, a);
};

class (Topological_space a, Uniformity a) => Open_uniformity a where {
};

class (Open_uniformity a) => Uniform_space a where {
};

class (Topological_space a) => First_countable_topology a where {
};

}
