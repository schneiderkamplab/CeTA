{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Limits(Topological_monoid_add, Topological_group_add,
          Topological_comm_monoid_add, Topological_ab_group_add)
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
import qualified Topological_Spaces;
import qualified Arith;

class (Arith.Monoid_add a,
        Topological_Spaces.Topological_space a) => Topological_monoid_add a where {
};

class (Arith.Group_add a,
        Topological_monoid_add a) => Topological_group_add a where {
};

class (Arith.Comm_monoid_add a,
        Topological_monoid_add a) => Topological_comm_monoid_add a where {
};

class (Arith.Ab_group_add a, Topological_comm_monoid_add a,
        Topological_group_add a) => Topological_ab_group_add a where {
};

}
