{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module RPO_Unbounded(rpo_unbounded) where {

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
import qualified Indexed_Term;
import qualified RPO_Mem_Impl;
import qualified Phantom_Type;
import qualified Mapping;
import qualified WPO;
import qualified Term;
import qualified Arith;
import qualified Mapping_Impl;
import qualified Collection_Order;

rpo_unbounded ::
  forall a b.
    (Eq b) => ((a, Arith.Nat) -> (a, Arith.Nat) -> (Bool, Bool),
                (a, Arith.Nat) -> Bool) ->
                ((a, Arith.Nat) -> WPO.Order_tag) ->
                  Term.Term a b -> Term.Term a b -> (Bool, Bool);
rpo_unbounded pr c s t =
  fst (RPO_Mem_Impl.rpo_mem pr c
        (Mapping_Impl.mapping_empty
          (Phantom_Type.of_phantom
            (Mapping_Impl.mapping_impl_prod ::
              Phantom_Type.Phantom (Arith.Int, Arith.Int)
                Mapping_Impl.Mapping_impla)))
        (Indexed_Term.index_term s, Indexed_Term.index_term t));

}
