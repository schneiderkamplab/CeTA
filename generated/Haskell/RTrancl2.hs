{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module RTrancl2(mk_rtrancl_set) where {

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
import qualified Arith;
import qualified RBTSetImpl;
import qualified RBT;
import qualified Compare;

mk_rtrancl_set_main ::
  forall a.
    (Compare.Compare_order a) => (a -> [a]) ->
                                   [a] -> RBT.Rbt a () -> RBT.Rbt a ();
mk_rtrancl_set_main r todo fin =
  (case todo of {
    [] -> fin;
    a : tod ->
      (if RBTSetImpl.memb_rm_basic_ops a fin then mk_rtrancl_set_main r tod fin
        else mk_rtrancl_set_main r (r a ++ tod)
               (RBTSetImpl.ins_dj_rm_basic_ops a fin));
  });

mk_rtrancl_set ::
  forall a. (Compare.Compare_order a) => (a -> [a]) -> [a] -> RBT.Rbt a ();
mk_rtrancl_set r init =
  mk_rtrancl_set_main r init (RBTSetImpl.empty_rm_basic_ops ());

}
