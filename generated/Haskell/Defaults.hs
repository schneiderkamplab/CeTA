{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Defaults(default_nfs_dp, default_nfs_trs, default_nfs_nt_dp,
            default_nfs_nt_trs)
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

default_nfs_dp :: Bool;
default_nfs_dp = True;

default_nfs_trs :: Bool;
default_nfs_trs = False;

default_nfs_nt_dp :: Bool;
default_nfs_nt_dp = False;

default_nfs_nt_trs :: Bool;
default_nfs_nt_trs = False;

}
