{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module RenamingN_String(string_renameN) where {

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
import qualified RenamingN;
import qualified Lists_are_Infinite;
import qualified Term_Rewriting;
import qualified Arith;

x_var_list :: (Arith.Nat, [Arith.Char]) -> [Arith.Char];
x_var_list ns =
  (case ns of {
    (n, s) ->
      Arith.char_0x78 :
        Term_Rewriting.shows_prec_nat Arith.zero_nat n [] ++
          [Arith.char_0x5F] ++ s;
  });

string_renameN :: RenamingN.RenamingN [Arith.Char];
string_renameN =
  RenamingN.Abs_renamingN (x_var_list, (\ a -> Arith.char_0x79 : a));

}
