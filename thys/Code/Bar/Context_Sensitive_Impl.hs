{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Context_Sensitive_Impl(mu_to_fp_impl) where {

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
import qualified Name;
import qualified Map;
import qualified HOL;
import qualified Forbidden_Patterns;
import qualified Term_Rewriting;
import qualified Arith;

mu_to_fp_impl ::
  forall a.
    (Eq a) => [((a, Arith.Nat), [Arith.Nat])] ->
                [(Term_Rewriting.Actxt a (Term_Rewriting.Term a [Arith.Char]),
                   (Term_Rewriting.Term a [Arith.Char],
                     Forbidden_Patterns.Location))];
mu_to_fp_impl mu =
  let {
    fs = Arith.remdups (map fst mu);
    m = Map.map_of mu;
    a = concatMap
          (\ f ->
            let {
              xs = map Term_Rewriting.Var
                     (Name.fresh_strings_list [Arith.char_0x78] Arith.zero_nat
                       [] (snd f));
            } in map (\ i -> (f, (xs, i)))
                   (concatMap
                     (\ i ->
                       (if not (Arith.membera (Arith.the (m f)) i) then [i]
                         else []))
                     (Arith.upt Arith.zero_nat (snd f))))
          fs;
  } in concatMap
         (\ (aa, b) ->
           (case aa of {
             (f, _) ->
               (\ (xs, i) ->
                 map (\ loc ->
                       (Term_Rewriting.ctxt_of_pos_term [i]
                          (Term_Rewriting.Fun f xs),
                         (Arith.nth xs i, loc)))
                   [Forbidden_Patterns.B, Forbidden_Patterns.H]);
           })
             b)
         a;

}
