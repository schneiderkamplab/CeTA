{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Sorted_Algebra(rename_vars_exp, has_type) where {

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
import qualified HOL;
import qualified List;
import qualified Arith;
import qualified Product_Type;
import qualified Term;

rename_vars_exp ::
  forall a b c d. (a -> b) -> Term.Term c (a, d) -> Term.Term c (b, d);
rename_vars_exp r = Term.map_term id (Product_Type.map_prod r id);

has_type ::
  forall a b c. (Eq b) => (a -> ([b], b)) -> Term.Term a (c, b) -> b -> Bool;
has_type type_of_fun (Term.Var v) ty = snd v == ty;
has_type type_of_fun (Term.Fun f es) ty =
  ty == snd (type_of_fun f) &&
    Arith.equal_nat (List.size_list es)
      (List.size_list (fst (type_of_fun f))) &&
      let {
        d = Arith.minus_nat (List.size_list es) Arith.one_nat;
      } in (if Arith.less_nat d (List.size_list es)
             then List.all_interval
                    (\ i ->
                      has_type type_of_fun (List.nth es i)
                        (List.nth (fst (type_of_fun f)) i))
                    Arith.zero_nat d
             else True);

}
