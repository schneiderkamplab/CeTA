{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module QDP_Framework_Impl(showsl_terms, showsl_tp, showsl_dpp) where {

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
import qualified Dependency_Pair_Problem_Spec;
import qualified HOL;
import qualified Termination_Problem_Spec;
import qualified Shows_Literal;
import qualified Term_Rewriting;

showsl_terms ::
  forall a. (Shows_Literal.Showl a) => String -> [a] -> String -> String;
showsl_terms name ts =
  (Shows_Literal.showsl_lit name . Shows_Literal.showsl_literal "\n") .
    Shows_Literal.showsl_list_gen Shows_Literal.showsl "" "" "\n" "" ts;

showsl_tp ::
  forall a b c.
    (Shows_Literal.Showl b,
      Shows_Literal.Showl c) => Termination_Problem_Spec.Tp_ops_ext a b c () ->
                                  a -> String -> String;
showsl_tp i t =
  let {
    nfs = Termination_Problem_Spec.nfs i t;
    r = Termination_Problem_Spec.r i t;
    rw = Termination_Problem_Spec.rw i t;
    q = Termination_Problem_Spec.q i t;
  } in ((Term_Rewriting.showsl_trsa Shows_Literal.showsl Shows_Literal.showsl
           "rules:" " -> " r .
          (if null rw then id
            else Term_Rewriting.showsl_trsa Shows_Literal.showsl
                   Shows_Literal.showsl "relative rules:" " ->= " rw)) .
         (if null q then id else showsl_terms "Q-component:" q)) .
         (if nfs
           then Shows_Literal.showsl_lit
                  "substitutions are assumed to be in normal form\n"
           else id);

showsl_dpp ::
  forall a b c.
    (Shows_Literal.Showl b,
      Shows_Literal.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b c
                                  () ->
                                  a -> String -> String;
showsl_dpp i d =
  let {
    m = Dependency_Pair_Problem_Spec.minimal i d;
    nfs = Dependency_Pair_Problem_Spec.nfs i d;
    p = Dependency_Pair_Problem_Spec.p i d;
    pw = Dependency_Pair_Problem_Spec.pw i d;
    r = Dependency_Pair_Problem_Spec.r i d;
    rw = Dependency_Pair_Problem_Spec.rw i d;
    q = Dependency_Pair_Problem_Spec.q i d;
  } in (((((Term_Rewriting.showsl_trsa Shows_Literal.showsl Shows_Literal.showsl
              "pairs:" " -> " p .
             (if null pw then id
               else Term_Rewriting.showsl_trsa Shows_Literal.showsl
                      Shows_Literal.showsl "weak pairs:" " ->= " pw)) .
            (if null r then id
              else Term_Rewriting.showsl_trsa Shows_Literal.showsl
                     Shows_Literal.showsl "strict rules:" " ->! " r)) .
           Term_Rewriting.showsl_trsa Shows_Literal.showsl Shows_Literal.showsl
             "rules:" " -> " rw) .
          (if null q then id else showsl_terms "Q-component:" q)) .
         (if m then Shows_Literal.showsl_lit "\n(minimal)" else id)) .
         (if nfs && not (null q)
           then Shows_Literal.showsl_lit "\n(normal form substitutions)"
           else id);

}
