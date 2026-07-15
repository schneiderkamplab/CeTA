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
import qualified Term_Rewriting;

showsl_terms ::
  forall a. (Term_Rewriting.Showl a) => String -> [a] -> String -> String;
showsl_terms name ts =
  (Term_Rewriting.showsl_lit name . Term_Rewriting.showsl_literal "\n") .
    Term_Rewriting.showsl_list_gen Term_Rewriting.showsl "" "" "\n" "" ts;

showsl_tp ::
  forall a b c.
    (Term_Rewriting.Showl b,
      Term_Rewriting.Showl c) => Termination_Problem_Spec.Tp_ops_ext a b c () ->
                                   a -> String -> String;
showsl_tp i t =
  let {
    nfs = Termination_Problem_Spec.nfs i t;
    r = Termination_Problem_Spec.r i t;
    rw = Termination_Problem_Spec.rw i t;
    q = Termination_Problem_Spec.q i t;
  } in ((Term_Rewriting.showsl_trsa Term_Rewriting.showsl Term_Rewriting.showsl
           "rules:" " -> " r .
          (if null rw then id
            else Term_Rewriting.showsl_trsa Term_Rewriting.showsl
                   Term_Rewriting.showsl "relative rules:" " ->= " rw)) .
         (if null q then id else showsl_terms "Q-component:" q)) .
         (if nfs
           then Term_Rewriting.showsl_lit
                  "substitutions are assumed to be in normal form\n"
           else id);

showsl_dpp ::
  forall a b c.
    (Term_Rewriting.Showl b,
      Term_Rewriting.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b c
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
  } in (((((Term_Rewriting.showsl_trsa Term_Rewriting.showsl
              Term_Rewriting.showsl "pairs:" " -> " p .
             (if null pw then id
               else Term_Rewriting.showsl_trsa Term_Rewriting.showsl
                      Term_Rewriting.showsl "weak pairs:" " ->= " pw)) .
            (if null r then id
              else Term_Rewriting.showsl_trsa Term_Rewriting.showsl
                     Term_Rewriting.showsl "strict rules:" " ->! " r)) .
           Term_Rewriting.showsl_trsa Term_Rewriting.showsl
             Term_Rewriting.showsl "rules:" " -> " rw) .
          (if null q then id else showsl_terms "Q-component:" q)) .
         (if m then Term_Rewriting.showsl_lit "\n(minimal)" else id)) .
         (if nfs && not (null q)
           then Term_Rewriting.showsl_lit "\n(normal form substitutions)"
           else id);

}
