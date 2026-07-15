{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Orthogonality_Impl(check_weakly_orthogonal) where {

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
import qualified Critical_Pairs_Impl;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Renaming2;
import qualified Sum_Type;
import qualified Term_Rewriting;
import qualified Shows_Literal;
import qualified Arith;
import qualified Fresh;

check_weakly_orthogonal ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Fresh.Infinite a, Eq a, Arith.Set_impl a,
      Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => Renaming2.Renaming2 a ->
                                  [(Term_Rewriting.Term b a,
                                     Term_Rewriting.Term b a)] ->
                                    Sum_Type.Sum (String -> String) ();
check_weakly_orthogonal ren r =
  Error_Monad.catch_error
    (Error_Monad.bind (Term_Rewriting.check_left_linear_trs r)
      (\ _ ->
        Error_Monad.bind
          (Error_Monad.catch_error
            (Error_Monad.forallM
              (\ (l, _) ->
                Check_Monad.check (not (Term_Rewriting.is_Var l))
                  (Shows_Literal.showsl_lit
                    "the TRS has variables as left-hand sides"))
              r)
            (\ x -> Sum_Type.Inl (snd x)))
          (\ _ ->
            Error_Monad.catch_error
              (Error_Monad.forallM
                (\ (_, (s, t)) ->
                  Check_Monad.check (Term_Rewriting.equal_term s t)
                    (((Shows_Literal.showsl_lit
                         "there is a non-trivial critical pair: " .
                        Term_Rewriting.showsl_terma s) .
                       Shows_Literal.showsl_lit " <- . -> ") .
                      Term_Rewriting.showsl_terma t))
                (Critical_Pairs_Impl.critical_pairs_impl ren r r))
              (\ x -> Sum_Type.Inl (snd x)))))
    (\ x ->
      Sum_Type.Inl
        ((x . Shows_Literal.showsl_lit
                "\nhence, the following TRS is not weakly orthogonal\n") .
          Term_Rewriting.showsl_trs r));

}
