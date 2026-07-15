{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Call_Graph_Scc_Decomp(scc_decomposition) where {

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
import qualified Gabow_SCC_RBT;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified HOL;
import qualified Sum_Type;
import qualified Arith;
import qualified Compare;
import qualified Term_Rewriting;
import qualified Shows_Literal;

call_graph_sharp_impl ::
  forall a b c d e.
    (Eq d) => Term_Rewriting.Lts_impl a b c (Term_Rewriting.Sharp d) e ->
                [(Term_Rewriting.Sharp d, Term_Rewriting.Sharp d)];
call_graph_sharp_impl r =
  Arith.remdups
    (concatMap
      (\ tau ->
        (if Term_Rewriting.is_sharp (Term_Rewriting.source (snd tau))
          then [(Term_Rewriting.source (snd tau),
                  Term_Rewriting.target (snd tau))]
          else []))
      (Term_Rewriting.transitions_impl r));

scc_decomposition ::
  forall a b c d e.
    (Arith.Ccompare d, Compare.Compare_order d, Eq d,
      Shows_Literal.Showl d) => Term_Rewriting.Lts_impl a b c
                                  (Term_Rewriting.Sharp d) e ->
                                  [[Term_Rewriting.Sharp d]] ->
                                    Sum_Type.Sum (String -> String)
                                      [Term_Rewriting.Lts_impl a b c
 (Term_Rewriting.Sharp d) e];
scc_decomposition cp sccs_info =
  let {
    cg = call_graph_sharp_impl cp;
    sccs = Gabow_SCC_RBT.scc_decomp cg;
  } in Error_Monad.bind
         (Error_Monad.catch_error
           (Error_Monad.forallM
             (\ c ->
               Check_Monad.check
                 (any (\ d -> Arith.set_eq (Arith.set c) (Arith.set d))
                   sccs_info)
                 ((Shows_Literal.showsl_lit "could not find SCC " .
                    Shows_Literal.showsl_lista c) .
                   Shows_Literal.showsl_lit " in provided decomposition"))
             sccs)
           (\ x -> Sum_Type.Inl (snd x)))
         (\ _ ->
           let {
             trans = Term_Rewriting.transitions_impl cp;
           } in (case Arith.partition
                        (\ tau ->
                          Term_Rewriting.is_sharp
                            (Term_Rewriting.source (snd tau)))
                        trans
                  of {
                  (sharp, flat) ->
                    let {
                      cPs = map (\ c ->
                                  let {
                                    l = Arith.set c;
                                  } in Term_Rewriting.Lts_Impl
 (Term_Rewriting.initiala cp)
 (flat ++
   filter
     (\ tau ->
       Arith.member (Term_Rewriting.source (snd tau)) l &&
         Arith.member (Term_Rewriting.target (snd tau)) l)
     sharp)
 (Term_Rewriting.assertion_impl cp))
                              sccs_info;
                    } in Error_Monad.catch_error (Sum_Type.Inr cPs)
                           (\ x ->
                             Sum_Type.Inl
                               (((Shows_Literal.showsl_lit
                                    "error is SCC-decomposition w.r.t. sccs_info\n" .
                                   Shows_Literal.showsl_lista sccs_info) .
                                  Shows_Literal.showsl_literal "\n") .
                                 x));
                }));

}
