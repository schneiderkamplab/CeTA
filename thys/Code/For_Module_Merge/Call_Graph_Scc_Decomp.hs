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
import qualified Product_Type;
import qualified Gabow_SCC_RBT;
import qualified Collection_Eq;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified List;
import qualified HOL;
import qualified Formula;
import qualified Sum_Type;
import qualified LTS;
import qualified Term;
import qualified Set;
import qualified Collection_Order;
import qualified Compare;
import qualified Container_Setup;
import qualified Cooperation_Program;
import qualified Shows_Literal;

call_graph_sharp_impl ::
  forall a b c d e.
    (Eq d) => LTS.Lts_impl a b c (Cooperation_Program.Sharp d) e ->
                [(Cooperation_Program.Sharp d, Cooperation_Program.Sharp d)];
call_graph_sharp_impl r =
  List.remdups
    (concatMap
      (\ tau ->
        (if Cooperation_Program.is_sharp (LTS.source (snd tau))
          then [(LTS.source (snd tau), LTS.target (snd tau))] else []))
      (LTS.transitions_impl r));

scc_decomposition ::
  forall a b c d e.
    (Collection_Order.Ccompare d, Compare.Compare_order d, Eq d,
      Shows_Literal.Showl d) => LTS.Lts_impl a b c (Cooperation_Program.Sharp d)
                                  e ->
                                  [[Cooperation_Program.Sharp d]] ->
                                    Sum_Type.Sum (String -> String)
                                      [LTS.Lts_impl a b c
 (Cooperation_Program.Sharp d) e];
scc_decomposition cp sccs_info =
  let {
    cg = call_graph_sharp_impl cp;
    sccs = Gabow_SCC_RBT.scc_decomp cg;
  } in Error_Monad.bind
         (Error_Monad.catch_error
           (Error_Monad.forallM
             (\ c ->
               Check_Monad.check
                 (any (\ d -> Collection_Eq.set_eq (List.set c) (List.set d))
                   sccs_info)
                 ((Shows_Literal.showsl_lit "could not find SCC " .
                    Shows_Literal.showsl_lista c) .
                   Shows_Literal.showsl_lit " in provided decomposition"))
             sccs)
           (\ x -> Sum_Type.Inl (snd x)))
         (\ _ ->
           let {
             trans = LTS.transitions_impl cp;
           } in (case List.partition
                        (\ tau ->
                          Cooperation_Program.is_sharp (LTS.source (snd tau)))
                        trans
                  of {
                  (sharp, flat) ->
                    let {
                      cPs = map (\ c ->
                                  let {
                                    l = List.set c;
                                  } in LTS.Lts_Impl (LTS.initiala cp)
 (flat ++
   filter
     (\ tau ->
       Set.member (LTS.source (snd tau)) l &&
         Set.member (LTS.target (snd tau)) l)
     sharp)
 (LTS.assertion_impl cp))
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
