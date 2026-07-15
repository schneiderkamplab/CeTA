{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module WPO_Mem_Impl(wpo_mem_impl) where {

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
import qualified Phantom_Type;
import qualified Mapping_Impl;
import qualified List_Memo_Functions;
import qualified List;
import qualified Product_Type;
import qualified Option;
import qualified Indexed_Term;
import qualified HOL;
import qualified Mapping;
import qualified WPO;
import qualified Status;
import qualified Term;
import qualified Collection_Order;
import qualified Arith;

wpo_mem ::
  forall a b.
    (Eq b) => ((a, Arith.Nat) -> (a, Arith.Nat) -> (Bool, Bool)) ->
                ((a, Arith.Nat) -> Bool) ->
                  Bool ->
                    ((a, Arith.Nat) -> Bool) ->
                      (Term.Term a b -> Term.Term a b -> Bool) ->
                        (Term.Term a b -> Term.Term a b -> Bool) ->
                          Status.Status a ->
                            ((a, Arith.Nat) -> WPO.Order_tag) ->
                              Mapping.Mapping (Arith.Int, Arith.Int)
                                (Bool, Bool) ->
                                (Term.Term (a, (Term.Term a b, Arith.Int))
                                   (b, (Term.Term a b, Arith.Int)),
                                  Term.Term (a, (Term.Term a b, Arith.Int))
                                    (b, (Term.Term a b, Arith.Int))) ->
                                  ((Bool, Bool),
                                    Mapping.Mapping (Arith.Int, Arith.Int)
                                      (Bool, Bool));
wpo_mem pr prl ssimple large cS cNS sigma c mem (s, t) =
  let {
    i = Indexed_Term.index s;
    j = Indexed_Term.index t;
  } in (case Mapping.lookup mem (i, j) of {
         Nothing ->
           (case wpo_main pr prl ssimple large cS cNS sigma c mem (s, t) of {
             (res, mem_new) -> (res, Mapping.update (i, j) res mem_new);
           });
         Just res -> (res, mem);
       });

wpo_main ::
  forall a b.
    (Eq b) => ((a, Arith.Nat) -> (a, Arith.Nat) -> (Bool, Bool)) ->
                ((a, Arith.Nat) -> Bool) ->
                  Bool ->
                    ((a, Arith.Nat) -> Bool) ->
                      (Term.Term a b -> Term.Term a b -> Bool) ->
                        (Term.Term a b -> Term.Term a b -> Bool) ->
                          Status.Status a ->
                            ((a, Arith.Nat) -> WPO.Order_tag) ->
                              Mapping.Mapping (Arith.Int, Arith.Int)
                                (Bool, Bool) ->
                                (Term.Term (a, (Term.Term a b, Arith.Int))
                                   (b, (Term.Term a b, Arith.Int)),
                                  Term.Term (a, (Term.Term a b, Arith.Int))
                                    (b, (Term.Term a b, Arith.Int))) ->
                                  ((Bool, Bool),
                                    Mapping.Mapping (Arith.Int, Arith.Int)
                                      (Bool, Bool));
wpo_main pr prl ssimple large cS cNS sigma c mem (s, t) =
  let {
    fs = Indexed_Term.stored s;
    ft = Indexed_Term.stored t;
  } in (if cS fs ft then ((True, True), mem)
         else (if cNS fs ft
                then (case s of {
                       Term.Var x ->
                         ((False,
                            (case t of {
                              Term.Var y ->
                                Indexed_Term.name_of x ==
                                  Indexed_Term.name_of y;
                              Term.Fun g ts ->
                                null (Status.status sigma
                                       (Indexed_Term.name_of g,
 List.size_list ts)) &&
                                  prl (Indexed_Term.name_of g,
List.size_list ts);
                            })),
                           mem);
                       Term.Fun f ss ->
                         let {
                           ff = (Indexed_Term.name_of f, List.size_list ss);
                           sf = Status.status sigma ff;
                           ssa = map (List.nth ss) sf;
                         } in (case List_Memo_Functions.exists_mem
                                      (\ sa -> (sa, t))
                                      (wpo_mem pr prl ssimple large cS cNS sigma
c)
                                      snd mem ssa
                                of {
                                (True, mem_out_1) -> ((True, True), mem_out_1);
                                (False, mem_out_1) ->
                                  (case t of {
                                    Term.Var _ ->
                                      ((False, ssimple && large ff), mem_out_1);
                                    Term.Fun g ts ->
                                      let {
gg = (Indexed_Term.name_of g, List.size_list ts);
sg = Status.status sigma gg;
tsa = map (List.nth ts) sg;
                                      } in
(case pr ff gg of {
  (prs, True) ->
    (case List_Memo_Functions.forall_mem (\ a -> (s, a))
            (wpo_mem pr prl ssimple large cS cNS sigma c) fst mem_out_1 tsa
      of {
      (True, mem_out_2) ->
        (if prs then ((True, True), mem_out_2)
          else let {
                 cf = c ff;
                 cg = c gg;
               } in (if WPO.equal_order_tag cf WPO.Lex &&
                          WPO.equal_order_tag cg WPO.Lex
                      then List_Memo_Functions.lex_ext_unbounded_mem
                             (wpo_mem pr prl ssimple large cS cNS sigma c)
                             mem_out_2 ssa tsa
                      else (if WPO.equal_order_tag cf WPO.Mul &&
                                 WPO.equal_order_tag cg WPO.Mul
                             then List_Memo_Functions.mul_ext_mem
                                    (wpo_mem pr prl ssimple large cS cNS sigma
                                      c)
                                    mem_out_2 ssa tsa
                             else (if null tsa
                                    then ((not (null ssa), True), mem_out_2)
                                    else ((False, False), mem_out_2)))));
      (False, mem_out_2) -> ((False, False), mem_out_2);
    });
  (_, False) -> ((False, False), mem_out_1);
});
                                  });
                              });
                     })
                else ((False, False), mem)));

wpo_mem_impl ::
  forall a b.
    (Eq b) => ((a, Arith.Nat) -> (a, Arith.Nat) -> (Bool, Bool)) ->
                ((a, Arith.Nat) -> Bool) ->
                  Bool ->
                    ((a, Arith.Nat) -> Bool) ->
                      (Term.Term a b -> Term.Term a b -> Bool) ->
                        (Term.Term a b -> Term.Term a b -> Bool) ->
                          Status.Status a ->
                            ((a, Arith.Nat) -> WPO.Order_tag) ->
                              Term.Term a b -> Term.Term a b -> (Bool, Bool);
wpo_mem_impl pr prl ssimple large cS cNS sigma c s t =
  fst (wpo_mem pr prl ssimple large cS cNS sigma c
        (Mapping_Impl.mapping_empty
          (Phantom_Type.of_phantom
            (Mapping_Impl.mapping_impl_prod ::
              Phantom_Type.Phantom (Arith.Int, Arith.Int)
                Mapping_Impl.Mapping_impla)))
        (Indexed_Term.index_term s, Indexed_Term.index_term t));

}
