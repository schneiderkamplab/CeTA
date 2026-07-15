{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module RPO_Mem_Impl(rpo_mem) where {

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
import qualified List_Memo_Functions;
import qualified Indexed_Term;
import qualified HOL;
import qualified Mapping;
import qualified WPO;
import qualified Term_Rewriting;
import qualified Arith;

rpo_mem ::
  forall a b.
    (Eq b) => ((a, Arith.Nat) -> (a, Arith.Nat) -> (Bool, Bool),
                (a, Arith.Nat) -> Bool) ->
                ((a, Arith.Nat) -> WPO.Order_tag) ->
                  Mapping.Mapping (Arith.Int, Arith.Int) (Bool, Bool) ->
                    (Term_Rewriting.Term
                       (a, (Term_Rewriting.Term a b, Arith.Int))
                       (b, (Term_Rewriting.Term a b, Arith.Int)),
                      Term_Rewriting.Term
                        (a, (Term_Rewriting.Term a b, Arith.Int))
                        (b, (Term_Rewriting.Term a b, Arith.Int))) ->
                      ((Bool, Bool),
                        Mapping.Mapping (Arith.Int, Arith.Int) (Bool, Bool));
rpo_mem pr c mem (s, t) =
  let {
    i = Indexed_Term.index s;
    j = Indexed_Term.index t;
  } in (case Mapping.lookup mem (i, j) of {
         Nothing ->
           (case rpo_main pr c mem (s, t) of {
             (res, mem_new) -> (res, Mapping.update (i, j) res mem_new);
           });
         Just res -> (res, mem);
       });

rpo_main ::
  forall a b.
    (Eq b) => ((a, Arith.Nat) -> (a, Arith.Nat) -> (Bool, Bool),
                (a, Arith.Nat) -> Bool) ->
                ((a, Arith.Nat) -> WPO.Order_tag) ->
                  Mapping.Mapping (Arith.Int, Arith.Int) (Bool, Bool) ->
                    (Term_Rewriting.Term
                       (a, (Term_Rewriting.Term a b, Arith.Int))
                       (b, (Term_Rewriting.Term a b, Arith.Int)),
                      Term_Rewriting.Term
                        (a, (Term_Rewriting.Term a b, Arith.Int))
                        (b, (Term_Rewriting.Term a b, Arith.Int))) ->
                      ((Bool, Bool),
                        Mapping.Mapping (Arith.Int, Arith.Int) (Bool, Bool));
rpo_main pr c mem (s, t) =
  (case s of {
    Term_Rewriting.Var x ->
      ((False,
         (case t of {
           Term_Rewriting.Var y ->
             Indexed_Term.name_of x == Indexed_Term.name_of y;
           Term_Rewriting.Fun g ts ->
             null ts && snd pr (Indexed_Term.name_of g, Arith.zero_nat);
         })),
        mem);
    Term_Rewriting.Fun f ss ->
      let {
        ff = (Indexed_Term.name_of f, Arith.size_list ss);
      } in (case List_Memo_Functions.exists_mem (\ sa -> (sa, t)) (rpo_mem pr c)
                   snd mem ss
             of {
             (True, mem_out_1) -> ((True, True), mem_out_1);
             (False, mem_out_1) ->
               (case t of {
                 Term_Rewriting.Var _ -> ((False, False), mem_out_1);
                 Term_Rewriting.Fun g ts ->
                   let {
                     gg = (Indexed_Term.name_of g, Arith.size_list ts);
                   } in (case fst pr ff gg of {
                          (prs, True) ->
                            (case List_Memo_Functions.forall_mem (\ a -> (s, a))
                                    (rpo_mem pr c) fst mem_out_1 ts
                              of {
                              (True, mem_out_2) ->
                                (if prs then ((True, True), mem_out_2)
                                  else let {
 cf = c ff;
 cg = c gg;
                                       } in
 (if WPO.equal_order_tag cf WPO.Lex && WPO.equal_order_tag cg WPO.Lex
   then List_Memo_Functions.lex_ext_unbounded_mem (rpo_mem pr c) mem_out_2 ss ts
   else (if WPO.equal_order_tag cf WPO.Mul && WPO.equal_order_tag cg WPO.Mul
          then List_Memo_Functions.mul_ext_mem (rpo_mem pr c) mem_out_2 ss ts
          else (if null ts then ((not (null ss), True), mem_out_2)
                 else ((False, False), mem_out_2)))));
                              (False, mem_out_2) -> ((False, False), mem_out_2);
                            });
                          (_, False) -> ((False, False), mem_out_1);
                        });
               });
           });
  });

}
