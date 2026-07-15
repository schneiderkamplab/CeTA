{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Simplex_Incremental(Simplex_state(..), init_simplex, check_simplex,
                       assert_simplex, solution_simplex, assert_all_simplex)
  where {

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
import qualified Rat;
import qualified Sum_Type;
import qualified HOL;
import qualified Simplex_Algebra;
import qualified Mapping;
import qualified QDelta;
import qualified Term_Rewriting;
import qualified Arith;

newtype Simplex_state a = Simplex_State
  ([Term_Rewriting.Ns_constraint QDelta.QDelta],
    ((Mapping.Mapping a [(a, Term_Rewriting.Atom QDelta.QDelta)],
       (Mapping.Mapping Arith.Nat QDelta.QDelta ->
          Mapping.Mapping Arith.Nat QDelta.QDelta,
         [a])),
      Term_Rewriting.State a QDelta.QDelta));

check_s ::
  forall a b.
    (Eq a, Eq b,
      Simplex_Algebra.Lrv b) => Term_Rewriting.State a b ->
                                  (Term_Rewriting.State a b, Maybe [a]);
check_s s =
  let {
    sa = Term_Rewriting.check_code s;
  } in (if Term_Rewriting.u sa
         then (sa, Just (Arith.the (Term_Rewriting.u_c sa)))
         else (sa, Nothing));

assert_s ::
  forall a b.
    (Eq a, Eq b,
      Simplex_Algebra.Lrv b) => (a, Term_Rewriting.Atom b) ->
                                  Term_Rewriting.State a b ->
                                    Sum_Type.Sum [a] (Term_Rewriting.State a b);
assert_s a s =
  let {
    sa = Term_Rewriting.assert_bound_code a s;
  } in (if Term_Rewriting.u sa
         then Sum_Type.Inl (Arith.the (Term_Rewriting.u_c sa))
         else Sum_Type.Inr sa);

create_map ::
  forall a b.
    (Arith.Ccompare a, Eq a,
      Mapping.Mapping_impl a) => [(a, b)] -> Mapping.Mapping a [(a, b)];
create_map [] = Mapping.empty;
create_map ((i, a) : xs) =
  let {
    m = create_map xs;
  } in (case Mapping.lookup m i of {
         Nothing -> Mapping.update i [(i, a)] m;
         Just ias -> Mapping.update i ((i, a) : ias) m;
       });

assert_all_s ::
  forall a b.
    (Eq a, Eq b,
      Simplex_Algebra.Lrv b) => [(a, Term_Rewriting.Atom b)] ->
                                  Term_Rewriting.State a b ->
                                    Sum_Type.Sum [a] (Term_Rewriting.State a b);
assert_all_s [] s = Sum_Type.Inr s;
assert_all_s (a : asa) s = (case assert_s a s of {
                             Sum_Type.Inl aa -> Sum_Type.Inl aa;
                             Sum_Type.Inr aa -> assert_all_s asa aa;
                           });

init_simplex ::
  forall a.
    (Arith.Ceq a, Arith.Ccompare a, Eq a, Mapping.Mapping_impl a,
      Arith.Set_impl a) => [(a, Term_Rewriting.Constraint)] -> Simplex_state a;
init_simplex cs =
  let {
    tons_cs = Term_Rewriting.to_ns cs;
  } in Simplex_State
         (map snd tons_cs,
           (case Term_Rewriting.preprocess tons_cs of {
             (t, (asa, (trans_v, ui))) ->
               ((create_map asa, (trans_v, Arith.remdups ui)),
                 Term_Rewriting.init_state t);
           }));

check_simplex ::
  forall a. (Eq a) => Simplex_state a -> (Simplex_state a, Maybe [a]);
check_simplex (Simplex_State (cs, (asi_tv, s))) =
  (case check_s s of {
    (sa, a) -> (Simplex_State (cs, (asi_tv, sa)), a);
  });

list_map_to_fun ::
  forall a b.
    (Arith.Ccompare a, Eq a) => Mapping.Mapping a [(a, b)] -> a -> [(a, b)];
list_map_to_fun m i = (case Mapping.lookup m i of {
                        Nothing -> [];
                        Just ias -> ias;
                      });

assert_simplex ::
  forall a.
    (Arith.Ccompare a,
      Eq a) => a -> Simplex_state a -> Sum_Type.Sum [a] (Simplex_state a);
assert_simplex i (Simplex_State (cs, ((asi, (tv, ui)), s))) =
  (if Arith.membera ui i then Sum_Type.Inl [i]
    else (case assert_all_s (list_map_to_fun asi i) s of {
           Sum_Type.Inl a -> Sum_Type.Inl a;
           Sum_Type.Inr sa ->
             Sum_Type.Inr (Simplex_State (cs, ((asi, (tv, ui)), sa)));
         }));

solution_simplex :: forall a. Simplex_state a -> Arith.Nat -> Rat.Rat;
solution_simplex (Simplex_State (cs, ((asi, (tv, ui)), s))) =
  Term_Rewriting.map2fun (Term_Rewriting.from_ns (tv (Term_Rewriting.v s)) cs);

assert_all_simplex ::
  forall a.
    (Arith.Ccompare a,
      Eq a) => [a] -> Simplex_state a -> Sum_Type.Sum [a] (Simplex_state a);
assert_all_simplex [] s = Sum_Type.Inr s;
assert_all_simplex (ja : j) s = (case assert_simplex ja s of {
                                  Sum_Type.Inl a -> Sum_Type.Inl a;
                                  Sum_Type.Inr a -> assert_all_simplex j a;
                                });

}
