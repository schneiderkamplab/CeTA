{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Tree_Automata_NF_Impl(merge_cl, nf_rules_states_impl) where {

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
import qualified Complete_Lattices;
import qualified Tree_Automata_NF;
import qualified Tree_Automata;
import qualified Cardinality;
import qualified Collection_Enum;
import qualified Phantom_Type;
import qualified Lattices_Big;
import qualified Term_More;
import qualified HOL;
import qualified Set;
import qualified Compare;
import qualified Compare_Instances;
import qualified Container_Setup;
import qualified Collection_Order;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Product_Type;
import qualified Option_Monad;
import qualified Option;
import qualified Arith;
import qualified List;
import qualified Term;

match :: forall a b. (Eq a) => Term.Term a () -> Term.Term a b -> Bool;
match (Term.Var ()) x = True;
match (Term.Fun fa tsa) (Term.Fun f ts) =
  fa == f && List.list_all2 match tsa ts;
match (Term.Fun v va) (Term.Var vb) = False;

merge ::
  forall a.
    (Eq a) => Term.Term a () -> Term.Term a () -> Maybe (Term.Term a ());
merge (Term.Fun fa tsa) (Term.Fun f ts) =
  Option.bind (Option_Monad.guard (fa == f))
    (\ _ ->
      Option.bind
        (Option_Monad.guard
          (Arith.equal_nat (List.size_list tsa) (List.size_list ts)))
        (\ _ ->
          Option.bind (Option_Monad.mapM (\ (a, b) -> merge a b) (zip tsa ts))
            (\ tsb -> Just (Term.Fun fa tsb))));
merge (Term.Var ()) x = Just x;
merge (Term.Fun v va) (Term.Var ()) = Just (Term.Fun v va);

shrinks ::
  forall a.
    (Compare.Compare a,
      Eq a) => Term.Term a () ->
                 Set.Set (Term.Term a ()) -> Set.Set (Term.Term a ());
shrinks ta t =
  let {
    s = Set.filtera (\ s -> match s ta) t;
    max = Lattices_Big.max
            (Set.image (List.size_list . Term_More.funs_term_list) s);
  } in Set.filtera
         (\ sa ->
           Arith.equal_nat ((List.size_list . Term_More.funs_term_list) sa) max)
         s;

merge_cl ::
  forall a.
    (Compare.Compare a,
      Eq a) => Set.Set (Term.Term a ()) -> Set.Set (Term.Term a ());
merge_cl s =
  let {
    new = Set.minus_set
            (Option.these
              (Set.image (\ (a, b) -> merge a b) (Product_Type.product s s)))
            s;
  } in (if Collection_Eq.set_eq new
             (Set_Impl.set_empty
               (Phantom_Type.of_phantom Container_Setup.set_impl_term))
         then s else merge_cl (Set.sup_set s new));

generate_listset ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Set_Impl.Set_impl a) => Arith.Nat -> Set.Set a -> Set.Set [a];
generate_listset n s =
  (if Arith.equal_nat n Arith.zero_nat
    then Set.insert []
           (Set_Impl.set_empty (Phantom_Type.of_phantom Set_Impl.set_impl_list))
    else List.set_Cons s
           (generate_listset (Arith.minus_nat n Arith.one_nat) s));

nf_rules_states_impl ::
  forall a b.
    (Cardinality.Finite_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Compare.Compare a, Eq a,
      Set_Impl.Set_impl a, Compare.Compare b,
      Eq b) => Set.Set (Term.Term a b) ->
                 Set.Set (a, Arith.Nat) ->
                   (Set.Set (Tree_Automata.Ta_rule (Term.Term a ()) a),
                     Set.Set (Term.Term a ()));
nf_rules_states_impl t sig =
  let {
    mcl = Tree_Automata_NF.subt_merge_cl t;
    states =
      Set.filtera
        (\ q ->
          Set.ball t
            (\ ta -> not (match (Term.map_term (\ x -> x) (\ _ -> ()) ta) q)))
        mcl;
    lhss =
      Complete_Lattices.sup_set
        (Set.image
          (\ (f, n) -> Set.image (\ a -> (f, a)) (generate_listset n states))
          sig);
    flhss =
      Set.filtera
        (\ q ->
          Set.ball t
            (\ ta ->
              not (match (Term.map_term (\ x -> x) (\ _ -> ()) ta)
                    (Term.Fun (fst q) (snd q)))))
        lhss;
    rules =
      Set.image
        (\ (f, qs) ->
          Set.image (Tree_Automata.TA_rule f qs) (shrinks (Term.Fun f qs) mcl))
        flhss;
  } in (Complete_Lattices.sup_set rules, states);

}
