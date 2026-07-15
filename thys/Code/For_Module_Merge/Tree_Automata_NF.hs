{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Tree_Automata_NF(subt_merge_cl, ta_contains_nf) where {

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
import qualified Term_Impl;
import qualified List;
import qualified Tree_Automata_NF_Impl;
import qualified Product_Type;
import qualified HOL;
import qualified Tree_Automata;
import qualified Phantom_Type;
import qualified Term;
import qualified Set;
import qualified Arith;
import qualified Cardinality;
import qualified Collection_Enum;
import qualified Set_Impl;
import qualified Compare;
import qualified Compare_Instances;
import qualified Collection_Order;
import qualified Collection_Eq;
import qualified Container_Setup;

ta_nf ::
  forall a b.
    (Cardinality.Finite_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Compare.Compare a, Eq a,
      Set_Impl.Set_impl a, Compare.Compare b,
      Eq b) => Set.Set (Term.Term a b) ->
                 Set.Set (a, Arith.Nat) ->
                   Tree_Automata.Ta_ext (Term.Term a ()) a ();
ta_nf t sig =
  (case Tree_Automata_NF_Impl.nf_rules_states_impl t sig of {
    (rules, states) ->
      Tree_Automata.Ta_ext states rules
        (Set_Impl.set_empty
          (Phantom_Type.of_phantom
            (Set_Impl.set_impl_prod ::
              Phantom_Type.Phantom (Term.Term a (), Term.Term a ())
                Set_Impl.Set_impla)))
        ();
  });

subt_merge_cl ::
  forall a b.
    (Compare.Compare a, Eq a, Compare.Compare b,
      Eq b) => Set.Set (Term.Term a b) -> Set.Set (Term.Term a ());
subt_merge_cl s =
  Tree_Automata_NF_Impl.merge_cl
    (Set.sup_set
      (Set.insert (Term.Var ())
        (Set_Impl.set_empty
          (Phantom_Type.of_phantom Container_Setup.set_impl_term)))
      (Complete_Lattices.sup_set
        (Set.image (\ t -> List.set (Term_Impl.supt_list t))
          (Set.image (Term.map_term (\ x -> x) (\ _ -> ())) s))));

ta_contains_nf ::
  forall a b c.
    (Cardinality.Finite_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Eq a, Set_Impl.Set_impl a,
      Cardinality.Finite_UNIV b, Collection_Enum.Cenum b, Collection_Eq.Ceq b,
      Collection_Order.Cproper_interval b, Compare.Compare b, HOL.Default b,
      Eq b, Set_Impl.Set_impl b, Compare.Compare c,
      Eq c) => Tree_Automata.Ta_ext a b () ->
                 Set.Set (Term.Term b c, Term.Term b c) -> Bool;
ta_contains_nf ta r =
  not (Tree_Automata.ta_empty
        (Tree_Automata.intersect_ta
          (ta_nf (Set.image fst r) (Tree_Automata.ta_syms ta)) ta));

}
