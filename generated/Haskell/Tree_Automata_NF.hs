{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Tree_Automata_NF(ta_contains_nf) where {

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
import qualified Lattices_Big;
import qualified Option_Monad;
import qualified HOL;
import qualified Phantom_Type;
import qualified Compare;
import qualified Arith;
import qualified Term_Rewriting;

generate_listset ::
  forall a.
    (Arith.Ceq a, Arith.Ccompare a,
      Arith.Set_impl a) => Arith.Nat -> Arith.Set a -> Arith.Set [a];
generate_listset n s =
  (if Arith.equal_nat n Arith.zero_nat
    then Arith.insert []
           (Arith.set_empty (Phantom_Type.of_phantom Arith.set_impl_list))
    else Arith.set_Cons s
           (generate_listset (Arith.minus_nat n Arith.one_nat) s));

merge ::
  forall a.
    (Eq a) => Term_Rewriting.Term a () ->
                Term_Rewriting.Term a () -> Maybe (Term_Rewriting.Term a ());
merge (Term_Rewriting.Fun fa tsa) (Term_Rewriting.Fun f ts) =
  Arith.bind (Option_Monad.guard (fa == f))
    (\ _ ->
      Arith.bind
        (Option_Monad.guard
          (Arith.equal_nat (Arith.size_list tsa) (Arith.size_list ts)))
        (\ _ ->
          Arith.bind (Option_Monad.mapM (\ (a, b) -> merge a b) (zip tsa ts))
            (\ tsb -> Just (Term_Rewriting.Fun fa tsb))));
merge (Term_Rewriting.Var ()) x = Just x;
merge (Term_Rewriting.Fun v va) (Term_Rewriting.Var ()) =
  Just (Term_Rewriting.Fun v va);

merge_cl ::
  forall a.
    (Compare.Compare a,
      Eq a) => Arith.Set (Term_Rewriting.Term a ()) ->
                 Arith.Set (Term_Rewriting.Term a ());
merge_cl s =
  let {
    new = Arith.minus_set
            (Arith.these
              (Arith.image (\ (a, b) -> merge a b) (Arith.productc s s)))
            s;
  } in (if Arith.set_eq new
             (Arith.set_empty
               (Phantom_Type.of_phantom Term_Rewriting.set_impl_term))
         then s else merge_cl (Arith.sup_set s new));

subt_merge_cl ::
  forall a b.
    (Compare.Compare a, Eq a, Compare.Compare b,
      Eq b) => Arith.Set (Term_Rewriting.Term a b) ->
                 Arith.Set (Term_Rewriting.Term a ());
subt_merge_cl s =
  merge_cl
    (Arith.sup_set
      (Arith.insert (Term_Rewriting.Var ())
        (Arith.set_empty
          (Phantom_Type.of_phantom Term_Rewriting.set_impl_term)))
      (Complete_Lattices.sup_set
        (Arith.image (\ t -> Arith.set (Term_Rewriting.supt_list t))
          (Arith.image (Term_Rewriting.map_term (\ x -> x) (\ _ -> ())) s))));

match ::
  forall a b.
    (Eq a) => Term_Rewriting.Term a () -> Term_Rewriting.Term a b -> Bool;
match (Term_Rewriting.Var ()) x = True;
match (Term_Rewriting.Fun fa tsa) (Term_Rewriting.Fun f ts) =
  fa == f && Arith.list_all2 match tsa ts;
match (Term_Rewriting.Fun v va) (Term_Rewriting.Var vb) = False;

shrinks ::
  forall a.
    (Compare.Compare a,
      Eq a) => Term_Rewriting.Term a () ->
                 Arith.Set (Term_Rewriting.Term a ()) ->
                   Arith.Set (Term_Rewriting.Term a ());
shrinks ta t =
  let {
    s = Arith.filtera (\ s -> match s ta) t;
    max = Lattices_Big.max
            (Arith.image (Arith.size_list . Term_Rewriting.funs_term_list) s);
  } in Arith.filtera
         (\ sa ->
           Arith.equal_nat
             ((Arith.size_list . Term_Rewriting.funs_term_list) sa) max)
         s;

nf_rules_states_impl ::
  forall a b.
    (Arith.Finite_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Compare.Compare a, Eq a, Arith.Set_impl a, Compare.Compare b,
      Eq b) => Arith.Set (Term_Rewriting.Term a b) ->
                 Arith.Set (a, Arith.Nat) ->
                   (Arith.Set
                      (Term_Rewriting.Ta_rule (Term_Rewriting.Term a ()) a),
                     Arith.Set (Term_Rewriting.Term a ()));
nf_rules_states_impl t sig =
  let {
    mcl = subt_merge_cl t;
    states =
      Arith.filtera
        (\ q ->
          Arith.ball t
            (\ ta ->
              not (match (Term_Rewriting.map_term (\ x -> x) (\ _ -> ()) ta)
                    q)))
        mcl;
    lhss =
      Complete_Lattices.sup_set
        (Arith.image
          (\ (f, n) -> Arith.image (\ a -> (f, a)) (generate_listset n states))
          sig);
    flhss =
      Arith.filtera
        (\ q ->
          Arith.ball t
            (\ ta ->
              not (match (Term_Rewriting.map_term (\ x -> x) (\ _ -> ()) ta)
                    (Term_Rewriting.Fun (fst q) (snd q)))))
        lhss;
    rules =
      Arith.image
        (\ (f, qs) ->
          Arith.image (Term_Rewriting.TA_rule f qs)
            (shrinks (Term_Rewriting.Fun f qs) mcl))
        flhss;
  } in (Complete_Lattices.sup_set rules, states);

ta_nf ::
  forall a b.
    (Arith.Finite_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Compare.Compare a, Eq a, Arith.Set_impl a, Compare.Compare b,
      Eq b) => Arith.Set (Term_Rewriting.Term a b) ->
                 Arith.Set (a, Arith.Nat) ->
                   Term_Rewriting.Ta_ext (Term_Rewriting.Term a ()) a ();
ta_nf t sig =
  (case nf_rules_states_impl t sig of {
    (rules, states) ->
      Term_Rewriting.Ta_ext states rules
        (Arith.set_empty
          (Phantom_Type.of_phantom
            (Arith.set_impl_prod ::
              Phantom_Type.Phantom
                (Term_Rewriting.Term a (), Term_Rewriting.Term a ())
                Arith.Set_impla)))
        ();
  });

ta_contains_nf ::
  forall a b c.
    (Arith.Finite_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Eq a, Arith.Set_impl a, Arith.Finite_UNIV b, Arith.Cenum b, Arith.Ceq b,
      Arith.Cproper_interval b, Compare.Compare b, HOL.Default b, Eq b,
      Arith.Set_impl b, Compare.Compare c,
      Eq c) => Term_Rewriting.Ta_ext a b () ->
                 Arith.Set (Term_Rewriting.Term b c, Term_Rewriting.Term b c) ->
                   Bool;
ta_contains_nf ta r =
  not (Term_Rewriting.ta_empty
        (Term_Rewriting.intersect_ta
          (ta_nf (Arith.image fst r) (Term_Rewriting.ta_syms ta)) ta));

}
