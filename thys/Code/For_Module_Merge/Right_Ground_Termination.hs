{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Right_Ground_Termination(right_ground_termination) where {

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
import qualified Option;
import qualified Term_Impl;
import qualified Product_Type;
import qualified List;
import qualified Term;

rg_init ::
  forall a b.
    (Eq a,
      Eq b) => (Term.Term a b -> [Term.Term a b]) ->
                 [(Term.Term a b, Term.Term a b)] ->
                   [(Term.Term a b, Term.Term a b)];
rg_init rewr r =
  List.remdups (concatMap (\ (_, ra) -> map (\ a -> (ra, a)) (rewr ra)) r);

is_subterm ::
  forall a b. (Eq a, Eq b) => (Term.Term a b, Term.Term a b) -> Bool;
is_subterm (s, t) = Term.equal_term t s || Term_Impl.supt_impl t s;

advance_sequence ::
  forall a b.
    (Eq a,
      Eq b) => (Term.Term a b -> [Term.Term a b]) ->
                 [(Term.Term a b, Term.Term a b)] ->
                   [(Term.Term a b, Term.Term a b)];
advance_sequence rewr xs =
  List.remdups (concatMap (\ (r, t) -> map (\ a -> (r, a)) (rewr t)) xs);

right_ground_termination_step ::
  forall a b.
    (Eq a,
      Eq b) => (Term.Term a b -> [Term.Term a b]) ->
                 [(Term.Term a b, Term.Term a b)] -> Bool;
right_ground_termination_step rewr s =
  (case s of {
    [] -> True;
    _ : _ ->
      (case List.find is_subterm s of {
        Nothing -> right_ground_termination_step rewr (advance_sequence rewr s);
        Just _ -> False;
      });
  });

right_ground_termination ::
  forall a b.
    (Eq a,
      Eq b) => (Term.Term a b -> [Term.Term a b]) ->
                 [(Term.Term a b, Term.Term a b)] -> Bool;
right_ground_termination rewr r =
  right_ground_termination_step rewr (rg_init rewr r);

}
