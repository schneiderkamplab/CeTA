{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Invariant_Proof_Checkers(Invariant_proof(..), invariant_proof_checker)
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
import qualified Show_LTS;
import qualified FOR_Preliminaries;
import qualified Map_Of;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Mapping;
import qualified HOL;
import qualified Arith;
import qualified Invariant_Checker;
import qualified Term_Rewriting;

data Invariant_proof a b c d e f g =
  Impact [(d, Term_Rewriting.Formula (Term_Rewriting.Term a (b, c)))]
    (Invariant_Checker.Art_impl_ext a b c d e f g ());

restrict_invariants ::
  forall a b c d.
    (Arith.Ceq a,
      Arith.Ccompare a) => (a -> Term_Rewriting.Formula
                                   (Term_Rewriting.Term b (c, d))) ->
                             Arith.Set a ->
                               a -> Term_Rewriting.Formula
                                      (Term_Rewriting.Term b (c, d));
restrict_invariants i la l =
  (if Arith.member l la then i l else Term_Rewriting.Conjunction []);

invariant_proof_checker ::
  forall a b c d e f g.
    (Arith.Ccompare a, Eq a, Term_Rewriting.Showl a, Arith.Ceq b,
      Arith.Ccompare b, Eq b, Term_Rewriting.Showl b, HOL.Default c,
      Term_Rewriting.Showl c, Arith.Ccompare d, Eq d, Term_Rewriting.Showl d,
      Arith.Cenum e, Arith.Ceq e, Arith.Ccompare e, Eq e,
      Mapping.Mapping_impl e, Arith.Set_impl e, Term_Rewriting.Showl e,
      Arith.Ceq f, Arith.Ccompare f, Eq f, Mapping.Mapping_impl f,
      Arith.Set_impl f, Term_Rewriting.Showl f, Arith.Ccompare g, Eq g,
      Mapping.Mapping_impl g,
      Term_Rewriting.Showl g) => (a -> ([b], b)) ->
                                   Arith.Set b ->
                                     (c -> Term_Rewriting.Formula
     (Term_Rewriting.Term a (d, b)) ->
     Sum_Type.Sum (String -> String) ()) ->
                                       (c ->
 Term_Rewriting.Formula
   (Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b)) ->
   Sum_Type.Sum (String -> String) ()) ->
 (Term_Rewriting.Term a (d, b) -> String -> String) ->
   (Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b) ->
     String -> String) ->
     (Bool ->
       Term_Rewriting.Term a (d, b) ->
         Term_Rewriting.Formula (Term_Rewriting.Term a (d, b))) ->
       (Bool ->
         Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b) ->
           Term_Rewriting.Formula
             (Term_Rewriting.Term a (Term_Rewriting.Trans_var d, b))) ->
         Term_Rewriting.Lts_impl a d b e f ->
           Invariant_proof a d b e g f c ->
             Sum_Type.Sum (String -> String)
               (e -> Term_Rewriting.Formula (Term_Rewriting.Term a (d, b)));
invariant_proof_checker type_of_fun bool_types tc tc2 sa sa2 ne ne2 pi
  (Impact ii ai) =
  FOR_Preliminaries.debug id "invariant checking: Impact"
    (let {
       i = Map_Of.map_of_default (Term_Rewriting.Conjunction []) ii;
     } in (case Error_Monad.catch_error
                  (Error_Monad.bind (Invariant_Checker.check_unique_names ai)
                    (\ _ ->
                      Error_Monad.bind
                        (FOR_Preliminaries.debug id
                          "provided invariants against deduced invariants from ART graph"
                          (Error_Monad.catch_error
                            (Error_Monad.forallM
                              (\ l ->
                                let {
                                  il = i l;
                                } in Error_Monad.bind
                                       (Check_Monad.check
 (Term_Rewriting.formula (Term_Rewriting.is_bool type_of_fun bool_types) il)
 (Term_Rewriting.showsl_lit "ill-formed formula for location " .
   Term_Rewriting.showsl l))
                                       (\ _ ->
 Check_Monad.check
   (Term_Rewriting.check_trivial_implication
     (Invariant_Checker.get_disj_invariant (Invariant_Checker.art_of pi ai) l)
     il)
   (Term_Rewriting.showsl_lit
      "could not match provided invariant with invariant extracted from art-graph at location " .
     Term_Rewriting.showsl l)))
                              (Term_Rewriting.nodes_lts_impl pi))
                            (\ x -> Sum_Type.Inl (snd x))))
                        (\ _ ->
                          FOR_Preliminaries.debug id "checking ART graph"
                            (Invariant_Checker.check_art_invariants_impl
                              type_of_fun bool_types tc tc2 sa sa2 ne ne2 ai
                              pi))))
                  (\ x ->
                    Sum_Type.Inl
                      ((((Term_Rewriting.showsl_lit
                            "problem in ensuring invariants for " .
                           Show_LTS.showsl_lts sa sa2 pi) .
                          Term_Rewriting.showsl_lit "\nvia ") .
                         Invariant_Checker.showsl_art ai) .
                        x))
            of {
            Sum_Type.Inl a -> Sum_Type.Inl a;
            Sum_Type.Inr _ ->
              Sum_Type.Inr
                (restrict_invariants i
                  (Arith.set (Term_Rewriting.nodes_lts_impl pi)));
          }));

}
