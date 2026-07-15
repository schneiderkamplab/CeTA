{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Location_Addition(Location_addition_info(..), location_addition) where {

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
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Arith;
import qualified HOL;
import qualified Term_Rewriting;

data Location_addition_info a b c d e =
  Location_Addition_Info d d e (Term_Rewriting.Transition_rule a b c d);

change_source ::
  forall a b c d.
    a -> Term_Rewriting.Transition_rule b c d a ->
           Term_Rewriting.Transition_rule b c d a;
change_source l (Term_Rewriting.Transition src tgt phi) =
  Term_Rewriting.Transition l tgt phi;

change_target ::
  forall a b c d.
    a -> Term_Rewriting.Transition_rule b c d a ->
           Term_Rewriting.Transition_rule b c d a;
change_target l (Term_Rewriting.Transition src tgt phi) =
  Term_Rewriting.Transition src l phi;

location_addition_outgoing ::
  forall a b c d e f.
    (Eq a, Arith.Ceq b, Arith.Ccompare b, Eq b, Eq c, Term_Rewriting.Showl c,
      HOL.Default d, Term_Rewriting.Showl d, Arith.Ccompare e, Eq e,
      Term_Rewriting.Showl e,
      Term_Rewriting.Showl f) => (a -> ([b], b)) ->
                                   Arith.Set b ->
                                     (Term_Rewriting.Term a (c, b) ->
                                       String -> String) ->
                                       (d ->
 Term_Rewriting.Formula (Term_Rewriting.Term a (c, b)) ->
   Sum_Type.Sum (String -> String) ()) ->
 (Bool ->
   Term_Rewriting.Term a (c, b) ->
     Term_Rewriting.Formula (Term_Rewriting.Term a (c, b))) ->
   Term_Rewriting.Lts_impl a c b (Term_Rewriting.Sharp e) f ->
     Location_addition_info a c b (Term_Rewriting.Sharp e) f ->
       Sum_Type.Sum (String -> String)
         (Term_Rewriting.Lts_impl a c b (Term_Rewriting.Sharp e) f);
location_addition_outgoing type_of_fun bool_types showsl_atom logic_checker
  normalize_lit p (Location_Addition_Info old new skip_ID skip) =
  Error_Monad.bind
    (Check_Monad.check
      (not (Arith.membera (Term_Rewriting.nodes_lts_impl p) new))
      ((Term_Rewriting.showsl_lit "location-id " .
         Term_Rewriting.showsl_sharp new) .
        Term_Rewriting.showsl_lit " is not fresh"))
    (\ _ ->
      Error_Monad.bind
        (Check_Monad.check (Term_Rewriting.is_sharp new)
          ((Term_Rewriting.showsl_lit "new location " .
             Term_Rewriting.showsl_sharp new) .
            Term_Rewriting.showsl_lit " must be sharp location"))
        (\ _ ->
          Error_Monad.bind
            (Check_Monad.check (Term_Rewriting.is_sharp old)
              ((Term_Rewriting.showsl_lit "copied location " .
                 Term_Rewriting.showsl_sharp old) .
                Term_Rewriting.showsl_lit " must be sharp location"))
            (\ _ ->
              Error_Monad.bind
                (Check_Monad.check
                  (Term_Rewriting.transition_rule type_of_fun bool_types skip)
                  ((Term_Rewriting.showsl_lit "new transition " .
                     Term_Rewriting.showsl skip_ID) .
                    Term_Rewriting.showsl_lit " seems to be ill-formed"))
                (\ _ ->
                  Error_Monad.bind
                    (Error_Monad.catch_error
                      (Term_Rewriting.check_skip_transition showsl_atom
                        logic_checker normalize_lit skip)
                      (\ x ->
                        Sum_Type.Inl
                          (((Term_Rewriting.showsl_lit "new transition " .
                              Term_Rewriting.showsl skip_ID) .
                             Term_Rewriting.showsl_lit
                               " must be skip transition\n") .
                            x)))
                    (\ _ ->
                      Error_Monad.bind
                        (Check_Monad.check
                          (Term_Rewriting.equal_sharp
                             (Term_Rewriting.source skip) old &&
                            Term_Rewriting.equal_sharp
                              (Term_Rewriting.target skip) new)
                          (((((Term_Rewriting.showsl_lit
                                 "new skip transition " .
                                Term_Rewriting.showsl skip_ID) .
                               Term_Rewriting.showsl_lit " must be from ") .
                              Term_Rewriting.showsl_sharp old) .
                             Term_Rewriting.showsl_lit " to ") .
                            Term_Rewriting.showsl_sharp new))
                        (\ _ ->
                          let {
                            trans = Term_Rewriting.transitions_impl p;
                          } in (case Arith.partition
                                       (\ tau ->
 Term_Rewriting.is_sharp (Term_Rewriting.source (snd tau)))
                                       trans
                                 of {
                                 (sharp, flat) ->
                                   (case Arith.partition
   (\ tau -> Term_Rewriting.equal_sharp (Term_Rewriting.source (snd tau)) old)
   sharp
                                     of {
                                     (sharp_modify, sharp_keep) ->
                                       let {
 q = Term_Rewriting.Lts_Impl (Term_Rewriting.initiala p)
       ((skip_ID, skip) :
         flat ++
           sharp_keep ++
             map (\ tau -> (fst tau, change_source new (snd tau))) sharp_modify)
       ((new, Term_Rewriting.assertion_of p old) :
         Term_Rewriting.assertion_impl p);
                                       } in
 Error_Monad.bind
   (Error_Monad.catch_error
     (Error_Monad.forallM
       (\ l ->
         Check_Monad.check
           (Term_Rewriting.equal_formula (Term_Rewriting.assertion_of p l)
             (Term_Rewriting.assertion_of q l))
           ((Term_Rewriting.showsl_lit "location condition of initial state " .
              Term_Rewriting.showsl_sharp l) .
             Term_Rewriting.showsl_lit " has been changed"))
       (Term_Rewriting.initiala p))
     (\ x -> Sum_Type.Inl (snd x)))
   (\ _ -> Sum_Type.Inr q);
                                   });
                               })))))));

location_addition_incoming ::
  forall a b c d e f.
    (Eq a, Arith.Ceq b, Arith.Ccompare b, Eq b, Eq c, Term_Rewriting.Showl c,
      HOL.Default d, Term_Rewriting.Showl d, Arith.Ccompare e, Eq e,
      Term_Rewriting.Showl e,
      Term_Rewriting.Showl f) => (a -> ([b], b)) ->
                                   Arith.Set b ->
                                     (Term_Rewriting.Term a (c, b) ->
                                       String -> String) ->
                                       (d ->
 Term_Rewriting.Formula (Term_Rewriting.Term a (c, b)) ->
   Sum_Type.Sum (String -> String) ()) ->
 (Bool ->
   Term_Rewriting.Term a (c, b) ->
     Term_Rewriting.Formula (Term_Rewriting.Term a (c, b))) ->
   Term_Rewriting.Lts_impl a c b (Term_Rewriting.Sharp e) f ->
     Location_addition_info a c b (Term_Rewriting.Sharp e) f ->
       Sum_Type.Sum (String -> String)
         (Term_Rewriting.Lts_impl a c b (Term_Rewriting.Sharp e) f);
location_addition_incoming type_of_fun bool_types showsl_atom logic_checker
  normalize_lit p (Location_Addition_Info new old skip_ID skip) =
  Error_Monad.bind
    (Check_Monad.check
      (not (Arith.membera (Term_Rewriting.nodes_lts_impl p) new))
      ((Term_Rewriting.showsl_lit "location-id " .
         Term_Rewriting.showsl_sharp new) .
        Term_Rewriting.showsl_lit " is not fresh"))
    (\ _ ->
      Error_Monad.bind
        (Check_Monad.check (Term_Rewriting.is_sharp new)
          ((Term_Rewriting.showsl_lit "new location " .
             Term_Rewriting.showsl_sharp new) .
            Term_Rewriting.showsl_lit " must be sharp location"))
        (\ _ ->
          Error_Monad.bind
            (Check_Monad.check (Term_Rewriting.is_sharp old)
              ((Term_Rewriting.showsl_lit "copied location " .
                 Term_Rewriting.showsl_sharp old) .
                Term_Rewriting.showsl_lit " must be sharp location"))
            (\ _ ->
              Error_Monad.bind
                (Check_Monad.check
                  (Term_Rewriting.transition_rule type_of_fun bool_types skip)
                  ((Term_Rewriting.showsl_lit "new transition " .
                     Term_Rewriting.showsl skip_ID) .
                    Term_Rewriting.showsl_lit " seems to be ill-formed"))
                (\ _ ->
                  Error_Monad.bind
                    (Error_Monad.catch_error
                      (Term_Rewriting.check_skip_transition showsl_atom
                        logic_checker normalize_lit skip)
                      (\ x ->
                        Sum_Type.Inl
                          (((Term_Rewriting.showsl_lit "new transition " .
                              Term_Rewriting.showsl skip_ID) .
                             Term_Rewriting.showsl_lit
                               " must be skip transition\n") .
                            x)))
                    (\ _ ->
                      Error_Monad.bind
                        (Check_Monad.check
                          (Term_Rewriting.equal_sharp
                             (Term_Rewriting.source skip) new &&
                            Term_Rewriting.equal_sharp
                              (Term_Rewriting.target skip) old)
                          (((((Term_Rewriting.showsl_lit
                                 "new skip transition " .
                                Term_Rewriting.showsl skip_ID) .
                               Term_Rewriting.showsl_lit " must be from ") .
                              Term_Rewriting.showsl_sharp new) .
                             Term_Rewriting.showsl_lit " to ") .
                            Term_Rewriting.showsl_sharp old))
                        (\ _ ->
                          let {
                            trans = Term_Rewriting.transitions_impl p;
                          } in (case Arith.partition
                                       (\ tau ->
 Term_Rewriting.is_sharp (Term_Rewriting.source (snd tau)))
                                       trans
                                 of {
                                 (sharp, flat) ->
                                   (case Arith.partition
   (\ tau -> Term_Rewriting.equal_sharp (Term_Rewriting.target (snd tau)) old)
   sharp
                                     of {
                                     (sharp_modify, sharp_keep) ->
                                       let {
 q = Term_Rewriting.Lts_Impl (Term_Rewriting.initiala p)
       ((skip_ID, skip) :
         flat ++
           sharp_keep ++
             map (\ tau -> (fst tau, change_target new (snd tau))) sharp_modify)
       ((new, Term_Rewriting.assertion_of p old) :
         Term_Rewriting.assertion_impl p);
                                       } in
 Error_Monad.bind
   (Error_Monad.catch_error
     (Error_Monad.forallM
       (\ l ->
         Check_Monad.check
           (Term_Rewriting.equal_formula (Term_Rewriting.assertion_of p l)
             (Term_Rewriting.assertion_of q l))
           ((Term_Rewriting.showsl_lit "location condition of initial state " .
              Term_Rewriting.showsl_sharp l) .
             Term_Rewriting.showsl_lit " has been changed"))
       (Term_Rewriting.initiala p))
     (\ x -> Sum_Type.Inl (snd x)))
   (\ _ -> Sum_Type.Inr q);
                                   });
                               })))))));

location_addition ::
  forall a b c d e f.
    (Eq a, Arith.Ceq b, Arith.Ccompare b, Eq b, Eq c, Term_Rewriting.Showl c,
      HOL.Default d, Term_Rewriting.Showl d, Arith.Ccompare e, Eq e,
      Term_Rewriting.Showl e,
      Term_Rewriting.Showl f) => (a -> ([b], b)) ->
                                   Arith.Set b ->
                                     (Term_Rewriting.Term a (c, b) ->
                                       String -> String) ->
                                       (d ->
 Term_Rewriting.Formula (Term_Rewriting.Term a (c, b)) ->
   Sum_Type.Sum (String -> String) ()) ->
 (Bool ->
   Term_Rewriting.Term a (c, b) ->
     Term_Rewriting.Formula (Term_Rewriting.Term a (c, b))) ->
   Term_Rewriting.Lts_impl a c b (Term_Rewriting.Sharp e) f ->
     Location_addition_info a c b (Term_Rewriting.Sharp e) f ->
       Sum_Type.Sum (String -> String)
         (Term_Rewriting.Lts_impl a c b (Term_Rewriting.Sharp e) f);
location_addition type_of_fun bool_types showsl_atom logic_checker normalize_lit
  p info =
  (case info of {
    Location_Addition_Info src _ _ _ ->
      (if not (Arith.membera (Term_Rewriting.nodes_lts_impl p) src)
        then location_addition_incoming type_of_fun bool_types showsl_atom
               logic_checker normalize_lit p info
        else location_addition_outgoing type_of_fun bool_types showsl_atom
               logic_checker normalize_lit p info);
  });

}
