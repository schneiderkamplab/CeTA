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
import qualified Product_Type;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Container_Setup;
import qualified List;
import qualified Sum_Type;
import qualified Set;
import qualified Collection_Order;
import qualified Shows_Literal;
import qualified Collection_Eq;
import qualified HOL;
import qualified Cooperation_Program;
import qualified Formula;
import qualified Term;
import qualified LTS;

data Location_addition_info a b c d e =
  Location_Addition_Info d d e (LTS.Transition_rule a b c d);

change_source ::
  forall a b c d.
    a -> LTS.Transition_rule b c d a -> LTS.Transition_rule b c d a;
change_source l (LTS.Transition src tgt phi) = LTS.Transition l tgt phi;

change_target ::
  forall a b c d.
    a -> LTS.Transition_rule b c d a -> LTS.Transition_rule b c d a;
change_target l (LTS.Transition src tgt phi) = LTS.Transition src l phi;

location_addition_outgoing ::
  forall a b c d e f.
    (Eq a, Collection_Eq.Ceq b, Collection_Order.Ccompare b, Eq b, Eq c,
      Shows_Literal.Showl c, HOL.Default d, Shows_Literal.Showl d,
      Collection_Order.Ccompare e, Eq e, Shows_Literal.Showl e,
      Shows_Literal.Showl f) => (a -> ([b], b)) ->
                                  Set.Set b ->
                                    (Term.Term a (c, b) -> String -> String) ->
                                      (d ->
Formula.Formula (Term.Term a (c, b)) -> Sum_Type.Sum (String -> String) ()) ->
(Bool -> Term.Term a (c, b) -> Formula.Formula (Term.Term a (c, b))) ->
  LTS.Lts_impl a c b (Cooperation_Program.Sharp e) f ->
    Location_addition_info a c b (Cooperation_Program.Sharp e) f ->
      Sum_Type.Sum (String -> String)
        (LTS.Lts_impl a c b (Cooperation_Program.Sharp e) f);
location_addition_outgoing type_of_fun bool_types showsl_atom logic_checker
  normalize_lit p (Location_Addition_Info old new skip_ID skip) =
  Error_Monad.bind
    (Check_Monad.check (not (List.member (LTS.nodes_lts_impl p) new))
      ((Shows_Literal.showsl_lit "location-id " .
         Cooperation_Program.showsl_sharp new) .
        Shows_Literal.showsl_lit " is not fresh"))
    (\ _ ->
      Error_Monad.bind
        (Check_Monad.check (Cooperation_Program.is_sharp new)
          ((Shows_Literal.showsl_lit "new location " .
             Cooperation_Program.showsl_sharp new) .
            Shows_Literal.showsl_lit " must be sharp location"))
        (\ _ ->
          Error_Monad.bind
            (Check_Monad.check (Cooperation_Program.is_sharp old)
              ((Shows_Literal.showsl_lit "copied location " .
                 Cooperation_Program.showsl_sharp old) .
                Shows_Literal.showsl_lit " must be sharp location"))
            (\ _ ->
              Error_Monad.bind
                (Check_Monad.check
                  (LTS.transition_rule type_of_fun bool_types skip)
                  ((Shows_Literal.showsl_lit "new transition " .
                     Shows_Literal.showsl skip_ID) .
                    Shows_Literal.showsl_lit " seems to be ill-formed"))
                (\ _ ->
                  Error_Monad.bind
                    (Error_Monad.catch_error
                      (Cooperation_Program.check_skip_transition showsl_atom
                        logic_checker normalize_lit skip)
                      (\ x ->
                        Sum_Type.Inl
                          (((Shows_Literal.showsl_lit "new transition " .
                              Shows_Literal.showsl skip_ID) .
                             Shows_Literal.showsl_lit
                               " must be skip transition\n") .
                            x)))
                    (\ _ ->
                      Error_Monad.bind
                        (Check_Monad.check
                          (Cooperation_Program.equal_sharp (LTS.source skip)
                             old &&
                            Cooperation_Program.equal_sharp (LTS.target skip)
                              new)
                          (((((Shows_Literal.showsl_lit "new skip transition " .
                                Shows_Literal.showsl skip_ID) .
                               Shows_Literal.showsl_lit " must be from ") .
                              Cooperation_Program.showsl_sharp old) .
                             Shows_Literal.showsl_lit " to ") .
                            Cooperation_Program.showsl_sharp new))
                        (\ _ ->
                          let {
                            trans = LTS.transitions_impl p;
                          } in (case List.partition
                                       (\ tau ->
 Cooperation_Program.is_sharp (LTS.source (snd tau)))
                                       trans
                                 of {
                                 (sharp, flat) ->
                                   (case List.partition
   (\ tau -> Cooperation_Program.equal_sharp (LTS.source (snd tau)) old) sharp
                                     of {
                                     (sharp_modify, sharp_keep) ->
                                       let {
 q = LTS.Lts_Impl (LTS.initiala p)
       ((skip_ID, skip) :
         flat ++
           sharp_keep ++
             map (\ tau -> (fst tau, change_source new (snd tau))) sharp_modify)
       ((new, LTS.assertion_of p old) : LTS.assertion_impl p);
                                       } in
 Error_Monad.bind
   (Error_Monad.catch_error
     (Error_Monad.forallM
       (\ l ->
         Check_Monad.check
           (Formula.equal_formula (LTS.assertion_of p l) (LTS.assertion_of q l))
           ((Shows_Literal.showsl_lit "location condition of initial state " .
              Cooperation_Program.showsl_sharp l) .
             Shows_Literal.showsl_lit " has been changed"))
       (LTS.initiala p))
     (\ x -> Sum_Type.Inl (snd x)))
   (\ _ -> Sum_Type.Inr q);
                                   });
                               })))))));

location_addition_incoming ::
  forall a b c d e f.
    (Eq a, Collection_Eq.Ceq b, Collection_Order.Ccompare b, Eq b, Eq c,
      Shows_Literal.Showl c, HOL.Default d, Shows_Literal.Showl d,
      Collection_Order.Ccompare e, Eq e, Shows_Literal.Showl e,
      Shows_Literal.Showl f) => (a -> ([b], b)) ->
                                  Set.Set b ->
                                    (Term.Term a (c, b) -> String -> String) ->
                                      (d ->
Formula.Formula (Term.Term a (c, b)) -> Sum_Type.Sum (String -> String) ()) ->
(Bool -> Term.Term a (c, b) -> Formula.Formula (Term.Term a (c, b))) ->
  LTS.Lts_impl a c b (Cooperation_Program.Sharp e) f ->
    Location_addition_info a c b (Cooperation_Program.Sharp e) f ->
      Sum_Type.Sum (String -> String)
        (LTS.Lts_impl a c b (Cooperation_Program.Sharp e) f);
location_addition_incoming type_of_fun bool_types showsl_atom logic_checker
  normalize_lit p (Location_Addition_Info new old skip_ID skip) =
  Error_Monad.bind
    (Check_Monad.check (not (List.member (LTS.nodes_lts_impl p) new))
      ((Shows_Literal.showsl_lit "location-id " .
         Cooperation_Program.showsl_sharp new) .
        Shows_Literal.showsl_lit " is not fresh"))
    (\ _ ->
      Error_Monad.bind
        (Check_Monad.check (Cooperation_Program.is_sharp new)
          ((Shows_Literal.showsl_lit "new location " .
             Cooperation_Program.showsl_sharp new) .
            Shows_Literal.showsl_lit " must be sharp location"))
        (\ _ ->
          Error_Monad.bind
            (Check_Monad.check (Cooperation_Program.is_sharp old)
              ((Shows_Literal.showsl_lit "copied location " .
                 Cooperation_Program.showsl_sharp old) .
                Shows_Literal.showsl_lit " must be sharp location"))
            (\ _ ->
              Error_Monad.bind
                (Check_Monad.check
                  (LTS.transition_rule type_of_fun bool_types skip)
                  ((Shows_Literal.showsl_lit "new transition " .
                     Shows_Literal.showsl skip_ID) .
                    Shows_Literal.showsl_lit " seems to be ill-formed"))
                (\ _ ->
                  Error_Monad.bind
                    (Error_Monad.catch_error
                      (Cooperation_Program.check_skip_transition showsl_atom
                        logic_checker normalize_lit skip)
                      (\ x ->
                        Sum_Type.Inl
                          (((Shows_Literal.showsl_lit "new transition " .
                              Shows_Literal.showsl skip_ID) .
                             Shows_Literal.showsl_lit
                               " must be skip transition\n") .
                            x)))
                    (\ _ ->
                      Error_Monad.bind
                        (Check_Monad.check
                          (Cooperation_Program.equal_sharp (LTS.source skip)
                             new &&
                            Cooperation_Program.equal_sharp (LTS.target skip)
                              old)
                          (((((Shows_Literal.showsl_lit "new skip transition " .
                                Shows_Literal.showsl skip_ID) .
                               Shows_Literal.showsl_lit " must be from ") .
                              Cooperation_Program.showsl_sharp new) .
                             Shows_Literal.showsl_lit " to ") .
                            Cooperation_Program.showsl_sharp old))
                        (\ _ ->
                          let {
                            trans = LTS.transitions_impl p;
                          } in (case List.partition
                                       (\ tau ->
 Cooperation_Program.is_sharp (LTS.source (snd tau)))
                                       trans
                                 of {
                                 (sharp, flat) ->
                                   (case List.partition
   (\ tau -> Cooperation_Program.equal_sharp (LTS.target (snd tau)) old) sharp
                                     of {
                                     (sharp_modify, sharp_keep) ->
                                       let {
 q = LTS.Lts_Impl (LTS.initiala p)
       ((skip_ID, skip) :
         flat ++
           sharp_keep ++
             map (\ tau -> (fst tau, change_target new (snd tau))) sharp_modify)
       ((new, LTS.assertion_of p old) : LTS.assertion_impl p);
                                       } in
 Error_Monad.bind
   (Error_Monad.catch_error
     (Error_Monad.forallM
       (\ l ->
         Check_Monad.check
           (Formula.equal_formula (LTS.assertion_of p l) (LTS.assertion_of q l))
           ((Shows_Literal.showsl_lit "location condition of initial state " .
              Cooperation_Program.showsl_sharp l) .
             Shows_Literal.showsl_lit " has been changed"))
       (LTS.initiala p))
     (\ x -> Sum_Type.Inl (snd x)))
   (\ _ -> Sum_Type.Inr q);
                                   });
                               })))))));

location_addition ::
  forall a b c d e f.
    (Eq a, Collection_Eq.Ceq b, Collection_Order.Ccompare b, Eq b, Eq c,
      Shows_Literal.Showl c, HOL.Default d, Shows_Literal.Showl d,
      Collection_Order.Ccompare e, Eq e, Shows_Literal.Showl e,
      Shows_Literal.Showl f) => (a -> ([b], b)) ->
                                  Set.Set b ->
                                    (Term.Term a (c, b) -> String -> String) ->
                                      (d ->
Formula.Formula (Term.Term a (c, b)) -> Sum_Type.Sum (String -> String) ()) ->
(Bool -> Term.Term a (c, b) -> Formula.Formula (Term.Term a (c, b))) ->
  LTS.Lts_impl a c b (Cooperation_Program.Sharp e) f ->
    Location_addition_info a c b (Cooperation_Program.Sharp e) f ->
      Sum_Type.Sum (String -> String)
        (LTS.Lts_impl a c b (Cooperation_Program.Sharp e) f);
location_addition type_of_fun bool_types showsl_atom logic_checker normalize_lit
  p info =
  (case info of {
    Location_Addition_Info src _ _ _ ->
      (if not (List.member (LTS.nodes_lts_impl p) src)
        then location_addition_incoming type_of_fun bool_types showsl_atom
               logic_checker normalize_lit p info
        else location_addition_outgoing type_of_fun bool_types showsl_atom
               logic_checker normalize_lit p info);
  });

}
