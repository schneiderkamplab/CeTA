{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Fresh_Variable_Addition(Fresh_variable_addition_info(..),
                           fresh_variable_addition)
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
import qualified Mapping;
import qualified Mapping_Impl;
import qualified Term_More;
import qualified Product_Type;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified HOL;
import qualified Sum_Type;
import qualified Set;
import qualified Collection_Order;
import qualified Shows_Literal;
import qualified Collection_Eq;
import qualified Formula;
import qualified LTS;
import qualified Term;

data Fresh_variable_addition_info a b c d =
  Fresh_Variable_Addition_Info b c
    [(d, Formula.Formula (Term.Term a (LTS.Trans_var b, c)))];

fresh_variable_checker ::
  forall a b c d e.
    (Shows_Literal.Showl a, Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Eq b, Shows_Literal.Showl b, Eq c, Shows_Literal.Showl c,
      Shows_Literal.Showl d,
      Shows_Literal.Showl e) => (a -> ([b], b)) ->
                                  Set.Set b ->
                                    (LTS.Trans_var c ->
                                      b ->
Formula.Formula (Term.Term a (LTS.Trans_var c, b)) ->
  Sum_Type.Sum (String -> String) ()) ->
                                      (Term.Term a (LTS.Trans_var c, b) ->
String -> String) ->
LTS.Lts_impl a c b d e ->
  (e -> Formula.Formula (Term.Term a (LTS.Trans_var c, b))) ->
    c -> b -> Sum_Type.Sum (String -> String) ();
fresh_variable_checker type_of_fun bool_types definability_checker sa2 p f x ty
  = Error_Monad.catch_error
      (Error_Monad.bind
        (Error_Monad.catch_error
          (Error_Monad.forallM
            (\ (l, fa) ->
              Check_Monad.check (not (Formula.in_vars_formula (x, ty) fa))
                ((Shows_Literal.showsl x .
                   Shows_Literal.showsl_lit
                     " is not fresh, it occurs in location condition of ") .
                  Shows_Literal.showsl l))
            (LTS.assertion_impl p))
          (\ xa -> Sum_Type.Inl (snd xa)))
        (\ _ ->
          Error_Monad.catch_error
            (Error_Monad.forallM
              (\ (tr, tau) ->
                let {
                  psi = f tr;
                } in Error_Monad.bind
                       (Check_Monad.check
                         (Formula.formula
                           (Formula.is_bool type_of_fun bool_types) psi)
                         (Shows_Literal.showsl_lit
                           "new transition formula seems to be not well-formed"))
                       (\ _ ->
                         Error_Monad.catch_error
                           (case tau of {
                             LTS.Transition _ _ phi ->
                               Error_Monad.bind
                                 (definability_checker (LTS.Post x) ty psi)
                                 (\ _ ->
                                   Error_Monad.bind
                                     (Check_Monad.check
                                       (not
 (Formula.in_vars_formula (LTS.Post x, ty) phi))
                                       (Shows_Literal.showsl_lit
  "Post x in transition formula" .
 Formula.showsl_formula sa2 phi))
                                     (\ _ ->
                                       Check_Monad.check
 (not (Formula.in_vars_formula (LTS.Pre x, ty) phi))
 (Shows_Literal.showsl_lit "Pre x in transition formula" .
   Formula.showsl_formula sa2 phi)));
                           })
                           (\ xa ->
                             Sum_Type.Inl
                               (((Shows_Literal.showsl_lit
                                    "problem in transition formula of transition " .
                                   Shows_Literal.showsl tr) .
                                  Shows_Literal.showsl_literal "\n") .
                                 xa))))
              (LTS.transitions_impl p))
            (\ xa -> Sum_Type.Inl (snd xa))))
      (\ xa ->
        Sum_Type.Inl
          (Shows_Literal.showsl_lit "fresh_variable_checker failed\n" . xa));

fresh_variable_addition ::
  forall a b c d e.
    (Shows_Literal.Showl a, Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Eq b, Shows_Literal.Showl b, Eq c, Shows_Literal.Showl c,
      Shows_Literal.Showl d, Collection_Order.Ccompare e, Eq e,
      Mapping_Impl.Mapping_impl e,
      Shows_Literal.Showl e) => (a -> ([b], b)) ->
                                  Set.Set b ->
                                    (LTS.Trans_var c ->
                                      b ->
Formula.Formula (Term.Term a (LTS.Trans_var c, b)) ->
  Sum_Type.Sum (String -> String) ()) ->
                                      (Term.Term a (LTS.Trans_var c, b) ->
String -> String) ->
LTS.Lts_impl a c b d e ->
  Fresh_variable_addition_info a c b e ->
    Sum_Type.Sum (String -> String) (LTS.Lts_impl a c b d e);
fresh_variable_addition type_of_fun bool_types definability_checker sa2 p
  (Fresh_Variable_Addition_Info x ty forms) =
  let {
    m = Mapping.of_alist forms;
    f = Mapping.lookup_default (Formula.Conjunction []) m;
  } in (case Error_Monad.catch_error
               (Error_Monad.bind
                 (Error_Monad.catch_error
                   (Error_Monad.forallM
                     (\ fa ->
                       Check_Monad.check
                         (Formula.formula
                           (Formula.is_bool type_of_fun bool_types) fa)
                         (Formula.showsl_formulaa fa .
                           Shows_Literal.showsl_lit " is not a valid formula"))
                     (map snd forms))
                   (\ xa -> Sum_Type.Inl (snd xa)))
                 (\ _ ->
                   fresh_variable_checker type_of_fun bool_types
                     definability_checker sa2 p f x ty))
               (\ xa ->
                 Sum_Type.Inl
                   (((Shows_Literal.showsl_lit
                        "problem in adding fresh variable " .
                       Shows_Literal.showsl x) .
                      Shows_Literal.showsl_literal "\n") .
                     xa))
         of {
         Sum_Type.Inl a -> Sum_Type.Inl a;
         Sum_Type.Inr _ -> Sum_Type.Inr (LTS.refine_transition_formulas p f);
       });

}
