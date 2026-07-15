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
import qualified Check_Monad;
import qualified Error_Monad;
import qualified HOL;
import qualified Sum_Type;
import qualified Arith;
import qualified Term_Rewriting;

data Fresh_variable_addition_info a b c d =
  Fresh_Variable_Addition_Info b c
    [(d, Term_Rewriting.Formula
           (Term_Rewriting.Term a (Term_Rewriting.Trans_var b, c)))];

fresh_variable_checker ::
  forall a b c d e.
    (Term_Rewriting.Showl a, Arith.Ceq b, Arith.Ccompare b, Eq b,
      Term_Rewriting.Showl b, Eq c, Term_Rewriting.Showl c,
      Term_Rewriting.Showl d,
      Term_Rewriting.Showl e) => (a -> ([b], b)) ->
                                   Arith.Set b ->
                                     (Term_Rewriting.Trans_var c ->
                                       b ->
 Term_Rewriting.Formula
   (Term_Rewriting.Term a (Term_Rewriting.Trans_var c, b)) ->
   Sum_Type.Sum (String -> String) ()) ->
                                       (Term_Rewriting.Term a
  (Term_Rewriting.Trans_var c, b) ->
 String -> String) ->
 Term_Rewriting.Lts_impl a c b d e ->
   (e -> Term_Rewriting.Formula
           (Term_Rewriting.Term a (Term_Rewriting.Trans_var c, b))) ->
     c -> b -> Sum_Type.Sum (String -> String) ();
fresh_variable_checker type_of_fun bool_types definability_checker sa2 p f x ty
  = Error_Monad.catch_error
      (Error_Monad.bind
        (Error_Monad.catch_error
          (Error_Monad.forallM
            (\ (l, fa) ->
              Check_Monad.check
                (not (Term_Rewriting.in_vars_formula (x, ty) fa))
                ((Term_Rewriting.showsl x .
                   Term_Rewriting.showsl_lit
                     " is not fresh, it occurs in location condition of ") .
                  Term_Rewriting.showsl l))
            (Term_Rewriting.assertion_impl p))
          (\ xa -> Sum_Type.Inl (snd xa)))
        (\ _ ->
          Error_Monad.catch_error
            (Error_Monad.forallM
              (\ (tr, tau) ->
                let {
                  psi = f tr;
                } in Error_Monad.bind
                       (Check_Monad.check
                         (Term_Rewriting.formula
                           (Term_Rewriting.is_bool type_of_fun bool_types) psi)
                         (Term_Rewriting.showsl_lit
                           "new transition formula seems to be not well-formed"))
                       (\ _ ->
                         Error_Monad.catch_error
                           (case tau of {
                             Term_Rewriting.Transition _ _ phi ->
                               Error_Monad.bind
                                 (definability_checker (Term_Rewriting.Post x)
                                    ty
                                   psi)
                                 (\ _ ->
                                   Error_Monad.bind
                                     (Check_Monad.check
                                       (not
 (Term_Rewriting.in_vars_formula (Term_Rewriting.Post x, ty) phi))
                                       (Term_Rewriting.showsl_lit
  "Post x in transition formula" .
 Term_Rewriting.showsl_formula sa2 phi))
                                     (\ _ ->
                                       Check_Monad.check
 (not (Term_Rewriting.in_vars_formula (Term_Rewriting.Pre x, ty) phi))
 (Term_Rewriting.showsl_lit "Pre x in transition formula" .
   Term_Rewriting.showsl_formula sa2 phi)));
                           })
                           (\ xa ->
                             Sum_Type.Inl
                               (((Term_Rewriting.showsl_lit
                                    "problem in transition formula of transition " .
                                   Term_Rewriting.showsl tr) .
                                  Term_Rewriting.showsl_literal "\n") .
                                 xa))))
              (Term_Rewriting.transitions_impl p))
            (\ xa -> Sum_Type.Inl (snd xa))))
      (\ xa ->
        Sum_Type.Inl
          (Term_Rewriting.showsl_lit "fresh_variable_checker failed\n" . xa));

fresh_variable_addition ::
  forall a b c d e.
    (Term_Rewriting.Showl a, Arith.Ceq b, Arith.Ccompare b, Eq b,
      Term_Rewriting.Showl b, Eq c, Term_Rewriting.Showl c,
      Term_Rewriting.Showl d, Arith.Ccompare e, Eq e, Mapping.Mapping_impl e,
      Term_Rewriting.Showl e) => (a -> ([b], b)) ->
                                   Arith.Set b ->
                                     (Term_Rewriting.Trans_var c ->
                                       b ->
 Term_Rewriting.Formula
   (Term_Rewriting.Term a (Term_Rewriting.Trans_var c, b)) ->
   Sum_Type.Sum (String -> String) ()) ->
                                       (Term_Rewriting.Term a
  (Term_Rewriting.Trans_var c, b) ->
 String -> String) ->
 Term_Rewriting.Lts_impl a c b d e ->
   Fresh_variable_addition_info a c b e ->
     Sum_Type.Sum (String -> String) (Term_Rewriting.Lts_impl a c b d e);
fresh_variable_addition type_of_fun bool_types definability_checker sa2 p
  (Fresh_Variable_Addition_Info x ty forms) =
  let {
    m = Mapping.of_alist forms;
    f = Mapping.lookup_default (Term_Rewriting.Conjunction []) m;
  } in (case Error_Monad.catch_error
               (Error_Monad.bind
                 (Error_Monad.catch_error
                   (Error_Monad.forallM
                     (\ fa ->
                       Check_Monad.check
                         (Term_Rewriting.formula
                           (Term_Rewriting.is_bool type_of_fun bool_types) fa)
                         (Term_Rewriting.showsl_formulaa fa .
                           Term_Rewriting.showsl_lit " is not a valid formula"))
                     (map snd forms))
                   (\ xa -> Sum_Type.Inl (snd xa)))
                 (\ _ ->
                   fresh_variable_checker type_of_fun bool_types
                     definability_checker sa2 p f x ty))
               (\ xa ->
                 Sum_Type.Inl
                   (((Term_Rewriting.showsl_lit
                        "problem in adding fresh variable " .
                       Term_Rewriting.showsl x) .
                      Term_Rewriting.showsl_literal "\n") .
                     xa))
         of {
         Sum_Type.Inl a -> Sum_Type.Inl a;
         Sum_Type.Inr _ ->
           Sum_Type.Inr (Term_Rewriting.refine_transition_formulas p f);
       });

}
