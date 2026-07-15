{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Monadic_Rewriting_Impl(Const_string_sound_proof(..),
                          Const_string_complete_proof(..),
                          const_to_string_sound_tt, const_to_string_complete_tt)
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
import qualified Termination_Problem_Spec;
import qualified Monadic_Rewriting;
import qualified HOL;
import qualified Map_Choice;
import qualified Map;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Shows_Literal;
import qualified Arith;
import qualified Term_Rewriting;

data Const_string_sound_proof a b =
  Const_string_sound_proof b [(a, a)]
    [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];

data Const_string_complete_proof a b =
  Const_string_complete_proof b [(a, a)]
    [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];

choose_var :: forall a b. a -> Term_Rewriting.Term b a -> a;
choose_var x l = Arith.hda (Term_Rewriting.vars_term_list l ++ [x]);

check_components ::
  forall a.
    (Eq a,
      Shows_Literal.Showl a) => [(a, Arith.Nat)] ->
                                  (a -> a, (a -> a, [a])) ->
                                    Sum_Type.Sum (String -> String) ();
check_components mu ddNU =
  (case ddNU of {
    (d, (da, nu)) ->
      Error_Monad.bind
        (Error_Monad.catch_error
          (Error_Monad.forallM
            (\ f ->
              Error_Monad.bind
                (Check_Monad.check (not (Arith.membera mu (f, Arith.one_nat)))
                  ((Shows_Literal.showsl_lit "new unary symbol " .
                     Shows_Literal.showsl f) .
                    Shows_Literal.showsl_lit " clashes with old symbol"))
                (\ _ ->
                  Error_Monad.bind
                    (Check_Monad.check (d (da f) == f)
                      (Shows_Literal.showsl_lit
                         "problem with bijection for renaming of " .
                        Shows_Literal.showsl f))
                    (\ _ ->
                      Check_Monad.check
                        (Arith.membera mu (da f, Arith.zero_nat))
                        (Shows_Literal.showsl_lit
                           "problem with inverse renaming of " .
                          Shows_Literal.showsl f))))
            nu)
          (\ x -> Sum_Type.Inl (snd x)))
        (\ _ ->
          Error_Monad.catch_error
            (Error_Monad.forallM
              (\ (f, n) ->
                Error_Monad.bind
                  (Check_Monad.check (Arith.less_eq_nat n Arith.one_nat)
                    (Shows_Literal.showsl_lit "arity > 1 for symbol " .
                      Shows_Literal.showsl f))
                  (\ _ ->
                    Check_Monad.check
                      (if Arith.equal_nat n Arith.zero_nat
                        then Arith.membera nu (d f) && da (d f) == f else True)
                      (Shows_Literal.showsl_lit
                         "problem with bijection for renaming of constant " .
                        Shows_Literal.showsl f)))
              mu)
            (\ x -> Sum_Type.Inl (snd x)));
  });

extract_renamings :: forall a. (Eq a) => [(a, a)] -> (a -> a, a -> a);
extract_renamings old_new =
  (Map_Choice.fun_of_map_fun (Map.map_of old_new) id,
    Map_Choice.fun_of_map_fun (Map.map_of (map Arith.swap old_new)) id);

extract_components ::
  forall a. (Eq a) => [(a, Arith.Nat)] -> [(a, a)] -> (a -> a, (a -> a, [a]));
extract_components mu old_new =
  (case extract_renamings old_new of {
    (d, da) ->
      let {
        c = Arith.map_filter
              (\ x ->
                (if (case x of {
                      (_, a) -> Arith.equal_nat a Arith.zero_nat;
                    })
                  then Just (fst x) else Nothing))
              mu;
        nu = map d c;
      } in (d, (da, nu));
  });

check_to_srs_sound ::
  forall a b.
    (Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a, Eq a, Arith.Set_impl a,
      Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => a -> [(b, b)] ->
                                       [(Term_Rewriting.Term b a,
  Term_Rewriting.Term b a)] ->
 [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
   [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
     [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
       Sum_Type.Sum (String -> String) ();
check_to_srs_sound v old_new r s rw sw =
  let {
    mu = Term_Rewriting.funas_trs_list (r ++ rw);
  } in (case extract_components mu old_new of {
         (d, (da, nu)) ->
           Error_Monad.bind (check_components mu (d, (da, nu)))
             (\ _ ->
               Error_Monad.bind (Term_Rewriting.check_varcond_subset r)
                 (\ _ ->
                   Error_Monad.bind (Term_Rewriting.check_varcond_subset rw)
                     (\ _ ->
                       let {
                         check =
                           (\ ra sa ->
                             Error_Monad.catch_error
                               (Error_Monad.forallM
                                 (\ (l, rb) ->
                                   let {
                                     y = choose_var v l;
                                     str = Monadic_Rewriting.str d y;
                                     slr = (str l, str rb);
                                   } in Check_Monad.check
  (Arith.less_eq_set (Term_Rewriting.vars_term l)
     (Arith.insert y Arith.bot_set) &&
    Arith.membera sa slr)
  (Shows_Literal.showsl_lit "problem with new rule " .
    Term_Rewriting.showsl_rule slr))
                                 ra)
                               (\ x -> Sum_Type.Inl (snd x)));
                       } in Error_Monad.bind (check r s)
                              (\ _ -> check rw sw))));
       });

check_to_srs_complete ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => a -> [(b, b)] ->
                                       [(Term_Rewriting.Term b a,
  Term_Rewriting.Term b a)] ->
 [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
   Sum_Type.Sum (String -> String) ();
check_to_srs_complete v old_new r s =
  let {
    mu = Term_Rewriting.funas_trs_list r;
  } in (case extract_components mu old_new of {
         (d, (da, nu)) ->
           Error_Monad.bind (check_components mu (d, (da, nu)))
             (\ _ ->
               Error_Monad.bind (Term_Rewriting.check_varcond_subset s)
                 (\ _ ->
                   Error_Monad.catch_error
                     (Error_Monad.forallM
                       (\ slr ->
                         let {
                           y = choose_var v (fst slr);
                           str = Monadic_Rewriting.str d y;
                           to_slr = (\ (l, ra) -> (str l, str ra));
                         } in Check_Monad.check
                                (any (\ lr -> to_slr lr == slr) r)
                                (Shows_Literal.showsl_lit
                                   "could not find original rule for " .
                                  Term_Rewriting.showsl_rule slr))
                       s)
                     (\ x -> Sum_Type.Inl (snd x))));
       });

const_to_string_sound_tt ::
  forall a b c.
    (Eq a, Shows_Literal.Showl a, Arith.Cenum b, Arith.Ceq b, Arith.Ccompare b,
      Eq b, Arith.Set_impl b,
      Shows_Literal.Showl b) => Const_string_sound_proof a b ->
                                  Termination_Problem_Spec.Tp_ops_ext c a b
                                    () ->
                                    c -> Sum_Type.Sum (String -> String) c;
const_to_string_sound_tt (Const_string_sound_proof v old_new s) i tp =
  Error_Monad.bind
    (check_to_srs_sound v old_new (Termination_Problem_Spec.r i tp) s
      (Termination_Problem_Spec.rw i tp) [])
    (\ _ -> Sum_Type.Inr (Termination_Problem_Spec.mk i False [] s []));

const_to_string_complete_tt ::
  forall a b c d.
    (Eq b, Shows_Literal.Showl b, Eq c,
      Shows_Literal.Showl c) => Termination_Problem_Spec.Tp_ops_ext a b c d ->
                                  a -> Const_string_complete_proof b c ->
 Sum_Type.Sum (String -> String) a;
const_to_string_complete_tt i tp (Const_string_complete_proof v old_new s) =
  Error_Monad.bind
    (Check_Monad.check (Termination_Problem_Spec.q_empty i tp)
      (Shows_Literal.showsl_lit "Q is not empty"))
    (\ _ ->
      Error_Monad.bind
        (check_to_srs_complete v old_new (Termination_Problem_Spec.rules i tp)
          s)
        (\ _ -> Sum_Type.Inr (Termination_Problem_Spec.mk i False [] s [])));

}
