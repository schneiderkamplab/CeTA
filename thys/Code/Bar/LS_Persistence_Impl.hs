{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module LS_Persistence_Impl(check_persistence_cr, check_persistence_not_cr)
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
import qualified Litsim_Trs_Impl;
import qualified Check_Monad;
import qualified Transitive_Closure_List_Impl;
import qualified Trs_Impl_More;
import qualified Error_Monad;
import qualified HOL;
import qualified Sum_Type;
import qualified Term_Rewriting;
import qualified Mapping;
import qualified Shows_Literal;
import qualified Arith;

mk_sigF ::
  forall a b. (Eq a) => [(a, ([b], b))] -> (a, Arith.Nat) -> Maybe ([b], b);
mk_sigF sig (f, a) =
  Arith.map_option snd
    (Arith.find
      (\ (fa, (tys, _)) -> f == fa && Arith.equal_nat a (Arith.size_list tys))
      sig);

annotate_term ::
  forall a b c.
    (Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl c) => ((a, Arith.Nat) -> Maybe ([b], b)) ->
                                  b -> Term_Rewriting.Term a c ->
 Sum_Type.Sum (String -> String) (Term_Rewriting.Term a (c, b));
annotate_term sigF alpha (Term_Rewriting.Var x) =
  Sum_Type.Inr (Term_Rewriting.Var (x, alpha));
annotate_term sigF alpha (Term_Rewriting.Fun f ts) =
  (case sigF (f, Arith.size_list ts) of {
    Nothing ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "persistent decomposition: no signature for symbol " .
          Shows_Literal.showsl f);
    Just (tys, ty) ->
      (if not (alpha == ty)
        then Sum_Type.Inl
               (((Shows_Literal.showsl_lit "persistent decomposition: " .
                   Shows_Literal.showsl f) .
                  Shows_Literal.showsl_lit " has wrong type in ") .
                 Term_Rewriting.showsl_terma (Term_Rewriting.Fun f ts))
        else Error_Monad.bind
               (Error_Monad.mapM (\ (a, b) -> annotate_term sigF a b)
                 (zip tys ts))
               (\ tsa -> Sum_Type.Inr (Term_Rewriting.Fun f tsa)));
  });

annotate_terma ::
  forall a b c.
    (Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl c) => ((a, Arith.Nat) -> Maybe ([b], b)) ->
                                  Term_Rewriting.Term a c ->
                                    Sum_Type.Sum (String -> String)
                                      (b, Term_Rewriting.Term a (c, b));
annotate_terma sigF t =
  (case Term_Rewriting.root t of {
    Nothing -> Sum_Type.Inl id;
    Just fn ->
      (case sigF fn of {
        Nothing ->
          Sum_Type.Inl
            (Shows_Literal.showsl_lit
               "persistent decomposition: no signature for symbol " .
              Shows_Literal.showsl_prod fn);
        Just (_, alpha) ->
          Error_Monad.bind (annotate_term sigF alpha t)
            (\ ta -> Sum_Type.Inr (alpha, ta));
      });
  });

check_rule ::
  forall a b c.
    (Eq a, Shows_Literal.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b, Shows_Literal.Showl b, Arith.Ccompare c, Eq c,
      Mapping.Mapping_impl c,
      Shows_Literal.Showl c) => ((a, Arith.Nat) -> Maybe ([b], b)) ->
                                  (Term_Rewriting.Term a c,
                                    Term_Rewriting.Term a c) ->
                                    Sum_Type.Sum (String -> String)
                                      (Term_Rewriting.Term a (c, b),
Term_Rewriting.Term a (c, b));
check_rule sigF rl =
  (case rl of {
    (l, r) ->
      Error_Monad.bind (annotate_terma sigF l)
        (\ (alpha, la) ->
          Error_Monad.bind (annotate_term sigF alpha r)
            (\ ra ->
              Error_Monad.bind
                (Error_Monad.catch_error
                  (Trs_Impl_More.check_variants_rule
                    (Term_Rewriting.map_term (\ x -> x) (\ x -> (x, alpha)) l,
                      Term_Rewriting.map_term (\ x -> x) (\ x -> (x, alpha)) r)
                    (la, ra))
                  (\ _ ->
                    Sum_Type.Inl
                      (Shows_Literal.showsl_lit
                         "persistent decomposition: inconsistent types of variables in rule " .
                        Term_Rewriting.showsl_rule (l, r))))
                (\ _ -> Sum_Type.Inr (la, ra))));
  });

sig_is_clean ::
  forall a b.
    (Eq a, Shows_Literal.Showl a,
      Shows_Literal.Showl b) => [(a, ([b], b))] -> Bool;
sig_is_clean sig =
  Arith.distinct (map (\ (f, (tys, _)) -> (f, Arith.size_list tys)) sig);

type_of_rule ::
  forall a b c d e.
    ((a, Arith.Nat) -> Maybe (b, c)) -> (Term_Rewriting.Term a d, e) -> c;
type_of_rule sigF r =
  snd (Arith.the (sigF (Arith.the (Term_Rewriting.root (fst r)))));

maximal_types_loop :: forall a. (Eq a) => (a -> [a]) -> [a] -> [a];
maximal_types_loop nt [] = [];
maximal_types_loop nt (beta : tys) =
  let {
    mt = maximal_types_loop nt tys;
    nt_beta = nt beta;
  } in (if any (\ alpha -> Arith.membera (nt alpha) beta) mt then mt
         else beta : filter (\ alpha -> not (Arith.membera nt_beta alpha)) mt);

maximal_types ::
  forall a b.
    (Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => [(a, ([b], b))] -> (b -> [b]) -> [b];
maximal_types sig nt = maximal_types_loop nt (map (snd . snd) sig);

sigF_arcs_code ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => [(a, ([b], b))] -> [(b, b)];
sigF_arcs_code sig =
  concatMap (\ (_, (tys, ty)) -> map (\ a -> (ty, a)) tys) sig;

needed_types_code ::
  forall a b.
    (Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => [(a, ([b], b))] -> b -> [b];
needed_types_code sig =
  Transitive_Closure_List_Impl.memo_list_rtrancl (sigF_arcs_code sig);

check_persistence1 ::
  forall a b c d.
    (Eq a, Shows_Literal.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b, Shows_Literal.Showl b, Arith.Ccompare c, Eq c,
      Mapping.Mapping_impl c, Shows_Literal.Showl c, Arith.Ccompare d, Eq d,
      Mapping.Mapping_impl d,
      Shows_Literal.Showl d) => [(a, ([b], b))] ->
                                  [(Term_Rewriting.Term a c,
                                     Term_Rewriting.Term a c)] ->
                                    [[(Term_Rewriting.Term a d,
Term_Rewriting.Term a d)]] ->
                                      Sum_Type.Sum (String -> String)
([(Term_Rewriting.Term a (c, b), Term_Rewriting.Term a (c, b))],
  [[(Term_Rewriting.Term a (d, b), Term_Rewriting.Term a (d, b))]]);
check_persistence1 sig r rs =
  Error_Monad.bind
    (Check_Monad.check (sig_is_clean sig)
      (Shows_Literal.showsl_lit
        "persistent decomposition: duplicate function symbol in signature"))
    (\ _ ->
      Error_Monad.bind (Term_Rewriting.check_wf_trs r)
        (\ _ ->
          Error_Monad.bind (Error_Monad.mapM Term_Rewriting.check_wf_trs rs)
            (\ _ ->
              let {
                sigF = mk_sigF sig;
              } in Error_Monad.bind (Error_Monad.mapM (check_rule sigF) r)
                     (\ ra ->
                       Error_Monad.bind
                         (Error_Monad.mapM (Error_Monad.mapM (check_rule sigF))
                           rs)
                         (\ rsa -> Sum_Type.Inr (ra, rsa))))));

check_persistence_cr ::
  forall a b c.
    (Eq a, Shows_Literal.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b, Shows_Literal.Showl b, Arith.Ccompare c, Eq c,
      Mapping.Mapping_impl c,
      Shows_Literal.Showl c) => [(a, ([b], b))] ->
                                  [(Term_Rewriting.Term a c,
                                     Term_Rewriting.Term a c)] ->
                                    [[(Term_Rewriting.Term a c,
Term_Rewriting.Term a c)]] ->
                                      Sum_Type.Sum (String -> String) ();
check_persistence_cr sig r rs =
  Error_Monad.bind (check_persistence1 sig r rs)
    (\ (ra, rsa) ->
      let {
        sigF = mk_sigF sig;
        needed_types = needed_types_code sig;
        types = maximal_types sig needed_types;
      } in Error_Monad.catch_error
             (Error_Monad.forallM
               (\ ty ->
                 let {
                   s = filter
                         (\ rb ->
                           Arith.membera (needed_types ty)
                             (type_of_rule sigF rb))
                         ra;
                 } in Error_Monad.catch_error
                        (Error_Monad.existsM
                          (Litsim_Trs_Impl.check_litsim_trs s) ([] : rsa))
                        (\ _ ->
                          Sum_Type.Inl
                            ((((Shows_Literal.showsl_lit
                                  "persistent decomposition: missing system induced by sort " .
                                 Shows_Literal.showsl ty) .
                                Shows_Literal.showsl_lit ":") .
                               Shows_Literal.showsl_literal "\n") .
                              Term_Rewriting.showsl_trs
                                (map (\ (l, rb) ->
                                       (Term_Rewriting.map_term (\ x -> x) snd
  l,
 Term_Rewriting.map_term (\ x -> x) snd rb))
                                  s))))
               types)
             (\ x -> Sum_Type.Inl (snd x)));

check_persistence_not_cr ::
  forall a b c.
    (Eq a, Shows_Literal.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b, Shows_Literal.Showl b, Arith.Ccompare c, Eq c,
      Mapping.Mapping_impl c,
      Shows_Literal.Showl c) => [(a, ([b], b))] ->
                                  [(Term_Rewriting.Term a c,
                                     Term_Rewriting.Term a c)] ->
                                    [(Term_Rewriting.Term a c,
                                       Term_Rewriting.Term a c)] ->
                                      Sum_Type.Sum (String -> String) ();
check_persistence_not_cr sig r s =
  Error_Monad.bind (check_persistence1 sig r [s])
    (\ (ra, ss) ->
      let {
        sigF = mk_sigF sig;
        types = map (snd . snd) sig;
        needed_types = needed_types_code sig;
      } in Error_Monad.catch_error
             (Error_Monad.existsM
               (\ sa -> Litsim_Trs_Impl.check_litsim_trs sa (Arith.hda ss))
               (map (\ ty ->
                      let {
                        tys = needed_types ty;
                      } in filter
                             (\ rb -> Arith.membera tys (type_of_rule sigF rb))
                             ra)
                 types))
             (\ _ ->
               Sum_Type.Inl
                 ((Shows_Literal.showsl_lit
                     "persistent decomposition: new system is not induced by any type:" .
                    Shows_Literal.showsl_literal "\n") .
                   Term_Rewriting.showsl_trs s)));

}
