{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Unraveling_Impl(split_if, check_unraveling, check_sp_unraveling) where {

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
import qualified Unraveling;
import qualified Option_Monad;
import qualified Map;
import qualified HOL;
import qualified Conditional_Rewriting_Impl;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Arith;
import qualified Shows_Literal;
import qualified Term_Rewriting;

check_prefix_equivalent ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => ((Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b),
                                  [(Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b)]) ->
                                  ((Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b),
                                    [(Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b)]) ->
                                    Arith.Nat ->
                                      Sum_Type.Sum (String -> String) ();
check_prefix_equivalent rhoa rho n =
  Error_Monad.catch_error
    (Error_Monad.bind
      (Check_Monad.check (Arith.less_nat n (Arith.size_list (snd rhoa)))
        (((Shows_Literal.showsl_lit "There are fewer than " .
            Shows_Literal.showsl_nat n) .
           Shows_Literal.showsl_lit " conditions in ") .
          Conditional_Rewriting_Impl.showsl_crule rhoa))
      (\ _ ->
        Error_Monad.bind
          (Check_Monad.check (Arith.less_nat n (Arith.size_list (snd rho)))
            (((Shows_Literal.showsl_lit "There are fewer than " .
                Shows_Literal.showsl_nat n) .
               Shows_Literal.showsl_lit " conditions in ") .
              Conditional_Rewriting_Impl.showsl_crule rho))
          (\ _ ->
            Error_Monad.bind
              (Check_Monad.check
                (Term_Rewriting.equal_term (fst (fst rhoa)) (fst (fst rho)))
                (Shows_Literal.showsl_lit "Left-hand sides are different."))
              (\ _ ->
                Error_Monad.bind
                  (Error_Monad.catch_error
                    (Error_Monad.forallM
                      (\ i ->
                        Check_Monad.check
                          (Term_Rewriting.equal_term
                            (snd (Arith.nth (snd rhoa) i))
                            (snd (Arith.nth (snd rho) i)))
                          (Shows_Literal.showsl_lit
                            "Rhs of conditions are different\n"))
                      (Arith.upt Arith.zero_nat n))
                    (\ x -> Sum_Type.Inl (snd x)))
                  (\ _ ->
                    Error_Monad.catch_error
                      (Error_Monad.forallM
                        (\ i ->
                          Check_Monad.check
                            (Term_Rewriting.equal_term
                              (fst (Arith.nth (snd rhoa) i))
                              (fst (Arith.nth (snd rho) i)))
                            (Shows_Literal.showsl_lit
                              "Lhs of conditions are different\n"))
                        (Arith.upt Arith.zero_nat (Arith.suc n)))
                      (\ x -> Sum_Type.Inl (snd x)))))))
    (\ x ->
      Sum_Type.Inl
        (((((((Shows_Literal.showsl_lit "Rules" .
                Conditional_Rewriting_Impl.showsl_crule rhoa) .
               Shows_Literal.showsl_lit " and ") .
              Conditional_Rewriting_Impl.showsl_crule rho) .
             Shows_Literal.showsl_lit " are not ") .
            Shows_Literal.showsl_nat n) .
           Shows_Literal.showsl_lit " equivalent.\n") .
          x));

check_f ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => ((Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b),
                                  [(Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b)]) ->
                                  Arith.Nat ->
                                    a -> [((Term_Rewriting.Term a b,
     Term_Rewriting.Term a b),
    [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)])] ->
   (((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]) ->
     Arith.Nat -> Term_Rewriting.Actxt a (Term_Rewriting.Term a b)) ->
     Sum_Type.Sum (String -> String) ();
check_f cr j f crs u =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ cra ->
        Error_Monad.catch_error
          (Error_Monad.forallM
            (\ i ->
              (case u cra i of {
                Term_Rewriting.Hole -> Sum_Type.Inr ();
                Term_Rewriting.More g _ _ _ ->
                  (if f == g
                    then Error_Monad.catch_error
                           (Error_Monad.bind
                             (Check_Monad.check (Arith.equal_nat i j)
                               (Shows_Literal.showsl_lit
                                 "Same symbol occurs at different levels\n"))
                             (\ _ ->
                               Error_Monad.bind
                                 (Error_Monad.catch_error
                                   (Error_Monad.forallM
                                     (\ k ->
                                       Check_Monad.check
 (Term_Rewriting.equal_actxt (u cra k) (u cr k))
 (Shows_Literal.showsl_lit "Contexts are different\n"))
                                     (Arith.upt Arith.zero_nat (Arith.suc j)))
                                   (\ x -> Sum_Type.Inl (snd x)))
                                 (\ _ -> check_prefix_equivalent cra cr j)))
                           (\ x ->
                             Sum_Type.Inl
                               (((((Shows_Literal.showsl_lit "Rules" .
                                     Conditional_Rewriting_Impl.showsl_crule
                                       cra) .
                                    Shows_Literal.showsl_lit " and ") .
                                   Conditional_Rewriting_Impl.showsl_crule cr) .
                                  Shows_Literal.showsl_lit
                                    " share a symbol.\n") .
                                 x))
                    else Sum_Type.Inr ());
              }))
            (Arith.upt Arith.zero_nat (Arith.size_list (snd cra))))
          (\ x -> Sum_Type.Inl (snd x)))
      crs)
    (\ x -> Sum_Type.Inl (snd x));

create_ctxts ::
  forall a b.
    [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
      Maybe (Arith.Nat -> Term_Rewriting.Actxt a (Term_Rewriting.Term a b));
create_ctxts r =
  (case r of {
    [] -> Nothing;
    _ : rr ->
      Arith.bind
        (Option_Monad.mapM
          (\ a ->
            (case a of {
              (Term_Rewriting.Var _, _) -> Nothing;
              (Term_Rewriting.Fun _ [], _) -> Nothing;
              (Term_Rewriting.Fun u (_ : ts), _) ->
                Just (Term_Rewriting.More u [] Term_Rewriting.Hole ts);
            }))
          rr)
        (\ cs ->
          let {
            _ = Arith.size_list cs;
          } in Just (\ i ->
                      (if Arith.less_nat i (Arith.size_list cs)
                        then Arith.nth cs i else Term_Rewriting.Hole)));
  });

create_U ::
  forall a b.
    (Eq a,
      Eq b) => [(((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                   [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]),
                  [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)])] ->
                 Maybe (((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                          [(Term_Rewriting.Term a b,
                             Term_Rewriting.Term a b)]) ->
                         Arith.Nat ->
                           Term_Rewriting.Actxt a (Term_Rewriting.Term a b));
create_U c_rs =
  Arith.bind
    (Option_Monad.mapM
      (\ (cr, rs) ->
        Arith.bind
          (Option_Monad.guard
            (Arith.equal_nat (Arith.size_list rs)
              (Arith.suc (Arith.size_list (snd cr)))))
          (\ _ -> Arith.bind (create_ctxts rs) (\ ctxt -> Just (cr, ctxt))))
      c_rs)
    (\ cr_ctxts ->
      let {
        m = Map.map_of cr_ctxts;
      } in Just (\ cr -> (case m cr of {
                           Nothing -> (\ _ -> Term_Rewriting.Hole);
                           Just ctxt -> ctxt;
                         })));

create_zs ::
  forall a b.
    [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
      Maybe (Arith.Nat -> [b]);
create_zs r =
  (case r of {
    [] -> Nothing;
    _ : rr ->
      Arith.bind
        (Option_Monad.mapM
          (\ a ->
            (case a of {
              (Term_Rewriting.Var _, _) -> Nothing;
              (Term_Rewriting.Fun _ [], _) -> Nothing;
              (Term_Rewriting.Fun _ (_ : ts), _) ->
                Just (map Term_Rewriting.the_Var ts);
            }))
          rr)
        (\ cs ->
          Just (\ i ->
                 (if Arith.less_nat i (Arith.size_list cs) then Arith.nth cs i
                   else [])));
  });

create_Z ::
  forall a b.
    (Eq a,
      Eq b) => [(((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                   [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]),
                  [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)])] ->
                 Maybe (((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                          [(Term_Rewriting.Term a b,
                             Term_Rewriting.Term a b)]) ->
                         Arith.Nat -> [b]);
create_Z c_rs =
  Arith.bind
    (Option_Monad.mapM
      (\ (cr, rs) -> Arith.bind (create_zs rs) (\ zs -> Just (cr, zs))) c_rs)
    (\ cr_zs -> let {
                  mc = Map.map_of cr_zs;
                } in Just (\ cr -> (case mc cr of {
                                     Nothing -> (\ _ -> []);
                                     Just zs -> zs;
                                   })));

create_U_s ::
  forall a b.
    (Eq a,
      Eq b) => [(((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                   [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]),
                  (a, [Term_Rewriting.Term a b]))] ->
                 ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                   [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]) ->
                   Maybe (a, [Term_Rewriting.Term a b]);
create_U_s ls rule = (case Arith.find (\ x -> fst x == rule) ls of {
                       Nothing -> Nothing;
                       Just (_, a) -> Just a;
                     });

rules_impl_s ::
  forall a b.
    (((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
       [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]) ->
      Maybe (a, [Term_Rewriting.Term a b])) ->
      ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
        [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]) ->
        [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
rules_impl_s u crule =
  (case u crule of {
    Nothing -> [fst crule];
    Just (f, ctxt) ->
      let {
        conds = snd crule;
        lr = fst crule;
      } in (if null conds then [lr]
             else [(fst lr, Term_Rewriting.Fun f (map fst conds ++ ctxt)),
                    (Term_Rewriting.Fun f (map snd conds ++ ctxt), snd lr)]);
  });

uR_impl_s ::
  forall a b.
    (((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
       [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]) ->
      Maybe (a, [Term_Rewriting.Term a b])) ->
      [((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
         [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)])] ->
        [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
uR_impl_s u r = concatMap (rules_impl_s u) r;

split_if ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => (Term_Rewriting.Term a b,
                                  (Term_Rewriting.Term a b,
                                    [(((Term_Rewriting.Term a b,
 Term_Rewriting.Term a b),
[(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]),
                                       (a, [Term_Rewriting.Term a b]))])) ->
                                  [((Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b),
                                     [(Term_Rewriting.Term a b,
Term_Rewriting.Term a b)])] ->
                                    [(Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b)] ->
                                      [(Term_Rewriting.Term a b,
 Term_Rewriting.Term a b)];
split_if p r cs = (case p of {
                    (_, (_, u)) -> uR_impl_s (create_U_s u) r;
                  });

rules_impl ::
  forall a b.
    (((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
       [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]) ->
      Arith.Nat -> Term_Rewriting.Actxt a (Term_Rewriting.Term a b)) ->
      ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
        [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]) ->
        [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
rules_impl u cr =
  map (\ i -> (Unraveling.lhs_n u cr i, Unraveling.rhs_n u cr i))
    (Arith.upt Arith.zero_nat (Arith.suc (Arith.size_list (snd cr))));

create_Umap_cr ::
  forall a b.
    ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]) ->
      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
        Maybe [(a, (((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                      [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]),
                     Arith.Nat))];
create_Umap_cr cr r =
  (case r of {
    [] -> Nothing;
    _ : rr ->
      Option_Monad.mapM
        (\ (a, b) ->
          (case a of {
            (l, _) ->
              (\ i -> (case l of {
                        Term_Rewriting.Var _ -> Nothing;
                        Term_Rewriting.Fun _ [] -> Nothing;
                        Term_Rewriting.Fun u (_ : _) -> Just (u, (cr, i));
                      }));
          })
            b)
        (zip rr (Arith.upt Arith.zero_nat (Arith.size_list rr)));
  });

create_Umap ::
  forall a b.
    (Eq a) => [(((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                  [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]),
                 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)])] ->
                a -> Maybe (((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                              [(Term_Rewriting.Term a b,
                                 Term_Rewriting.Term a b)]),
                             Arith.Nat);
create_Umap c_rs =
  (case Option_Monad.mapM (\ (a, b) -> create_Umap_cr a b) c_rs of {
    Nothing -> (\ _ -> Nothing);
    Just u -> Map.map_of (concat u);
  });

check_U_cond ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => (((Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b),
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)]) ->
                                  Arith.Nat ->
                                    Term_Rewriting.Actxt a
                                      (Term_Rewriting.Term a b)) ->
                                  [((Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b),
                                     [(Term_Rewriting.Term a b,
Term_Rewriting.Term a b)])] ->
                                    [a] ->
                                      (((Term_Rewriting.Term a b,
  Term_Rewriting.Term a b),
 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]) ->
Arith.Nat -> [b]) ->
Sum_Type.Sum (String -> String) ();
check_U_cond u crs f z =
  Error_Monad.catch_error
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ cr ->
          Error_Monad.catch_error
            (Error_Monad.forallM
              (\ i ->
                (case u cr i of {
                  Term_Rewriting.Hole ->
                    Sum_Type.Inl
                      (Shows_Literal.showsl_lit " Unexpected empty context.");
                  Term_Rewriting.More fa [] Term_Rewriting.Hole aft ->
                    Error_Monad.catch_error
                      (Error_Monad.bind
                        (Error_Monad.catch_error
                          (Check_Monad.check_disjoint [fa] f)
                          (\ _ ->
                            Sum_Type.Inl
                              ((Shows_Literal.showsl_lit
                                  "The function symbol " .
                                 Shows_Literal.showsl fa) .
                                Shows_Literal.showsl_lit " is not fresh.\n")))
                        (\ _ ->
                          Error_Monad.bind
                            (Check_Monad.check
                              (aft == map Term_Rewriting.Var (z cr i))
                              (Shows_Literal.showsl_lit
                                " U does not map to Z vars "))
                            (\ _ -> check_f cr i fa crs u)))
                      (\ x ->
                        Sum_Type.Inl
                          (((((Shows_Literal.showsl_lit "Conditions for " .
                                Conditional_Rewriting_Impl.showsl_crule cr) .
                               Shows_Literal.showsl_lit " at  ") .
                              Shows_Literal.showsl_nat i) .
                             Shows_Literal.showsl_lit " are violated.\n") .
                            x));
                  Term_Rewriting.More _ [] (Term_Rewriting.More _ _ _ _) _ ->
                    Sum_Type.Inl
                      (Shows_Literal.showsl_lit " Unexpected empty context.");
                  Term_Rewriting.More _ (_ : _) _ _ ->
                    Sum_Type.Inl
                      (Shows_Literal.showsl_lit " Unexpected empty context.");
                }))
              (Arith.upt Arith.zero_nat (Arith.size_list (snd cr))))
            (\ x -> Sum_Type.Inl (snd x)))
        crs)
      (\ x -> Sum_Type.Inl (snd x)))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "The CTRS does not fulfill the condition on the U symbols.\n" .
          x));

check_Z_vars ::
  forall a b.
    (Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => [((Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b),
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)])] ->
                                  (((Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b),
                                     [(Term_Rewriting.Term a b,
Term_Rewriting.Term a b)]) ->
                                    Arith.Nat -> [b]) ->
                                    Sum_Type.Sum (String -> String) ();
check_Z_vars crs z =
  Error_Monad.catch_error
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ cr ->
          Error_Monad.catch_error
            (Error_Monad.forallM
              (\ i ->
                Error_Monad.catch_error
                  (Error_Monad.bind
                    (Error_Monad.catch_error
                      (Check_Monad.check_subseteq
                        (Arith.inter_list_set
                          (Conditional_Rewriting_Impl.x_impl cr i)
                          (Conditional_Rewriting_Impl.y_impl cr i))
                        (z cr i))
                      (\ x ->
                        Sum_Type.Inl
                          ((((Shows_Literal.showsl_lit "Variable " .
                               Shows_Literal.showsl x) .
                              Shows_Literal.showsl_lit
                                " does not occur in variable list of ") .
                             Shows_Literal.showsl_nat (Arith.suc i)) .
                            Shows_Literal.showsl_lit ". U-symbol\n")))
                    (\ _ ->
                      Check_Monad.check (Arith.distinct (z cr i))
                        (Shows_Literal.showsl_lit
                          " variables in additional arguments of U-symbols are not distinct.\n")))
                  (\ x ->
                    Sum_Type.Inl
                      (((Shows_Literal.showsl_lit
                           "conditions for variable-lists in U-symbols for " .
                          Conditional_Rewriting_Impl.showsl_crule cr) .
                         Shows_Literal.showsl_lit " are violated.\n") .
                        x)))
              (Arith.upt Arith.zero_nat (Arith.size_list (snd cr))))
            (\ x -> Sum_Type.Inl (snd x)))
        crs)
      (\ x -> Sum_Type.Inl (snd x)))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "The CTRS does not fulfill the condition on Z variables.\n" .
          x));

check_unraveling ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => [(((Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b),
                                    [(Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b)]),
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)])] ->
                                  [((Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b),
                                     [(Term_Rewriting.Term a b,
Term_Rewriting.Term a b)])] ->
                                    Sum_Type.Sum (String -> String)
                                      [(Term_Rewriting.Term a b,
 Term_Rewriting.Term a b)];
check_unraveling c_rs ctrs =
  Error_Monad.catch_error
    (Error_Monad.bind
      (Error_Monad.catch_error (Check_Monad.check_subseteq ctrs (map fst c_rs))
        (\ x ->
          Sum_Type.Inl
            ((Shows_Literal.showsl_lit "did not find rule " .
               Conditional_Rewriting_Impl.showsl_crule x) .
              Shows_Literal.showsl_literal "\n")))
      (\ _ ->
        Error_Monad.bind
          (case create_U c_rs of {
            Nothing ->
              Sum_Type.Inl
                (Shows_Literal.showsl_lit
                  "unable to extract unraveling contexts");
            Just a -> Sum_Type.Inr a;
          })
          (\ u ->
            Error_Monad.bind
              (Error_Monad.catch_error
                (Error_Monad.forallM
                  (\ (c, rs) ->
                    Check_Monad.check (rules_impl u c == rs)
                      ((Shows_Literal.showsl_lit "problem with rules of " .
                         Conditional_Rewriting_Impl.showsl_crule c) .
                        Shows_Literal.showsl_literal "\n"))
                  c_rs)
                (\ x -> Sum_Type.Inl (snd x)))
              (\ _ -> Sum_Type.Inr (concatMap snd c_rs)))))
    (\ x ->
      Sum_Type.Inl (Shows_Literal.showsl_lit "problem in unraveling\n" . x));

check_source_preserving ::
  forall a b.
    (Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => [((Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b),
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)])] ->
                                  (((Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b),
                                     [(Term_Rewriting.Term a b,
Term_Rewriting.Term a b)]) ->
                                    Arith.Nat -> [b]) ->
                                    Sum_Type.Sum (String -> String) ();
check_source_preserving crs zv =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ cr ->
        Error_Monad.catch_error
          (Error_Monad.forallM
            (\ i ->
              Error_Monad.catch_error
                (Error_Monad.catch_error
                  (Check_Monad.check_subseteq
                    (Term_Rewriting.vars_term_list (fst (fst cr))) (zv cr i))
                  (\ _ ->
                    Sum_Type.Inl
                      ((Shows_Literal.showsl_lit
                          "Some variable in lhs does not occur in Z_" .
                         Shows_Literal.showsl_nat i) .
                        Shows_Literal.showsl_lit ". \n")))
                (\ x ->
                  Sum_Type.Inl
                    (((Shows_Literal.showsl_lit
                         "The unraveling is not source preserving for rule " .
                        Conditional_Rewriting_Impl.showsl_crule cr) .
                       Shows_Literal.showsl_literal "\n") .
                      x)))
            (Arith.upt Arith.zero_nat (Arith.size_list (snd cr))))
          (\ x -> Sum_Type.Inl (snd x)))
      crs)
    (\ x -> Sum_Type.Inl (snd x));

check_sp_unraveling ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Arith.Ceq b, Arith.Ccompare b, Eq b,
      Arith.Set_impl b,
      Shows_Literal.Showl b) => [(((Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b),
                                    [(Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b)]),
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)])] ->
                                  [((Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b),
                                     [(Term_Rewriting.Term a b,
Term_Rewriting.Term a b)])] ->
                                    Sum_Type.Sum (String -> String)
                                      [(Term_Rewriting.Term a b,
 Term_Rewriting.Term a b)];
check_sp_unraveling c_rs ctrs =
  Error_Monad.catch_error
    (Error_Monad.bind
      (Error_Monad.catch_error (Check_Monad.check_same_set ctrs (map fst c_rs))
        (\ x ->
          Sum_Type.Inl
            ((Shows_Literal.showsl_lit "did not find rule " .
               Conditional_Rewriting_Impl.showsl_crule x) .
              Shows_Literal.showsl_literal "\n")))
      (\ _ ->
        Error_Monad.bind
          (case create_U c_rs of {
            Nothing ->
              Sum_Type.Inl
                (Shows_Literal.showsl_lit
                  "unable to extract unraveling contexts");
            Just a -> Sum_Type.Inr a;
          })
          (\ u ->
            Error_Monad.bind
              (case create_Z c_rs of {
                Nothing ->
                  Sum_Type.Inl
                    (Shows_Literal.showsl_lit "unable to extract Z variables");
                Just a -> Sum_Type.Inr a;
              })
              (\ z ->
                Error_Monad.bind (Sum_Type.Inr (create_Umap c_rs))
                  (\ _ ->
                    Error_Monad.bind
                      (check_U_cond u ctrs
                        (Conditional_Rewriting_Impl.funs_ctrs_list ctrs) z)
                      (\ _ ->
                        Error_Monad.bind (check_Z_vars ctrs z)
                          (\ _ ->
                            Error_Monad.bind
                              (Conditional_Rewriting_Impl.check_dctrs ctrs)
                              (\ _ ->
                                Error_Monad.bind
                                  (Conditional_Rewriting_Impl.check_type3 ctrs)
                                  (\ _ ->
                                    Error_Monad.bind
                                      (Error_Monad.catch_error
(Error_Monad.forallM
  (\ (c, rs) ->
    Check_Monad.check (rules_impl u c == rs)
      ((Shows_Literal.showsl_lit "problem with rules of " .
         Conditional_Rewriting_Impl.showsl_crule c) .
        Shows_Literal.showsl_literal "\n"))
  c_rs)
(\ x -> Sum_Type.Inl (snd x)))
                                      (\ _ ->
Error_Monad.bind
  (Error_Monad.catch_error
    (Term_Rewriting.check_left_linear_trs (concatMap snd c_rs))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit "the unraveled TRS is not left-linear\n" .
          x)))
  (\ _ ->
    Error_Monad.bind
      (Error_Monad.catch_error (Conditional_Rewriting_Impl.check_wf_ctrs ctrs)
        (\ x ->
          Sum_Type.Inl
            (Shows_Literal.showsl_lit "the CTRS is not well-formed\n" . x)))
      (\ _ ->
        Error_Monad.bind
          (Error_Monad.catch_error (check_source_preserving ctrs z)
            (\ x ->
              Sum_Type.Inl
                (Shows_Literal.showsl_lit
                   "unraveling is not source preserving\n" .
                  x)))
          (\ _ -> Sum_Type.Inr (concatMap snd c_rs))))))))))))))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "preconditions on the unraveling are not satisfied\n" .
          x));

}
