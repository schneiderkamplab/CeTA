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
import qualified Term_More;
import qualified Trs_Impl;
import qualified Collection_Order;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Unraveling;
import qualified Product_Type;
import qualified Option_Monad;
import qualified Option;
import qualified Map;
import qualified HOL;
import qualified Conditional_Rewriting_Impl;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified List;
import qualified Subterm_and_Context;
import qualified Sum_Type;
import qualified Arith;
import qualified Shows_Literal;
import qualified Term;

check_prefix_equivalent ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => ((Term.Term a b, Term.Term a b),
                                  [(Term.Term a b, Term.Term a b)]) ->
                                  ((Term.Term a b, Term.Term a b),
                                    [(Term.Term a b, Term.Term a b)]) ->
                                    Arith.Nat ->
                                      Sum_Type.Sum (String -> String) ();
check_prefix_equivalent rhoa rho n =
  Error_Monad.catch_error
    (Error_Monad.bind
      (Check_Monad.check (Arith.less_nat n (List.size_list (snd rhoa)))
        (((Shows_Literal.showsl_lit "There are fewer than " .
            Shows_Literal.showsl_nat n) .
           Shows_Literal.showsl_lit " conditions in ") .
          Conditional_Rewriting_Impl.showsl_crule rhoa))
      (\ _ ->
        Error_Monad.bind
          (Check_Monad.check (Arith.less_nat n (List.size_list (snd rho)))
            (((Shows_Literal.showsl_lit "There are fewer than " .
                Shows_Literal.showsl_nat n) .
               Shows_Literal.showsl_lit " conditions in ") .
              Conditional_Rewriting_Impl.showsl_crule rho))
          (\ _ ->
            Error_Monad.bind
              (Check_Monad.check
                (Term.equal_term (fst (fst rhoa)) (fst (fst rho)))
                (Shows_Literal.showsl_lit "Left-hand sides are different."))
              (\ _ ->
                Error_Monad.bind
                  (Error_Monad.catch_error
                    (Error_Monad.forallM
                      (\ i ->
                        Check_Monad.check
                          (Term.equal_term (snd (List.nth (snd rhoa) i))
                            (snd (List.nth (snd rho) i)))
                          (Shows_Literal.showsl_lit
                            "Rhs of conditions are different\n"))
                      (List.upt Arith.zero_nat n))
                    (\ x -> Sum_Type.Inl (snd x)))
                  (\ _ ->
                    Error_Monad.catch_error
                      (Error_Monad.forallM
                        (\ i ->
                          Check_Monad.check
                            (Term.equal_term (fst (List.nth (snd rhoa) i))
                              (fst (List.nth (snd rho) i)))
                            (Shows_Literal.showsl_lit
                              "Lhs of conditions are different\n"))
                        (List.upt Arith.zero_nat (Arith.suc n)))
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
      Shows_Literal.Showl b) => ((Term.Term a b, Term.Term a b),
                                  [(Term.Term a b, Term.Term a b)]) ->
                                  Arith.Nat ->
                                    a -> [((Term.Term a b, Term.Term a b),
    [(Term.Term a b, Term.Term a b)])] ->
   (((Term.Term a b, Term.Term a b), [(Term.Term a b, Term.Term a b)]) ->
     Arith.Nat -> Subterm_and_Context.Actxt a (Term.Term a b)) ->
     Sum_Type.Sum (String -> String) ();
check_f cr j f crs u =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ cra ->
        Error_Monad.catch_error
          (Error_Monad.forallM
            (\ i ->
              (case u cra i of {
                Subterm_and_Context.Hole -> Sum_Type.Inr ();
                Subterm_and_Context.More g _ _ _ ->
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
 (Subterm_and_Context.equal_actxt (u cra k) (u cr k))
 (Shows_Literal.showsl_lit "Contexts are different\n"))
                                     (List.upt Arith.zero_nat (Arith.suc j)))
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
            (List.upt Arith.zero_nat (List.size_list (snd cra))))
          (\ x -> Sum_Type.Inl (snd x)))
      crs)
    (\ x -> Sum_Type.Inl (snd x));

create_ctxts ::
  forall a b.
    [(Term.Term a b, Term.Term a b)] ->
      Maybe (Arith.Nat -> Subterm_and_Context.Actxt a (Term.Term a b));
create_ctxts r =
  (case r of {
    [] -> Nothing;
    _ : rr ->
      Option.bind
        (Option_Monad.mapM
          (\ a ->
            (case a of {
              (Term.Var _, _) -> Nothing;
              (Term.Fun _ [], _) -> Nothing;
              (Term.Fun u (_ : ts), _) ->
                Just (Subterm_and_Context.More u [] Subterm_and_Context.Hole
                       ts);
            }))
          rr)
        (\ cs ->
          let {
            _ = List.size_list cs;
          } in Just (\ i ->
                      (if Arith.less_nat i (List.size_list cs)
                        then List.nth cs i else Subterm_and_Context.Hole)));
  });

create_U ::
  forall a b.
    (Eq a,
      Eq b) => [(((Term.Term a b, Term.Term a b),
                   [(Term.Term a b, Term.Term a b)]),
                  [(Term.Term a b, Term.Term a b)])] ->
                 Maybe (((Term.Term a b, Term.Term a b),
                          [(Term.Term a b, Term.Term a b)]) ->
                         Arith.Nat ->
                           Subterm_and_Context.Actxt a (Term.Term a b));
create_U c_rs =
  Option.bind
    (Option_Monad.mapM
      (\ (cr, rs) ->
        Option.bind
          (Option_Monad.guard
            (Arith.equal_nat (List.size_list rs)
              (Arith.suc (List.size_list (snd cr)))))
          (\ _ -> Option.bind (create_ctxts rs) (\ ctxt -> Just (cr, ctxt))))
      c_rs)
    (\ cr_ctxts ->
      let {
        m = Map.map_of cr_ctxts;
      } in Just (\ cr -> (case m cr of {
                           Nothing -> (\ _ -> Subterm_and_Context.Hole);
                           Just ctxt -> ctxt;
                         })));

create_zs ::
  forall a b. [(Term.Term a b, Term.Term a b)] -> Maybe (Arith.Nat -> [b]);
create_zs r =
  (case r of {
    [] -> Nothing;
    _ : rr ->
      Option.bind
        (Option_Monad.mapM
          (\ a -> (case a of {
                    (Term.Var _, _) -> Nothing;
                    (Term.Fun _ [], _) -> Nothing;
                    (Term.Fun _ (_ : ts), _) -> Just (map Term.the_Var ts);
                  }))
          rr)
        (\ cs ->
          Just (\ i ->
                 (if Arith.less_nat i (List.size_list cs) then List.nth cs i
                   else [])));
  });

create_Z ::
  forall a b.
    (Eq a,
      Eq b) => [(((Term.Term a b, Term.Term a b),
                   [(Term.Term a b, Term.Term a b)]),
                  [(Term.Term a b, Term.Term a b)])] ->
                 Maybe (((Term.Term a b, Term.Term a b),
                          [(Term.Term a b, Term.Term a b)]) ->
                         Arith.Nat -> [b]);
create_Z c_rs =
  Option.bind
    (Option_Monad.mapM
      (\ (cr, rs) -> Option.bind (create_zs rs) (\ zs -> Just (cr, zs))) c_rs)
    (\ cr_zs -> let {
                  mc = Map.map_of cr_zs;
                } in Just (\ cr -> (case mc cr of {
                                     Nothing -> (\ _ -> []);
                                     Just zs -> zs;
                                   })));

create_U_s ::
  forall a b.
    (Eq a,
      Eq b) => [(((Term.Term a b, Term.Term a b),
                   [(Term.Term a b, Term.Term a b)]),
                  (a, [Term.Term a b]))] ->
                 ((Term.Term a b, Term.Term a b),
                   [(Term.Term a b, Term.Term a b)]) ->
                   Maybe (a, [Term.Term a b]);
create_U_s ls rule = (case List.find (\ x -> fst x == rule) ls of {
                       Nothing -> Nothing;
                       Just (_, a) -> Just a;
                     });

rules_impl_s ::
  forall a b.
    (((Term.Term a b, Term.Term a b), [(Term.Term a b, Term.Term a b)]) ->
      Maybe (a, [Term.Term a b])) ->
      ((Term.Term a b, Term.Term a b), [(Term.Term a b, Term.Term a b)]) ->
        [(Term.Term a b, Term.Term a b)];
rules_impl_s u crule =
  (case u crule of {
    Nothing -> [fst crule];
    Just (f, ctxt) ->
      let {
        conds = snd crule;
        lr = fst crule;
      } in (if null conds then [lr]
             else [(fst lr, Term.Fun f (map fst conds ++ ctxt)),
                    (Term.Fun f (map snd conds ++ ctxt), snd lr)]);
  });

uR_impl_s ::
  forall a b.
    (((Term.Term a b, Term.Term a b), [(Term.Term a b, Term.Term a b)]) ->
      Maybe (a, [Term.Term a b])) ->
      [((Term.Term a b, Term.Term a b), [(Term.Term a b, Term.Term a b)])] ->
        [(Term.Term a b, Term.Term a b)];
uR_impl_s u r = concatMap (rules_impl_s u) r;

split_if ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => (Term.Term a b,
                                  (Term.Term a b,
                                    [(((Term.Term a b, Term.Term a b),
[(Term.Term a b, Term.Term a b)]),
                                       (a, [Term.Term a b]))])) ->
                                  [((Term.Term a b, Term.Term a b),
                                     [(Term.Term a b, Term.Term a b)])] ->
                                    [(Term.Term a b, Term.Term a b)] ->
                                      [(Term.Term a b, Term.Term a b)];
split_if p r cs = (case p of {
                    (_, (_, u)) -> uR_impl_s (create_U_s u) r;
                  });

rules_impl ::
  forall a b.
    (((Term.Term a b, Term.Term a b), [(Term.Term a b, Term.Term a b)]) ->
      Arith.Nat -> Subterm_and_Context.Actxt a (Term.Term a b)) ->
      ((Term.Term a b, Term.Term a b), [(Term.Term a b, Term.Term a b)]) ->
        [(Term.Term a b, Term.Term a b)];
rules_impl u cr =
  map (\ i -> (Unraveling.lhs_n u cr i, Unraveling.rhs_n u cr i))
    (List.upt Arith.zero_nat (Arith.suc (List.size_list (snd cr))));

create_Umap_cr ::
  forall a b.
    ((Term.Term a b, Term.Term a b), [(Term.Term a b, Term.Term a b)]) ->
      [(Term.Term a b, Term.Term a b)] ->
        Maybe [(a, (((Term.Term a b, Term.Term a b),
                      [(Term.Term a b, Term.Term a b)]),
                     Arith.Nat))];
create_Umap_cr cr r =
  (case r of {
    [] -> Nothing;
    _ : rr ->
      Option_Monad.mapM
        (\ (a, b) ->
          (case a of {
            (l, _) -> (\ i -> (case l of {
                                Term.Var _ -> Nothing;
                                Term.Fun _ [] -> Nothing;
                                Term.Fun u (_ : _) -> Just (u, (cr, i));
                              }));
          })
            b)
        (zip rr (List.upt Arith.zero_nat (List.size_list rr)));
  });

create_Umap ::
  forall a b.
    (Eq a) => [(((Term.Term a b, Term.Term a b),
                  [(Term.Term a b, Term.Term a b)]),
                 [(Term.Term a b, Term.Term a b)])] ->
                a -> Maybe (((Term.Term a b, Term.Term a b),
                              [(Term.Term a b, Term.Term a b)]),
                             Arith.Nat);
create_Umap c_rs =
  (case Option_Monad.mapM (\ (a, b) -> create_Umap_cr a b) c_rs of {
    Nothing -> (\ _ -> Nothing);
    Just u -> Map.map_of (concat u);
  });

check_U_cond ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => (((Term.Term a b, Term.Term a b),
                                   [(Term.Term a b, Term.Term a b)]) ->
                                  Arith.Nat ->
                                    Subterm_and_Context.Actxt a
                                      (Term.Term a b)) ->
                                  [((Term.Term a b, Term.Term a b),
                                     [(Term.Term a b, Term.Term a b)])] ->
                                    [a] ->
                                      (((Term.Term a b, Term.Term a b),
 [(Term.Term a b, Term.Term a b)]) ->
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
                  Subterm_and_Context.Hole ->
                    Sum_Type.Inl
                      (Shows_Literal.showsl_lit " Unexpected empty context.");
                  Subterm_and_Context.More fa [] Subterm_and_Context.Hole aft ->
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
                            (Check_Monad.check (aft == map Term.Var (z cr i))
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
                  Subterm_and_Context.More _ []
                    (Subterm_and_Context.More _ _ _ _) _
                    -> Sum_Type.Inl
                         (Shows_Literal.showsl_lit
                           " Unexpected empty context.");
                  Subterm_and_Context.More _ (_ : _) _ _ ->
                    Sum_Type.Inl
                      (Shows_Literal.showsl_lit " Unexpected empty context.");
                }))
              (List.upt Arith.zero_nat (List.size_list (snd cr))))
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
      Shows_Literal.Showl b) => [((Term.Term a b, Term.Term a b),
                                   [(Term.Term a b, Term.Term a b)])] ->
                                  (((Term.Term a b, Term.Term a b),
                                     [(Term.Term a b, Term.Term a b)]) ->
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
                        (List.inter_list_set
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
                      Check_Monad.check (List.distinct (z cr i))
                        (Shows_Literal.showsl_lit
                          " variables in additional arguments of U-symbols are not distinct.\n")))
                  (\ x ->
                    Sum_Type.Inl
                      (((Shows_Literal.showsl_lit
                           "conditions for variable-lists in U-symbols for " .
                          Conditional_Rewriting_Impl.showsl_crule cr) .
                         Shows_Literal.showsl_lit " are violated.\n") .
                        x)))
              (List.upt Arith.zero_nat (List.size_list (snd cr))))
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
      Shows_Literal.Showl b) => [(((Term.Term a b, Term.Term a b),
                                    [(Term.Term a b, Term.Term a b)]),
                                   [(Term.Term a b, Term.Term a b)])] ->
                                  [((Term.Term a b, Term.Term a b),
                                     [(Term.Term a b, Term.Term a b)])] ->
                                    Sum_Type.Sum (String -> String)
                                      [(Term.Term a b, Term.Term a b)];
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
      Shows_Literal.Showl b) => [((Term.Term a b, Term.Term a b),
                                   [(Term.Term a b, Term.Term a b)])] ->
                                  (((Term.Term a b, Term.Term a b),
                                     [(Term.Term a b, Term.Term a b)]) ->
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
                    (Term_More.vars_term_list (fst (fst cr))) (zv cr i))
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
            (List.upt Arith.zero_nat (List.size_list (snd cr))))
          (\ x -> Sum_Type.Inl (snd x)))
      crs)
    (\ x -> Sum_Type.Inl (snd x));

check_sp_unraveling ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Collection_Eq.Ceq b,
      Collection_Order.Ccompare b, Eq b, Set_Impl.Set_impl b,
      Shows_Literal.Showl b) => [(((Term.Term a b, Term.Term a b),
                                    [(Term.Term a b, Term.Term a b)]),
                                   [(Term.Term a b, Term.Term a b)])] ->
                                  [((Term.Term a b, Term.Term a b),
                                     [(Term.Term a b, Term.Term a b)])] ->
                                    Sum_Type.Sum (String -> String)
                                      [(Term.Term a b, Term.Term a b)];
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
  (Error_Monad.catch_error (Trs_Impl.check_left_linear_trs (concatMap snd c_rs))
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
