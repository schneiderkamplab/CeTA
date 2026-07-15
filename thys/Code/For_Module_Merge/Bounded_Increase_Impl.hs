{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Bounded_Increase_Impl(Cond_constraint_prf(..), Cond_red_pair_prf(..),
                         conditional_general_reduction_pair_proc)
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
import qualified Q_Restricted_Rewriting_Impl;
import qualified Generalized_Usable_Rules_Impl;
import qualified Orthogonality_Impl;
import qualified Renaming2_String;
import qualified Non_Inf_Order;
import qualified Renaming2;
import qualified Lists_are_Infinite;
import qualified Missing_List;
import qualified Dependency_Graph_Impl;
import qualified Dependency_Pair_Problem_Spec;
import qualified Compare;
import qualified Cardinality;
import qualified Subterm_and_Context;
import qualified Bounded_Increase;
import qualified Trs_Impl;
import qualified Trs;
import qualified Name;
import qualified Unification;
import qualified Fun;
import qualified List;
import qualified HOL;
import qualified Non_Inf_Order_Impl;
import qualified Set;
import qualified Set_Impl;
import qualified Str;
import qualified Mapping_Impl;
import qualified Collection_Order;
import qualified Collection_Eq;
import qualified Product_Type;
import qualified Term_More;
import qualified Term_Impl;
import qualified Option;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Shows_Literal;
import qualified Generalized_Usable_Rules;
import qualified Term;
import qualified Arith;

data Cond_constraint_prf a b = Final
  | Delete_Condition (Generalized_Usable_Rules.Cond_constraint a b)
      (Cond_constraint_prf a b)
  | Different_Constructor (Generalized_Usable_Rules.Cond_constraint a b)
  | Same_Constructor (Generalized_Usable_Rules.Cond_constraint a b)
      (Generalized_Usable_Rules.Cond_constraint a b) (Cond_constraint_prf a b)
  | Variable_Equation b (Term.Term a b)
      (Generalized_Usable_Rules.Cond_constraint a b) (Cond_constraint_prf a b)
  | Funarg_Into_Var (Generalized_Usable_Rules.Cond_constraint a b) Arith.Nat b
      (Generalized_Usable_Rules.Cond_constraint a b) (Cond_constraint_prf a b)
  | Simplify_Condition (Generalized_Usable_Rules.Cond_constraint a b)
      [(b, Term.Term a b)] (Generalized_Usable_Rules.Cond_constraint a b)
      (Cond_constraint_prf a b)
  | Induction (Generalized_Usable_Rules.Cond_constraint a b)
      [Generalized_Usable_Rules.Cond_constraint a b]
      [((Term.Term a b, Term.Term a b),
         ([(Term.Term a b, [b])],
           (Generalized_Usable_Rules.Cond_constraint a b,
             Cond_constraint_prf a b)))];

data Cond_red_pair_prf a b =
  Cond_Red_Pair_Prf a
    [(Generalized_Usable_Rules.Cond_constraint a b,
       ([(Term.Term a b, Term.Term a b)], Cond_constraint_prf a b))]
    Arith.Nat Arith.Nat;

check_rys ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => ((a, Arith.Nat) -> Bool) ->
                                  Maybe (a, Arith.Nat) ->
                                    Term.Term a b ->
                                      (Term.Term a b, [b]) ->
Sum_Type.Sum (String -> String) ();
check_rys d rt r rys =
  (case rys of {
    (ra, ys) ->
      Error_Monad.bind
        (Check_Monad.check (Term.root ra == rt)
          (((Shows_Literal.showsl_lit "root of " . Term_More.showsl_terma ra) .
             Shows_Literal.showsl_lit " is not ") .
            Shows_Literal.showsl_prod (Option.the rt)))
        (\ _ ->
          Error_Monad.bind
            (Check_Monad.check
              (Term.equal_term r ra || Term_Impl.supt_impl r ra)
              ((Term_More.showsl_terma ra .
                 Shows_Literal.showsl_lit " is not a subterm of ") .
                Term_More.showsl_terma r))
            (\ _ ->
              Error_Monad.bind
                (Error_Monad.catch_error
                  (Error_Monad.forallM
                    (\ f ->
                      Check_Monad.check (not (d f))
                        ((((Shows_Literal.showsl_lit "the defined symbol " .
                             Shows_Literal.showsl_prod f) .
                            Shows_Literal.showsl_lit
                              " occurs in the subterm ") .
                           Term_More.showsl_terma ra) .
                          Shows_Literal.showsl_lit " of the rhs"))
                    (Term_More.funas_args_term_list ra))
                  (\ x -> Sum_Type.Inl (snd x)))
                (\ _ ->
                  Error_Monad.catch_error
                    (Check_Monad.check_disjoint ys (Term_More.vars_term_list r))
                    (\ x ->
                      Sum_Type.Inl
                        ((Shows_Literal.showsl x .
                           Shows_Literal.showsl_lit " occurs in ") .
                          Term_More.showsl_terma r)))));
  });

showsl_cc_aux ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => Bool ->
                                  Generalized_Usable_Rules.Cond_constraint a
                                    b ->
                                    String -> String;
showsl_cc_aux b (Generalized_Usable_Rules.CC_rewr s t) =
  (Term_More.showsl_terma s . Shows_Literal.showsl_lit " = ") .
    Term_More.showsl_terma t;
showsl_cc_aux b (Generalized_Usable_Rules.CC_cond stri (s, t)) =
  (Term_More.showsl_terma s .
    Shows_Literal.showsl_lit (if stri then " > " else " >= ")) .
    Term_More.showsl_terma t;
showsl_cc_aux b (Generalized_Usable_Rules.CC_all x c) =
  let {
    s = ((Shows_Literal.showsl_lit "ALL " . Shows_Literal.showsl x) .
          Shows_Literal.showsl_lit ". ") .
          showsl_cc_aux False c;
  } in (if b then (Shows_Literal.showsl_lit "(" . s) .
                    Shows_Literal.showsl_lit ")"
         else s);
showsl_cc_aux b (Generalized_Usable_Rules.CC_impl cs c2) =
  (((Shows_Literal.showsl_lit "(" .
      Shows_Literal.showsl_list_gen id "True" "" " and " ""
        (map (showsl_cc_aux True) cs)) .
     Shows_Literal.showsl_lit " => ") .
    showsl_cc_aux True c2) .
    Shows_Literal.showsl_lit ")";

showsl_cc ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => Generalized_Usable_Rules.Cond_constraint a b ->
                                  String -> String;
showsl_cc = showsl_cc_aux False;

cc_unbound ::
  forall a b.
    Generalized_Usable_Rules.Cond_constraint a b ->
      ([b], Generalized_Usable_Rules.Cond_constraint a b);
cc_unbound (Generalized_Usable_Rules.CC_all x c) = (case cc_unbound c of {
             (xs, a) -> (x : xs, a);
           });
cc_unbound (Generalized_Usable_Rules.CC_cond v va) =
  ([], Generalized_Usable_Rules.CC_cond v va);
cc_unbound (Generalized_Usable_Rules.CC_rewr v va) =
  ([], Generalized_Usable_Rules.CC_rewr v va);
cc_unbound (Generalized_Usable_Rules.CC_impl v va) =
  ([], Generalized_Usable_Rules.CC_impl v va);

deep_normalize_cca ::
  forall a b.
    Generalized_Usable_Rules.Cond_constraint a b ->
      Generalized_Usable_Rules.Cond_constraint a b;
deep_normalize_cca (Generalized_Usable_Rules.CC_impl [] c) =
  deep_normalize_cca c;
deep_normalize_cca (Generalized_Usable_Rules.CC_impl (v : va) c) =
  Generalized_Usable_Rules.CC_impl (map deep_normalize_cca (v : va))
    (deep_normalize_cca c);
deep_normalize_cca (Generalized_Usable_Rules.CC_cond s c) =
  Generalized_Usable_Rules.CC_cond s c;
deep_normalize_cca (Generalized_Usable_Rules.CC_all s c) =
  Generalized_Usable_Rules.CC_all s (deep_normalize_cca c);
deep_normalize_cca (Generalized_Usable_Rules.CC_rewr s c) =
  Generalized_Usable_Rules.CC_rewr s c;

deep_normalize_cc ::
  forall a b.
    (Eq a) => ([a] -> a) ->
                Generalized_Usable_Rules.Cond_constraint b a ->
                  Generalized_Usable_Rules.Cond_constraint b a;
deep_normalize_cc fresh c =
  Bounded_Increase.normalize_alpha fresh (deep_normalize_cca c);

check_subsumesa ::
  forall a b.
    (Eq a,
      Eq b) => Generalized_Usable_Rules.Cond_constraint a b ->
                 Generalized_Usable_Rules.Cond_constraint a b -> Bool;
check_subsumesa (Generalized_Usable_Rules.CC_impl cs c)
  (Generalized_Usable_Rules.CC_impl ds d) =
  check_subsumesa c d &&
    all (\ ca -> any (\ da -> check_subsumesa da ca) ds) cs;
check_subsumesa (Generalized_Usable_Rules.CC_cond v va)
  (Generalized_Usable_Rules.CC_impl ds d) =
  check_subsumesa (Generalized_Usable_Rules.CC_cond v va) d;
check_subsumesa (Generalized_Usable_Rules.CC_rewr v va)
  (Generalized_Usable_Rules.CC_impl ds d) =
  check_subsumesa (Generalized_Usable_Rules.CC_rewr v va) d;
check_subsumesa (Generalized_Usable_Rules.CC_all v va)
  (Generalized_Usable_Rules.CC_impl ds d) =
  check_subsumesa (Generalized_Usable_Rules.CC_all v va) d;
check_subsumesa (Generalized_Usable_Rules.CC_all x c)
  (Generalized_Usable_Rules.CC_all y d) = x == y && check_subsumesa c d;
check_subsumesa (Generalized_Usable_Rules.CC_cond v va)
  (Generalized_Usable_Rules.CC_cond vb vc) =
  Generalized_Usable_Rules.equal_cond_constraint
    (Generalized_Usable_Rules.CC_cond v va)
    (Generalized_Usable_Rules.CC_cond vb vc);
check_subsumesa (Generalized_Usable_Rules.CC_cond v va)
  (Generalized_Usable_Rules.CC_rewr vb vc) =
  Generalized_Usable_Rules.equal_cond_constraint
    (Generalized_Usable_Rules.CC_cond v va)
    (Generalized_Usable_Rules.CC_rewr vb vc);
check_subsumesa (Generalized_Usable_Rules.CC_cond v va)
  (Generalized_Usable_Rules.CC_all vb vc) =
  Generalized_Usable_Rules.equal_cond_constraint
    (Generalized_Usable_Rules.CC_cond v va)
    (Generalized_Usable_Rules.CC_all vb vc);
check_subsumesa (Generalized_Usable_Rules.CC_rewr v va)
  (Generalized_Usable_Rules.CC_cond vb vc) =
  Generalized_Usable_Rules.equal_cond_constraint
    (Generalized_Usable_Rules.CC_rewr v va)
    (Generalized_Usable_Rules.CC_cond vb vc);
check_subsumesa (Generalized_Usable_Rules.CC_rewr v va)
  (Generalized_Usable_Rules.CC_rewr vb vc) =
  Generalized_Usable_Rules.equal_cond_constraint
    (Generalized_Usable_Rules.CC_rewr v va)
    (Generalized_Usable_Rules.CC_rewr vb vc);
check_subsumesa (Generalized_Usable_Rules.CC_rewr v va)
  (Generalized_Usable_Rules.CC_all vb vc) =
  Generalized_Usable_Rules.equal_cond_constraint
    (Generalized_Usable_Rules.CC_rewr v va)
    (Generalized_Usable_Rules.CC_all vb vc);
check_subsumesa (Generalized_Usable_Rules.CC_all v va)
  (Generalized_Usable_Rules.CC_cond vb vc) =
  Generalized_Usable_Rules.equal_cond_constraint
    (Generalized_Usable_Rules.CC_all v va)
    (Generalized_Usable_Rules.CC_cond vb vc);
check_subsumesa (Generalized_Usable_Rules.CC_all v va)
  (Generalized_Usable_Rules.CC_rewr vb vc) =
  Generalized_Usable_Rules.equal_cond_constraint
    (Generalized_Usable_Rules.CC_all v va)
    (Generalized_Usable_Rules.CC_rewr vb vc);
check_subsumesa c (Generalized_Usable_Rules.CC_cond v va) =
  Generalized_Usable_Rules.equal_cond_constraint c
    (Generalized_Usable_Rules.CC_cond v va);
check_subsumesa c (Generalized_Usable_Rules.CC_rewr v va) =
  Generalized_Usable_Rules.equal_cond_constraint c
    (Generalized_Usable_Rules.CC_rewr v va);
check_subsumesa (Generalized_Usable_Rules.CC_impl vb vc)
  (Generalized_Usable_Rules.CC_all v va) =
  Generalized_Usable_Rules.equal_cond_constraint
    (Generalized_Usable_Rules.CC_impl vb vc)
    (Generalized_Usable_Rules.CC_all v va);

check_subsumes ::
  forall a b.
    (Eq a,
      Eq b) => ([a] -> a) ->
                 Generalized_Usable_Rules.Cond_constraint b a ->
                   Generalized_Usable_Rules.Cond_constraint b a -> Bool;
check_subsumes fresh c d = let {
                             n = deep_normalize_cc fresh;
                           } in check_subsumesa (n c) (n d);

check_cc_prf ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Eq a,
      Set_Impl.Set_impl a,
      Shows_Literal.Showl a) => [(Term.Term a [Str.Char],
                                   Term.Term a [Str.Char])] ->
                                  ((a, Arith.Nat) -> Bool) ->
                                    [(a, Arith.Nat)] ->
                                      Bool ->
Generalized_Usable_Rules.Cond_constraint a [Str.Char] ->
  Cond_constraint_prf a [Str.Char] ->
    Sum_Type.Sum (String -> String)
      [Non_Inf_Order_Impl.C_constraint a [Str.Char]];
check_cc_prf r d f m_ortho cc Final =
  (case Bounded_Increase.normalize_cc cc of {
    Generalized_Usable_Rules.CC_cond _ _ ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "problem in final constraint: it is neither a condition nor an implification of two conditions, but it is\n" .
          showsl_cc cc);
    Generalized_Usable_Rules.CC_rewr _ _ ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "problem in final constraint: it is neither a condition nor an implification of two conditions, but it is\n" .
          showsl_cc cc);
    Generalized_Usable_Rules.CC_impl []
      (Generalized_Usable_Rules.CC_cond stri st)
      -> Sum_Type.Inr [Non_Inf_Order_Impl.Unconditional_C stri st];
    Generalized_Usable_Rules.CC_impl [] (Generalized_Usable_Rules.CC_rewr _ _)
      -> Sum_Type.Inl
           (Shows_Literal.showsl_lit
              "problem in final constraint: it is neither a condition nor an implification of two conditions, but it is\n" .
             showsl_cc cc);
    Generalized_Usable_Rules.CC_impl [] (Generalized_Usable_Rules.CC_impl _ _)
      -> Sum_Type.Inl
           (Shows_Literal.showsl_lit
              "problem in final constraint: it is neither a condition nor an implification of two conditions, but it is\n" .
             showsl_cc cc);
    Generalized_Usable_Rules.CC_impl [] (Generalized_Usable_Rules.CC_all _ _) ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "problem in final constraint: it is neither a condition nor an implification of two conditions, but it is\n" .
          showsl_cc cc);
    Generalized_Usable_Rules.CC_impl [Generalized_Usable_Rules.CC_cond stri uv]
      (Generalized_Usable_Rules.CC_cond stria st)
      -> (if stri == stria
           then Sum_Type.Inr [Non_Inf_Order_Impl.Conditional_C stri uv st]
           else Sum_Type.Inl
                  (Shows_Literal.showsl_lit
                     "problem in final constraint: different relations for finalizing " .
                    showsl_cc cc));
    Generalized_Usable_Rules.CC_impl [Generalized_Usable_Rules.CC_cond _ _]
      (Generalized_Usable_Rules.CC_rewr _ _)
      -> Sum_Type.Inl
           (Shows_Literal.showsl_lit
              "problem in final constraint: it is neither a condition nor an implification of two conditions, but it is\n" .
             showsl_cc cc);
    Generalized_Usable_Rules.CC_impl [Generalized_Usable_Rules.CC_cond _ _]
      (Generalized_Usable_Rules.CC_impl _ _)
      -> Sum_Type.Inl
           (Shows_Literal.showsl_lit
              "problem in final constraint: it is neither a condition nor an implification of two conditions, but it is\n" .
             showsl_cc cc);
    Generalized_Usable_Rules.CC_impl [Generalized_Usable_Rules.CC_cond _ _]
      (Generalized_Usable_Rules.CC_all _ _)
      -> Sum_Type.Inl
           (Shows_Literal.showsl_lit
              "problem in final constraint: it is neither a condition nor an implification of two conditions, but it is\n" .
             showsl_cc cc);
    Generalized_Usable_Rules.CC_impl
      (Generalized_Usable_Rules.CC_cond _ _ : _ : _) _
      -> Sum_Type.Inl
           (Shows_Literal.showsl_lit
              "problem in final constraint: it is neither a condition nor an implification of two conditions, but it is\n" .
             showsl_cc cc);
    Generalized_Usable_Rules.CC_impl (Generalized_Usable_Rules.CC_rewr _ _ : _)
      _
      -> Sum_Type.Inl
           (Shows_Literal.showsl_lit
              "problem in final constraint: it is neither a condition nor an implification of two conditions, but it is\n" .
             showsl_cc cc);
    Generalized_Usable_Rules.CC_impl (Generalized_Usable_Rules.CC_impl _ _ : _)
      _
      -> Sum_Type.Inl
           (Shows_Literal.showsl_lit
              "problem in final constraint: it is neither a condition nor an implification of two conditions, but it is\n" .
             showsl_cc cc);
    Generalized_Usable_Rules.CC_impl (Generalized_Usable_Rules.CC_all _ _ : _) _
      -> Sum_Type.Inl
           (Shows_Literal.showsl_lit
              "problem in final constraint: it is neither a condition nor an implification of two conditions, but it is\n" .
             showsl_cc cc);
    Generalized_Usable_Rules.CC_all _ _ ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "problem in final constraint: it is neither a condition nor an implification of two conditions, but it is\n" .
          showsl_cc cc);
  });
check_cc_prf r da f m_ortho c (Delete_Condition d prf) =
  Error_Monad.bind
    (Check_Monad.check
      (check_subsumes (Name.fresh_string [Str.char_0x78, Str.char_0x78]) d c)
      (((Shows_Literal.showsl_lit
           "problem in delete conditions when switching from\n" .
          showsl_cc c) .
         Shows_Literal.showsl_lit " to\n") .
        showsl_cc d))
    (\ _ -> check_cc_prf r da f m_ortho d prf);
check_cc_prf r da f m_ortho c (Different_Constructor d) =
  (case Bounded_Increase.normalize_cc c of {
    Generalized_Usable_Rules.CC_impl cs _ ->
      Error_Monad.catch_error
        (Error_Monad.bind
          (Check_Monad.check (List.member cs d)
            ((showsl_cc d . Shows_Literal.showsl_lit "\nis not a premise of ") .
              showsl_cc c))
          (\ _ ->
            (case d of {
              Generalized_Usable_Rules.CC_cond _ _ ->
                Sum_Type.Inl
                  (showsl_cc d .
                    Shows_Literal.showsl_lit
                      " is not a rewrite condition of the correct shape");
              Generalized_Usable_Rules.CC_rewr (Term.Var _) _ ->
                Sum_Type.Inl
                  (showsl_cc d .
                    Shows_Literal.showsl_lit
                      " is not a rewrite condition of the correct shape");
              Generalized_Usable_Rules.CC_rewr (Term.Fun _ _) (Term.Var _) ->
                Sum_Type.Inl
                  (showsl_cc d .
                    Shows_Literal.showsl_lit
                      " is not a rewrite condition of the correct shape");
              Generalized_Usable_Rules.CC_rewr (Term.Fun fa ss) (Term.Fun g ts)
                -> Error_Monad.bind
                     (Check_Monad.check (not (da (fa, List.size_list ss)))
                       (Shows_Literal.showsl fa .
                         Shows_Literal.showsl_lit " is defined"))
                     (\ _ ->
                       Error_Monad.bind
                         (Check_Monad.check
                           (not ((fa, List.size_list ss) ==
                                  (g, List.size_list ts)))
                           ((Shows_Literal.showsl_lit "the root " .
                              Shows_Literal.showsl fa) .
                             Shows_Literal.showsl_lit
                               " is identical on both sides"))
                         (\ _ -> Sum_Type.Inr []));
              Generalized_Usable_Rules.CC_impl _ _ ->
                Sum_Type.Inl
                  (showsl_cc d .
                    Shows_Literal.showsl_lit
                      " is not a rewrite condition of the correct shape");
              Generalized_Usable_Rules.CC_all _ _ ->
                Sum_Type.Inl
                  (showsl_cc d .
                    Shows_Literal.showsl_lit
                      " is not a rewrite condition of the correct shape");
            })))
        (\ x ->
          Sum_Type.Inl
            (((((Shows_Literal.showsl_lit
                   "problem in Different Constructor with rewrite condition " .
                  showsl_cc d) .
                 Shows_Literal.showsl_lit "\non input constraint\n") .
                showsl_cc c) .
               Shows_Literal.showsl_literal "\n") .
              x));
  });
check_cc_prf r da f m_ortho ca (Same_Constructor d c p) =
  (case Bounded_Increase.normalize_cc ca of {
    Generalized_Usable_Rules.CC_impl cs con ->
      Error_Monad.bind
        (Error_Monad.catch_error
          (Error_Monad.bind
            (Check_Monad.check (List.member cs d)
              ((showsl_cc d .
                 Shows_Literal.showsl_lit "\nis not a premise of ") .
                showsl_cc ca))
            (\ _ ->
              (case d of {
                Generalized_Usable_Rules.CC_cond _ _ ->
                  Sum_Type.Inl
                    (showsl_cc d .
                      Shows_Literal.showsl_lit
                        " is not a rewrite condition of the correct shape");
                Generalized_Usable_Rules.CC_rewr (Term.Var _) _ ->
                  Sum_Type.Inl
                    (showsl_cc d .
                      Shows_Literal.showsl_lit
                        " is not a rewrite condition of the correct shape");
                Generalized_Usable_Rules.CC_rewr (Term.Fun _ _) (Term.Var _) ->
                  Sum_Type.Inl
                    (showsl_cc d .
                      Shows_Literal.showsl_lit
                        " is not a rewrite condition of the correct shape");
                Generalized_Usable_Rules.CC_rewr (Term.Fun fa ss)
                  (Term.Fun g ts)
                  -> Error_Monad.bind
                       (Check_Monad.check (not (da (fa, List.size_list ss)))
                         (Shows_Literal.showsl fa .
                           Shows_Literal.showsl_lit " is defined"))
                       (\ _ ->
                         Error_Monad.bind
                           (Check_Monad.check
                             ((fa, List.size_list ss) == (g, List.size_list ts))
                             (((Shows_Literal.showsl fa .
                                 Shows_Literal.showsl_lit " and ") .
                                Shows_Literal.showsl g) .
                               Shows_Literal.showsl_lit " are not identical"))
                           (\ _ ->
                             let {
                               ds = cs ++ map
    (\ (a, b) -> Generalized_Usable_Rules.CC_rewr a b) (zip ss ts);
                               db = Generalized_Usable_Rules.CC_impl ds con;
                             } in Check_Monad.check
                                    (check_subsumes
                                      (Name.fresh_string
[Str.char_0x78, Str.char_0x78])
                                      c db)
                                    (((Shows_Literal.showsl_lit
 "new constraint is " .
showsl_cc c) .
                                       Shows_Literal.showsl_lit
 "\nbut expected was ") .
                                      showsl_cc db)));
                Generalized_Usable_Rules.CC_impl _ _ ->
                  Sum_Type.Inl
                    (showsl_cc d .
                      Shows_Literal.showsl_lit
                        " is not a rewrite condition of the correct shape");
                Generalized_Usable_Rules.CC_all _ _ ->
                  Sum_Type.Inl
                    (showsl_cc d .
                      Shows_Literal.showsl_lit
                        " is not a rewrite condition of the correct shape");
              })))
          (\ x ->
            Sum_Type.Inl
              (((((((Shows_Literal.showsl_lit
                       "problem in Same Constructor with rewrite condition " .
                      showsl_cc d) .
                     Shows_Literal.showsl_lit "\n when switching from\n") .
                    showsl_cc ca) .
                   Shows_Literal.showsl_lit " to\n") .
                  showsl_cc c) .
                 Shows_Literal.showsl_literal "\n") .
                x)))
        (\ _ -> check_cc_prf r da f m_ortho c p);
  });
check_cc_prf r da f m_ortho c (Variable_Equation x t d p) =
  (case Bounded_Increase.normalize_cc c of {
    Generalized_Usable_Rules.CC_impl cs _ ->
      Error_Monad.bind
        (Error_Monad.catch_error
          (Error_Monad.bind
            (Check_Monad.check
              (List.member cs
                 (Generalized_Usable_Rules.CC_rewr (Term.Var x) t) ||
                List.member cs
                  (Generalized_Usable_Rules.CC_rewr t (Term.Var x)) &&
                  Set.ball (Subterm_and_Context.funas_term t)
                    (\ fa -> not (da fa)))
              (((Shows_Literal.showsl_lit "could not find " .
                  showsl_cc (Generalized_Usable_Rules.CC_rewr (Term.Var x) t)) .
                 Shows_Literal.showsl_lit " or reversed as a premise of\n") .
                showsl_cc c))
            (\ _ ->
              let {
                ca = Bounded_Increase.cc_subst_apply
                       (Name.fresh_string [Str.char_0x78, Str.char_0x78]) c
                       (Fun.fun_upd Term.Var x t, Term_More.vars_term_list t);
              } in Check_Monad.check
                     (check_subsumes
                       (Name.fresh_string [Str.char_0x78, Str.char_0x78]) d ca)
                     (((Shows_Literal.showsl_lit "new constraint is " .
                         showsl_cc d) .
                        Shows_Literal.showsl_lit "\nbut expected was ") .
                       showsl_cc ca)))
          (\ xa ->
            Sum_Type.Inl
              (((((((((Shows_Literal.showsl_lit
                         "problem in Variable Equation with substitution " .
                        Shows_Literal.showsl_lista x) .
                       Shows_Literal.showsl_lit "/") .
                      Term_More.showsl_terma t) .
                     Shows_Literal.showsl_lit " to switch from\n") .
                    showsl_cc c) .
                   Shows_Literal.showsl_lit "\nto\n") .
                  showsl_cc d) .
                 Shows_Literal.showsl_literal "\n") .
                xa)))
        (\ _ -> check_cc_prf r da f m_ortho d p);
  });
check_cc_prf r da f m_ortho ca (Funarg_Into_Var c i x d p) =
  (case Bounded_Increase.normalize_cc ca of {
    Generalized_Usable_Rules.CC_impl cs con ->
      Error_Monad.bind
        (Error_Monad.catch_error
          (Error_Monad.bind
            (Check_Monad.check (List.member cs c)
              ((showsl_cc c .
                 Shows_Literal.showsl_lit "\nis not a premise of ") .
                showsl_cc ca))
            (\ _ ->
              Error_Monad.bind
                (Check_Monad.check
                  (not (List.member (Bounded_Increase.vars_cc_list ca) x))
                  ((Shows_Literal.showsl_lit "variable " .
                     Shows_Literal.showsl_lista x) .
                    Shows_Literal.showsl_lit " is not fresh"))
                (\ _ ->
                  (case c of {
                    Generalized_Usable_Rules.CC_cond _ _ ->
                      Sum_Type.Inl
                        (showsl_cc c .
                          Shows_Literal.showsl_lit
                            " is not a rewrite condition of the correct shape");
                    Generalized_Usable_Rules.CC_rewr (Term.Var _) _ ->
                      Sum_Type.Inl
                        (showsl_cc c .
                          Shows_Literal.showsl_lit
                            " is not a rewrite condition of the correct shape");
                    Generalized_Usable_Rules.CC_rewr (Term.Fun fa ss) q ->
                      Error_Monad.bind
                        (Check_Monad.check
                          (Arith.less_nat i (List.size_list ss))
                          (Shows_Literal.showsl_lit "invalid position"))
                        (\ _ ->
                          (case (List.take i ss,
                                  (List.nth ss i, List.drop (Arith.suc i) ss))
                            of {
                            (bef, (pa, aft)) ->
                              Error_Monad.bind
                                (Error_Monad.catch_error
                                  (Check_Monad.check_subseteq
                                    (Term_More.funas_term_list pa) f)
                                  (\ xa ->
                                    Sum_Type.Inl
                                      ((Shows_Literal.showsl_lit
  "function symbol " .
 Shows_Literal.showsl_prod xa) .
Shows_Literal.showsl_lit " is not allowed in argument")))
                                (\ _ ->
                                  let {
                                    px = Generalized_Usable_Rules.CC_rewr pa
   (Term.Var x);
                                    fq = Generalized_Usable_Rules.CC_rewr
   (Term.Fun fa (bef ++ Term.Var x : aft)) q;
                                    ds = px : fq : cs;
                                    daa = Generalized_Usable_Rules.CC_impl ds
    con;
                                  } in Check_Monad.check
 (check_subsumes (Name.fresh_string [Str.char_0x78, Str.char_0x78]) d daa)
 (((Shows_Literal.showsl_lit "new constraint is " . showsl_cc d) .
    Shows_Literal.showsl_lit "\nbut expected was ") .
   showsl_cc daa));
                          }));
                    Generalized_Usable_Rules.CC_impl _ _ ->
                      Sum_Type.Inl
                        (showsl_cc c .
                          Shows_Literal.showsl_lit
                            " is not a rewrite condition of the correct shape");
                    Generalized_Usable_Rules.CC_all _ _ ->
                      Sum_Type.Inl
                        (showsl_cc c .
                          Shows_Literal.showsl_lit
                            " is not a rewrite condition of the correct shape");
                  }))))
          (\ xa ->
            Sum_Type.Inl
              (((((((((((Shows_Literal.showsl_lit
                           "problem in introducing fresh variable " .
                          Shows_Literal.showsl_lista x) .
                         Shows_Literal.showsl_lit " on ") .
                        Shows_Literal.showsl_nat (Arith.suc i)) .
                       Shows_Literal.showsl_lit "-th argument of lhs of ") .
                      showsl_cc c) .
                     Shows_Literal.showsl_lit " to switch from ") .
                    showsl_cc ca) .
                   Shows_Literal.showsl_lit "to\n") .
                  showsl_cc d) .
                 Shows_Literal.showsl_literal "\n") .
                xa)))
        (\ _ -> check_cc_prf r da f m_ortho d p);
  });
check_cc_prf r da f m_ortho c (Simplify_Condition bc sigma d p) =
  (case Bounded_Increase.normalize_cc c of {
    Generalized_Usable_Rules.CC_impl cs psi ->
      Error_Monad.bind
        (Error_Monad.catch_error
          (Error_Monad.bind
            (Check_Monad.check (List.member cs bc)
              ((showsl_cc bc .
                 Shows_Literal.showsl_lit "\nis not a premise of ") .
                showsl_cc c))
            (\ _ ->
              (case cc_unbound bc of {
                (ys, cc) ->
                  (case (case Bounded_Increase.normalize_cc cc of {
                          Generalized_Usable_Rules.CC_impl a b -> (a, b);
                        })
                    of {
                    (phi, psia) ->
                      let {
                        dom_ran = Term_Impl.mk_subst_domain sigma;
                      } in Error_Monad.bind
                             (Error_Monad.catch_error
                               (Check_Monad.check_subseteq (map fst dom_ran) ys)
                               (\ x ->
                                 Sum_Type.Inl
                                   (Shows_Literal.showsl_lista x .
                                     Shows_Literal.showsl_lit
                                       " is in the domain of sigma, but not a bound variable ")))
                             (\ _ ->
                               Error_Monad.bind
                                 (Error_Monad.catch_error
                                   (Error_Monad.forallM
                                     (\ fn ->
                                       Error_Monad.bind
 (Check_Monad.check (not (da fn))
   ((Shows_Literal.showsl_lit "symbol " . Shows_Literal.showsl_prod fn) .
     Shows_Literal.showsl_lit
       " is not allowed in range of sigma, as it is defined"))
 (\ _ ->
   Check_Monad.check (List.member f fn)
     ((Shows_Literal.showsl_lit "symbol " . Shows_Literal.showsl_prod fn) .
       Shows_Literal.showsl_lit
         " is not allowed in range of sigma, as it is not in F")))
                                     (concatMap
                                       (\ x_t ->
 Term_More.funas_term_list (snd x_t))
                                       dom_ran))
                                   (\ x -> Sum_Type.Inl (snd x)))
                                 (\ _ ->
                                   let {
                                     vs = List.remdups
    (concatMap (\ x_t -> Term_More.vars_term_list (snd x_t)) dom_ran);
                                     sigmaa =
                                       (\ ca ->
 Bounded_Increase.cc_subst_apply
   (Name.fresh_string [Str.char_0x78, Str.char_0x78]) ca
   (Term_More.mk_subst Term.Var sigma, vs));
                                   } in Error_Monad.bind
  (Error_Monad.catch_error
    (Error_Monad.forallM
      (\ ca ->
        Check_Monad.check
          (any (\ caa ->
                 check_subsumes
                   (Name.fresh_string [Str.char_0x78, Str.char_0x78]) caa
                   (sigmaa ca))
            cs)
          (showsl_cc (sigmaa ca) .
            Shows_Literal.showsl_lit
              "\nis not contained as premise of the input implication"))
      phi)
    (\ x -> Sum_Type.Inl (snd x)))
  (\ _ ->
    let {
      daa = Generalized_Usable_Rules.CC_impl (sigmaa psia : cs) psi;
    } in Check_Monad.check
           (check_subsumes (Name.fresh_string [Str.char_0x78, Str.char_0x78]) d
             daa)
           (((Shows_Literal.showsl_lit "new constraint is " . showsl_cc d) .
              Shows_Literal.showsl_lit "\nbut expected was ") .
             showsl_cc daa))));
                  });
              })))
          (\ x ->
            Sum_Type.Inl
              (((((((((Shows_Literal.showsl_lit
                         "problem in Simplify Condition with substitution " .
                        Shows_Literal.showsl_lista sigma) .
                       Shows_Literal.showsl_lit " on IH\n") .
                      showsl_cc bc) .
                     Shows_Literal.showsl_lit "\nto switch from\n") .
                    showsl_cc c) .
                   Shows_Literal.showsl_lit "\nto\n") .
                  showsl_cc d) .
                 Shows_Literal.showsl_literal "\n") .
                x)))
        (\ _ -> check_cc_prf r da f m_ortho d p);
  });
check_cc_prf r da f m_ortho c (Induction d ccs ihs) =
  (case Bounded_Increase.normalize_cc c of {
    Generalized_Usable_Rules.CC_impl cs ca ->
      Error_Monad.bind
        (Error_Monad.catch_error
          (Error_Monad.bind
            (Check_Monad.check m_ortho
              (Shows_Literal.showsl_lit "CR or minimality required"))
            (\ _ ->
              Error_Monad.bind
                (Error_Monad.catch_error
                  (Error_Monad.forallM
                    (\ cc ->
                      Check_Monad.check (List.member cs cc)
                        ((showsl_cc cc .
                           Shows_Literal.showsl_lit "\nis not a premise of ") .
                          showsl_cc c))
                    (d : ccs))
                  (\ x -> Sum_Type.Inl (snd x)))
                (\ _ ->
                  (case d of {
                    Generalized_Usable_Rules.CC_cond _ _ ->
                      Sum_Type.Inl
                        (showsl_cc d .
                          Shows_Literal.showsl_lit
                            " is not a rewrite condition of the correct shape");
                    Generalized_Usable_Rules.CC_rewr (Term.Var _) _ ->
                      Sum_Type.Inl
                        (showsl_cc d .
                          Shows_Literal.showsl_lit
                            " is not a rewrite condition of the correct shape");
                    Generalized_Usable_Rules.CC_rewr (Term.Fun fa xs) q ->
                      let {
                        csa = Bounded_Increase.vars_cc_list
                                (Generalized_Usable_Rules.CC_impl
                                  (Generalized_Usable_Rules.CC_rewr
                                     (Term.Fun fa xs) q :
                                    ccs)
                                  ca);
                      } in Error_Monad.bind
                             (Check_Monad.check
                               (all Term.is_Var xs &&
                                 List.distinct (map Term.the_Var xs))
                               ((Shows_Literal.showsl_lit "arguments of " .
                                  Term_More.showsl_terma (Term.Fun fa xs)) .
                                 Shows_Literal.showsl_lit
                                   " are not different variables"))
                             (\ _ ->
                               let {
                                 xsa = map Term.the_Var xs;
                                 rt = Term.root (Term.Fun fa xs);
                               } in Error_Monad.bind
                                      (Check_Monad.check
(Option.is_none (Unification.mgu (Term.Fun fa xs) q))
(Shows_Literal.showsl_lit "lhs and rhs unify"))
                                      (\ _ ->
Error_Monad.bind
  (Error_Monad.catch_error
    (Error_Monad.forallM
      (\ lr ->
        Check_Monad.check
          (if Term.root (fst lr) == rt
            then any (\ lra ->
                       Trs.eq_rule_mod_vars lr lra &&
                         Error_Monad.isOK
                           (Check_Monad.check_disjoint csa
                             (Trs.vars_rule_list lra)))
                   (map (\ (ra, _) -> ra) ihs)
            else True)
          (Shows_Literal.showsl_lit
             "could not find variable renamed version of rule " .
            Trs_Impl.showsl_rule lr))
      r)
    (\ x -> Sum_Type.Inl (snd x)))
  (\ _ ->
    Error_Monad.catch_error
      (Error_Monad.forallM
        (\ (a, b) ->
          (case a of {
            (l, ra) ->
              (\ (rys, (cc, _)) ->
                Error_Monad.catch_error
                  (let {
                     cca = Bounded_Increase.cc_rule_constraint
                             (Name.fresh_string [Str.char_0x78, Str.char_0x78])
                             fa (Term.args l) ra q xsa ccs ca rys;
                   } in Error_Monad.bind
                          (Error_Monad.catch_error
                            (Error_Monad.forallM (check_rys da rt ra) rys)
                            (\ x -> Sum_Type.Inl (snd x)))
                          (\ _ ->
                            Check_Monad.check
                              (check_subsumes
                                (Name.fresh_string
                                  [Str.char_0x78, Str.char_0x78])
                                cc cca)
                              (((Shows_Literal.showsl_lit "new constraint is " .
                                  showsl_cc cc) .
                                 Shows_Literal.showsl_lit
                                   "\nbut expected was ") .
                                showsl_cc cca)))
                  (\ x ->
                    Sum_Type.Inl
                      (((Shows_Literal.showsl_lit
                           "problem in constraint for rule " .
                          Trs_Impl.showsl_rule (l, ra)) .
                         Shows_Literal.showsl_literal "\n") .
                        x)));
          })
            b)
        ihs)
      (\ x -> Sum_Type.Inl (snd x)))));
                    Generalized_Usable_Rules.CC_impl _ _ ->
                      Sum_Type.Inl
                        (showsl_cc d .
                          Shows_Literal.showsl_lit
                            " is not a rewrite condition of the correct shape");
                    Generalized_Usable_Rules.CC_all _ _ ->
                      Sum_Type.Inl
                        (showsl_cc d .
                          Shows_Literal.showsl_lit
                            " is not a rewrite condition of the correct shape");
                  }))))
          (\ x ->
            Sum_Type.Inl
              ((((((Shows_Literal.showsl_lit
                      "problem in Induction rule with rewrite condition " .
                     showsl_cc d) .
                    Shows_Literal.showsl_lit " to switch from\n") .
                   showsl_cc c) .
                  Shows_Literal.showsl_lit "\nto\n") .
                 Shows_Literal.showsl_list_gen
                   (\ (_, (_, (cb, _))) ->
                     showsl_cc cb . Shows_Literal.showsl_literal "\n")
                   "" "" "" "" ihs) .
                x)))
        (\ _ ->
          Error_Monad.bind
            (Error_Monad.mapM
              (\ (_, (_, (a, b))) -> check_cc_prf r da f m_ortho a b) ihs)
            (\ fcss -> Sum_Type.Inr (concat fcss)));
  });

check_cc_prfs ::
  forall a b.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Eq a,
      Set_Impl.Set_impl a,
      Shows_Literal.Showl a) => [(Term.Term a [Str.Char],
                                   Term.Term a [Str.Char])] ->
                                  ((a, Arith.Nat) -> Bool) ->
                                    [(a, Arith.Nat)] ->
                                      Bool ->
[(Generalized_Usable_Rules.Cond_constraint a [Str.Char],
   (b, Cond_constraint_prf a [Str.Char]))] ->
  Sum_Type.Sum (String -> String)
    [Non_Inf_Order_Impl.C_constraint a [Str.Char]];
check_cc_prfs r d f m_ortho [] = Sum_Type.Inr [];
check_cc_prfs r d f m_ortho ((c, (uu, prf)) : cpfs) =
  Error_Monad.bind (check_cc_prf r d f m_ortho c prf)
    (\ l1 ->
      Error_Monad.bind (check_cc_prfs r d f m_ortho cpfs)
        (\ l2 -> Sum_Type.Inr (l1 ++ l2)));

initial_conditions_gen_impl ::
  forall a. (a -> a -> Bool) -> Arith.Nat -> Arith.Nat -> [a] -> a -> [[a]];
initial_conditions_gen_impl pa bef_len aft_len p st =
  let {
    pairs = (\ n -> Missing_List.generate_lists n p);
    a = concatMap (\ bef -> map (\ aft -> bef ++ st : aft) (pairs aft_len))
          (pairs bef_len);
  } in filter
         (\ bef_st_aft ->
           let {
             d = Arith.minus_nat (Arith.plus_nat bef_len aft_len) Arith.one_nat;
           } in (if Arith.less_nat d (Arith.plus_nat bef_len aft_len)
                  then List.all_interval
                         (\ i ->
                           pa (List.nth bef_st_aft i)
                             (List.nth bef_st_aft (Arith.suc i)))
                         Arith.zero_nat d
                  else True))
         a;

check_constraint_present ::
  forall a b.
    (Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b
                                  [Str.Char] () ->
                                  a -> b ->
 [(Term.Term b [Str.Char], Term.Term b [Str.Char])] ->
   Arith.Nat ->
     Arith.Nat ->
       [(Generalized_Usable_Rules.Cond_constraint b [Str.Char],
          [(Term.Term b [Str.Char], Term.Term b [Str.Char])])] ->
         Generalized_Usable_Rules.Condition_type ->
           (Term.Term b [Str.Char], Term.Term b [Str.Char]) ->
             Sum_Type.Sum (String -> String) ();
check_constraint_present i dpp constant p bef aft ccs =
  let {
    edg = Dependency_Graph_Impl.is_iedg_edge_dpp i dpp;
    init_conds =
      initial_conditions_gen_impl (\ st uv -> edg st (fst uv)) bef aft p;
  } in (\ ct st ->
         Error_Monad.catch_error
           (Error_Monad.forallM
             (\ sts ->
               Check_Monad.check
                 (any (\ (c, uvs) ->
                        Generalized_Usable_Rules.disjoint_variant sts uvs &&
                          check_subsumes
                            (Name.fresh_string [Str.char_0x78, Str.char_0x78]) c
                            (Generalized_Usable_Rules.constraint_of constant ct
                              uvs bef))
                   ccs)
                 (((Shows_Literal.showsl_lit "did not find " .
                     Shows_Literal.showsl_lit
                       (case ct of {
                         Generalized_Usable_Rules.Bound -> "bound";
                         Generalized_Usable_Rules.Strict -> "strict";
                         Generalized_Usable_Rules.Non_Strict -> "non-strict";
                       })) .
                    Shows_Literal.showsl_lit " constraint for sequence ") .
                   Trs_Impl.showsl_rules sts))
             (init_conds st))
           (\ x -> Sum_Type.Inl (snd x)));

conditional_general_reduction_pair_proc ::
  forall a b.
    (Collection_Eq.Ceq b, Collection_Order.Ccompare b, Compare.Compare_order b,
      Eq b, Set_Impl.Set_impl b,
      Shows_Literal.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b
                                  [Str.Char] () ->
                                  ([(b, Arith.Nat)] ->
                                    Non_Inf_Order_Impl.Non_inf_order_ext b
                                      [Str.Char] ()) ->
                                    [(Term.Term b [Str.Char],
                                       Term.Term b [Str.Char])] ->
                                      [(Term.Term b [Str.Char],
 Term.Term b [Str.Char])] ->
Cond_red_pair_prf b [Str.Char] ->
  Bool -> a -> Sum_Type.Sum (String -> String) [a];
conditional_general_reduction_pair_proc i grp pstrict pbound prof merge dpp =
  (case prof of {
    Cond_Red_Pair_Prf c ccs bef aft ->
      let {
        p = Dependency_Pair_Problem_Spec.pairs i dpp;
        r = Dependency_Pair_Problem_Spec.rules i dpp;
        f = List.remdups
              (Trs.funas_trs_list r ++
                Trs.funas_args_trs_list p ++
                  concatMap Term_More.funas_term_list
                    (Dependency_Pair_Problem_Spec.q i dpp));
        rp = grp f;
      } in (case Error_Monad.catch_error
                   (Error_Monad.bind (Non_Inf_Order_Impl.valid rp)
                     (\ _ ->
                       Error_Monad.bind
                         (Check_Monad.check
                           (Dependency_Pair_Problem_Spec.wwf_rules i dpp)
                           (Shows_Literal.showsl_lit
                             "require well-formedness of TRS"))
                         (\ _ ->
                           let {
                             is_def =
                               (\ fn ->
                                 not (null (Dependency_Pair_Problem_Spec.rules_map
     i dpp fn)));
                           } in Error_Monad.bind
                                  (Trs_Impl.check_varcond_subset p)
                                  (\ _ ->
                                    Error_Monad.bind
                                      (Error_Monad.catch_error
(Error_Monad.forallM
  (\ (l, ra) ->
    Error_Monad.bind (Term_Impl.check_no_var l)
      (\ _ ->
        Error_Monad.bind (Term_Impl.check_no_var ra)
          (\ _ -> Q_Restricted_Rewriting_Impl.check_no_defined_root is_def ra)))
  p)
(\ x -> Sum_Type.Inl (snd x)))
                                      (\ _ ->
let {
  ccsa = map (\ (ca, (uvs, _)) -> (ca, uvs)) ccs;
  check_present = check_constraint_present i dpp c p bef aft ccsa;
} in (case Dependency_Pair_Problem_Spec.split_pairs i dpp pstrict of {
       (ps, pns) ->
         (case Dependency_Pair_Problem_Spec.split_pairs i dpp pbound of {
           (pb, _) ->
             let {
               pi = Non_Inf_Order_Impl.af rp;
               us = Generalized_Usable_Rules_Impl.usable_rules_gen pi r p;
             } in Error_Monad.bind
                    (Error_Monad.catch_error
                      (Error_Monad.forallM
                        (check_present Generalized_Usable_Rules.Strict) ps)
                      (\ x -> Sum_Type.Inl (snd x)))
                    (\ _ ->
                      Error_Monad.bind
                        (Error_Monad.catch_error
                          (Error_Monad.forallM
                            (check_present Generalized_Usable_Rules.Non_Strict)
                            pns)
                          (\ x -> Sum_Type.Inl (snd x)))
                        (\ _ ->
                          Error_Monad.bind
                            (Error_Monad.catch_error
                              (Error_Monad.forallM
                                (check_present Generalized_Usable_Rules.Bound)
                                pb)
                              (\ x -> Sum_Type.Inl (snd x)))
                            (\ _ ->
                              Error_Monad.bind
                                (Check_Monad.check
                                  (Dependency_Pair_Problem_Spec.nFQ_subset_NF_rules
                                    i dpp)
                                  (Shows_Literal.showsl_lit
                                    "innermost required"))
                                (\ _ ->
                                  Error_Monad.bind
                                    (Error_Monad.catch_error
                                      (Error_Monad.catch_error
(Error_Monad.forallM (Non_Inf_Order_Impl.ns rp) us)
(\ x -> Sum_Type.Inl (snd x)))
                                      (\ x ->
Sum_Type.Inl
  (Shows_Literal.showsl_lit "problem when orienting usable rules\n" . x)))
                                    (\ _ ->
                                      let {
m = Dependency_Pair_Problem_Spec.minimal i dpp;
ortho =
  Error_Monad.isOK
    (Orthogonality_Impl.check_weakly_orthogonal Renaming2_String.string_rename
      r);
                                      } in
Error_Monad.bind
  (Error_Monad.catch_error
    (check_cc_prfs r
      (\ fn -> not (null (Dependency_Pair_Problem_Spec.rules_map i dpp fn))) f
      (m || ortho) ccs)
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "problem when simplifying conditional constraints\n" .
          x)))
  (\ fcs ->
    Error_Monad.catch_error
      (Error_Monad.catch_error
        (Error_Monad.forallM (Non_Inf_Order_Impl.cc rp) fcs)
        (\ x -> Sum_Type.Inl (snd x)))
      (\ x ->
        Sum_Type.Inl
          (Shows_Literal.showsl_lit
             "problem when orienting final (conditional) constraints for pairs\n" .
            x))))))));
         });
     }))))))
                   (\ x ->
                     Sum_Type.Inl
                       (((Shows_Literal.showsl_lit
                            "could not apply the bounded increase processor with the following\n" .
                           Non_Inf_Order_Impl.desc rp) .
                          Shows_Literal.showsl_literal "\n") .
                         x))
             of {
             Sum_Type.Inl a -> Sum_Type.Inl a;
             Sum_Type.Inr _ ->
               Sum_Type.Inr
                 (if merge
                   then [Dependency_Pair_Problem_Spec.delete_P_Pw i dpp
                           (List.inter_list_set pstrict pbound)
                           (List.inter_list_set pstrict pbound)]
                   else [Dependency_Pair_Problem_Spec.delete_P_Pw i dpp pstrict
                           pstrict,
                          Dependency_Pair_Problem_Spec.delete_P_Pw i dpp pbound
                            pbound]);
           });
  });

}
