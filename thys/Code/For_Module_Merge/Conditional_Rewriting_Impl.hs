{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Conditional_Rewriting_Impl(Cstep_proof(..), x_impl, y_impl, showsl_eq,
                              showsl_conditions, showsl_crule,
                              check_crule_variants, showsl_ctrs,
                              check_variant_in_ctrs, check_csteps, check_dctrs,
                              check_type3, match_crule, check_wf_ctrs,
                              funs_ctrs_list, showsl_coverlap,
                              check_feasibility, check_right_stable,
                              check_extended_properly_oriented)
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
import qualified Conditional_Rewriting;
import qualified Set;
import qualified Container_Setup;
import qualified Trs_Impl_More;
import qualified Term_Impl;
import qualified HOL;
import qualified Cardinality;
import qualified Collection_Enum;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Product_Type;
import qualified Fresh;
import qualified Position;
import qualified Option_Monad;
import qualified Matching;
import qualified Option;
import qualified Error_Monad;
import qualified Subterm_and_Context;
import qualified Check_Monad;
import qualified Sum_Type;
import qualified Mapping_Impl;
import qualified Collection_Order;
import qualified Compare;
import qualified Trs_Impl;
import qualified Shows_Literal;
import qualified Trs;
import qualified Term_More;
import qualified List;
import qualified Term;
import qualified Arith;

data Cstep_proof a b =
  Cstep_step ((Term.Term a b, Term.Term a b), [(Term.Term a b, Term.Term a b)])
    [Arith.Nat] (b -> Term.Term a b) (Term.Term a b) (Term.Term a b)
    [[Cstep_proof a b]];

x_impl ::
  forall a b.
    ((Term.Term a b, Term.Term a b), [(Term.Term a b, Term.Term a b)]) ->
      Arith.Nat -> [b];
x_impl cr i =
  concat
    (Term_More.vars_term_list (fst (fst cr)) :
      map (Term_More.vars_term_list . snd) (List.take i (snd cr)));

y_impl ::
  forall a b.
    ((Term.Term a b, Term.Term a b), [(Term.Term a b, Term.Term a b)]) ->
      Arith.Nat -> [b];
y_impl cr i =
  Term_More.vars_term_list (snd (fst cr)) ++
    Term_More.vars_term_list (snd (List.nth (snd cr) i)) ++
      Trs.vars_trs_list (List.drop (Arith.suc i) (snd cr));

showsl_eq ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => (Term.Term a b, Term.Term a b) ->
                                  String -> String;
showsl_eq =
  Trs_Impl.showsl_rulea Shows_Literal.showsl Shows_Literal.showsl " ->* ";

check_Ru_NF ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a,
      Collection_Order.Ccompare b, Eq b, Mapping_Impl.Mapping_impl b,
      Shows_Literal.Showl b) => Term.Term a b ->
                                  [((Term.Term a b, Term.Term a b),
                                     [(Term.Term a b, Term.Term a b)])] ->
                                    Sum_Type.Sum (String -> String) ();
check_Ru_NF s r =
  Check_Monad.check (Trs_Impl.is_NF_trs (map fst r) s)
    ((Shows_Literal.showsl_lit "the term " . Term_More.showsl_terma s) .
      Shows_Literal.showsl_lit " is not an Ru normal form\n");

showsl_conditions ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => [(Term.Term a b, Term.Term a b)] ->
                                  String -> String;
showsl_conditions =
  Shows_Literal.showsl_sep showsl_eq (Shows_Literal.showsl_lit ", ");

showsl_crule ::
  forall a b c d.
    (Shows_Literal.Showl a, Shows_Literal.Showl b, Shows_Literal.Showl c,
      Shows_Literal.Showl d) => ((Term.Term a b, Term.Term a b),
                                  [(Term.Term c d, Term.Term c d)]) ->
                                  String -> String;
showsl_crule cr =
  Trs_Impl.showsl_rule (fst cr) .
    (if null (snd cr) then id
      else Shows_Literal.showsl_lit " | " . showsl_conditions (snd cr));

check_crule_variants ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b,
      Shows_Literal.Showl b) => ((Term.Term a b, Term.Term a b),
                                  [(Term.Term a b, Term.Term a b)]) ->
                                  ((Term.Term a b, Term.Term a b),
                                    [(Term.Term a b, Term.Term a b)]) ->
                                    Sum_Type.Sum (String -> String) ();
check_crule_variants ra r =
  let {
    rs = fst ra : snd ra;
    rsa = fst r : snd r;
  } in Check_Monad.check
         (not (Option.is_none (Trs_Impl_More.match_rules rs rsa)) &&
           not (Option.is_none (Trs_Impl_More.match_rules rsa rs)))
         (((showsl_crule ra . Shows_Literal.showsl_lit " and ") .
            showsl_crule r) .
           Shows_Literal.showsl_lit " are not variants of each other\n");

showsl_crules ::
  forall a b c d.
    (Shows_Literal.Showl a, Shows_Literal.Showl b, Shows_Literal.Showl c,
      Shows_Literal.Showl d) => [((Term.Term a b, Term.Term a b),
                                   [(Term.Term c d, Term.Term c d)])] ->
                                  String -> String;
showsl_crules ctrs =
  Shows_Literal.showsl_list_gen showsl_crule "" "" "\n" "" ctrs .
    Shows_Literal.showsl_literal "\n";

showsl_ctrs ::
  forall a b c d.
    (Shows_Literal.Showl a, Shows_Literal.Showl b, Shows_Literal.Showl c,
      Shows_Literal.Showl d) => [((Term.Term a b, Term.Term a b),
                                   [(Term.Term c d, Term.Term c d)])] ->
                                  String -> String;
showsl_ctrs r = Shows_Literal.showsl_lit "CTRS:\n\n" . showsl_crules r;

check_variant_in_ctrs ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b,
      Shows_Literal.Showl b) => [((Term.Term a b, Term.Term a b),
                                   [(Term.Term a b, Term.Term a b)])] ->
                                  ((Term.Term a b, Term.Term a b),
                                    [(Term.Term a b, Term.Term a b)]) ->
                                    Sum_Type.Sum (String -> String) ();
check_variant_in_ctrs ra r =
  Error_Monad.catch_error
    (Error_Monad.catch_error (Error_Monad.existsM (check_crule_variants r) ra)
      (\ x -> Sum_Type.Inl (Shows_Literal.showsl_sep id id x)))
    (\ _ ->
      Sum_Type.Inl
        (((Shows_Literal.showsl_lit "rule " . showsl_crule r) .
           Shows_Literal.showsl_lit " is not a variant of any rule in:\n") .
          showsl_ctrs ra));

cstep_trg :: forall a b. Cstep_proof a b -> Term.Term a b;
cstep_trg (Cstep_step x1 x2 x3 x4 x5 x6) = x5;

cstep_src :: forall a b. Cstep_proof a b -> Term.Term a b;
cstep_src (Cstep_step x1 x2 x3 x4 x5 x6) = x4;

check_cstep ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b,
      Shows_Literal.Showl b) => [((Term.Term a b, Term.Term a b),
                                   [(Term.Term a b, Term.Term a b)])] ->
                                  Cstep_proof a b ->
                                    Sum_Type.Sum (String -> String) ();
check_cstep ra (Cstep_step ((l, r), cs) p sigma s t pss) =
  Error_Monad.bind (check_variant_in_ctrs ra ((l, r), cs))
    (\ _ ->
      Error_Monad.bind
        (Check_Monad.check
          (Arith.equal_nat (List.size_list pss) (List.size_list cs))
          (Shows_Literal.showsl_lit
            "mismatch between number of conditions and number of rewrite sequences"))
        (\ _ ->
          Error_Monad.bind
            (Check_Monad.check
              (Term.equal_term s
                (Subterm_and_Context.intp_actxt Term.Fun
                  (Term_More.ctxt_of_pos_term p s)
                  (Term.eval_term Term.Fun l sigma)))
              ((Term_More.showsl_terma s .
                 Shows_Literal.showsl_lit " does not contain an instance of ") .
                Term_More.showsl_terma l))
            (\ _ ->
              Error_Monad.bind
                (Check_Monad.check
                  (Term.equal_term t
                    (Subterm_and_Context.intp_actxt Term.Fun
                      (Term_More.ctxt_of_pos_term p s)
                      (Term.eval_term Term.Fun r sigma)))
                  ((Term_More.showsl_terma t .
                     Shows_Literal.showsl_lit
                       " does not contain an instance of ") .
                    Term_More.showsl_terma r))
                (\ _ ->
                  Error_Monad.catch_error
                    (Error_Monad.forallM
                      (\ i ->
                        check_csteps ra
                          (Term.eval_term Term.Fun (fst (List.nth cs i)) sigma)
                          (Term.eval_term Term.Fun (snd (List.nth cs i)) sigma)
                          (List.nth pss i))
                      (List.upt Arith.zero_nat (List.size_list cs)))
                    (\ x -> Sum_Type.Inl (snd x))))));

check_csteps ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b,
      Shows_Literal.Showl b) => [((Term.Term a b, Term.Term a b),
                                   [(Term.Term a b, Term.Term a b)])] ->
                                  Term.Term a b ->
                                    Term.Term a b ->
                                      [Cstep_proof a b] ->
Sum_Type.Sum (String -> String) ();
check_csteps r s t [] =
  Check_Monad.check (Term.equal_term s t)
    ((((Shows_Literal.showsl_lit "empty rewrite sequence but source " .
         Term_More.showsl_terma s) .
        Shows_Literal.showsl_lit " and target ") .
       Term_More.showsl_terma t) .
      Shows_Literal.showsl_lit " differ");
check_csteps r s t [p] =
  Error_Monad.bind
    (Check_Monad.check (Term.equal_term (cstep_src p) s)
      ((Term_More.showsl_terma (cstep_src p) .
         Shows_Literal.showsl_lit " does not match the source ") .
        Term_More.showsl_terma s))
    (\ _ ->
      Error_Monad.bind
        (Check_Monad.check (Term.equal_term (cstep_trg p) t)
          ((Term_More.showsl_terma (cstep_trg p) .
             Shows_Literal.showsl_lit " does not match the target ") .
            Term_More.showsl_terma t))
        (\ _ -> check_cstep r p));
check_csteps r s t (p : v : va) =
  Error_Monad.bind
    (Check_Monad.check (Term.equal_term (cstep_src p) s)
      ((Term_More.showsl_terma (cstep_src p) .
         Shows_Literal.showsl_lit " does not match the source ") .
        Term_More.showsl_terma s))
    (\ _ ->
      Error_Monad.bind (check_cstep r p)
        (\ _ -> check_csteps r (cstep_trg p) t (v : va)));

check_dctrs ::
  forall a b.
    (Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => [((Term.Term a b, Term.Term a b),
                                   [(Term.Term a b, Term.Term a b)])] ->
                                  Sum_Type.Sum (String -> String) ();
check_dctrs r =
  Error_Monad.catch_error
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ cr ->
          Error_Monad.catch_error
            (Error_Monad.forallM
              (\ i ->
                Error_Monad.catch_error
                  (Check_Monad.check_subseteq
                    (Term_More.vars_term_list (fst (List.nth (snd cr) i)))
                    (x_impl cr i))
                  (\ x ->
                    Sum_Type.Inl
                      ((((((Shows_Literal.showsl_lit "variable " .
                             Shows_Literal.showsl x) .
                            Shows_Literal.showsl_lit " in condition ") .
                           Trs_Impl.showsl_rule (List.nth (snd cr) i)) .
                          Shows_Literal.showsl_lit " of rule ") .
                         showsl_crule cr) .
                        Shows_Literal.showsl_lit "violates DCTRS condition\n")))
              (List.upt Arith.zero_nat (List.size_list (snd cr))))
            (\ x -> Sum_Type.Inl (snd x)))
        r)
      (\ x -> Sum_Type.Inl (snd x)))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit "the CTRS is not deterministic\n" . x));

check_type3 ::
  forall a b.
    (Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => [((Term.Term a b, Term.Term a b),
                                   [(Term.Term a b, Term.Term a b)])] ->
                                  Sum_Type.Sum (String -> String) ();
check_type3 r =
  Error_Monad.catch_error
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ cr ->
          Error_Monad.catch_error
            (Check_Monad.check_subseteq
              (Term_More.vars_term_list (snd (fst cr)))
              (Term_More.vars_term_list (fst (fst cr)) ++
                Trs.vars_trs_list (snd cr)))
            (\ x ->
              Sum_Type.Inl
                ((((Shows_Literal.showsl_lit "variable " .
                     Shows_Literal.showsl x) .
                    Shows_Literal.showsl_lit
                      " occurs only in right-hand side of rule ") .
                   showsl_crule cr) .
                  Shows_Literal.showsl_literal "\n")))
        r)
      (\ x -> Sum_Type.Inl (snd x)))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit "the CTRS is not of type 3\n" . x));

match_crule ::
  forall a b.
    (Eq a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b) => ((Term.Term a b, Term.Term a b),
[(Term.Term a b, Term.Term a b)]) ->
((Term.Term a b, Term.Term a b), [(Term.Term a b, Term.Term a b)]) ->
  Maybe (b -> Term.Term a b);
match_crule rho_1 rho_2 =
  Option.bind
    (Option_Monad.zip_option
      (fst (fst rho_2) :
        snd (fst rho_2) : map fst (snd rho_2) ++ map snd (snd rho_2))
      (fst (fst rho_1) :
        snd (fst rho_1) : map fst (snd rho_1) ++ map snd (snd rho_1)))
    (Matching.match_list Term.Var);

check_wf_ctrs ::
  forall a b.
    (Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => [((Term.Term a b, Term.Term a b),
                                   [(Term.Term a b, Term.Term a b)])] ->
                                  Sum_Type.Sum (String -> String) ();
check_wf_ctrs r =
  Error_Monad.catch_error
    (Error_Monad.bind (Trs_Impl.check_varcond_no_Var_lhs (map fst r))
      (\ _ -> Error_Monad.bind (check_dctrs r) (\ _ -> check_type3 r)))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit "the CTRS is not well-formed\n" . x));

funs_crule_list ::
  forall a b.
    ((Term.Term a b, Term.Term a b), [(Term.Term a b, Term.Term a b)]) -> [a];
funs_crule_list r = Trs_Impl.add_funs_rule (fst r) (Trs.funs_trs_list (snd r));

funs_ctrs_list ::
  forall a b.
    [((Term.Term a b, Term.Term a b), [(Term.Term a b, Term.Term a b)])] -> [a];
funs_ctrs_list trs = concatMap funs_crule_list trs;

showsl_coverlap ::
  forall a b c d e f g h.
    (Shows_Literal.Showl a, Shows_Literal.Showl b, Shows_Literal.Showl c,
      Shows_Literal.Showl d, Shows_Literal.Showl e, Shows_Literal.Showl f,
      Shows_Literal.Showl g,
      Shows_Literal.Showl h) => ((Term.Term a b, Term.Term a b),
                                  [(Term.Term c d, Term.Term c d)]) ->
                                  ((Term.Term e f, Term.Term e f),
                                    [(Term.Term g h, Term.Term g h)]) ->
                                    [Arith.Nat] -> String -> String;
showsl_coverlap rho_1 rho_2 p =
  ((((Shows_Literal.showsl_lit "overlap of conditional rules " .
       showsl_crule rho_1) .
      Shows_Literal.showsl_lit " and ") .
     showsl_crule rho_2) .
    Shows_Literal.showsl_lit " at position ") .
    Position.showsl_pos p;

check_feasibility ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Collection_Order.Ccompare b, Fresh.Infinite b,
      Eq b, Mapping_Impl.Mapping_impl b,
      Shows_Literal.Showl b) => [((Term.Term a b, Term.Term a b),
                                   [(Term.Term a b, Term.Term a b)])] ->
                                  [(Term.Term a b, Term.Term a b)] ->
                                    (b -> Term.Term a b) ->
                                      [[Cstep_proof a b]] ->
Sum_Type.Sum (String -> String) ();
check_feasibility r cs sigma prfs =
  Error_Monad.bind
    (Check_Monad.check
      (Arith.equal_nat (List.size_list cs) (List.size_list prfs))
      (Shows_Literal.showsl_lit "# conditions != # rewrite sequences"))
    (\ _ ->
      Error_Monad.bind
        (Error_Monad.catch_error
          (Error_Monad.forallM
            (\ (a, b) ->
              (case a of {
                (s, t) ->
                  check_csteps r (Term.eval_term Term.Fun s sigma)
                    (Term.eval_term Term.Fun t sigma);
              })
                b)
            (zip cs prfs))
          (\ x -> Sum_Type.Inl (snd x)))
        (\ _ -> Sum_Type.Inr ()));

check_constructor_term ::
  forall a b.
    (Cardinality.Finite_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Compare.Compare a, Eq a,
      Set_Impl.Set_impl a, Shows_Literal.Showl a, Compare.Compare b, Eq b,
      Shows_Literal.Showl b) => Term.Term a b ->
                                  [((Term.Term a b, Term.Term a b),
                                     [(Term.Term a b, Term.Term a b)])] ->
                                    Sum_Type.Sum (String -> String) ();
check_constructor_term s r =
  Check_Monad.check
    (Set.less_eq_set (Subterm_and_Context.funas_term s)
      (Set.minus_set (Conditional_Rewriting.funas_ctrs (List.set r))
        (List.set (Trs_Impl.defined_list (map fst r)))))
    ((Shows_Literal.showsl_lit "the term " . Term_More.showsl_terma s) .
      Shows_Literal.showsl_lit " is not a constructor term\n");

check_right_stable ::
  forall a b.
    (Cardinality.Finite_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Compare.Compare_order a, Eq a,
      Set_Impl.Set_impl a, Shows_Literal.Showl a, Collection_Eq.Ceq b,
      Collection_Order.Ccompare b, Compare.Compare b, Eq b,
      Mapping_Impl.Mapping_impl b, Set_Impl.Set_impl b,
      Shows_Literal.Showl b) => [((Term.Term a b, Term.Term a b),
                                   [(Term.Term a b, Term.Term a b)])] ->
                                  Sum_Type.Sum (String -> String) ();
check_right_stable r =
  Error_Monad.catch_error
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ ra ->
          Error_Monad.catch_error
            (Error_Monad.forallM
              (\ i ->
                let {
                  t_i = snd (List.nth (snd ra) i);
                } in Error_Monad.bind
                       (Error_Monad.catch_error
                         (Check_Monad.check_disjoint
                           (Term_More.vars_term_list (fst (fst ra)) ++
                             concatMap (\ (s, _) -> Term_More.vars_term_list s)
                               (List.take (Arith.suc i) (snd ra)) ++
                               concatMap
                                 (\ (_, a) -> Term_More.vars_term_list a)
                                 (List.take i (snd ra)))
                           (Term_More.vars_term_list t_i))
                         (\ x ->
                           Sum_Type.Inl
                             ((((Shows_Literal.showsl_lit "variable " .
                                  Shows_Literal.showsl x) .
                                 Shows_Literal.showsl_lit
                                   " in rhs of condition ") .
                                Shows_Literal.showsl_nat i) .
                               Shows_Literal.showsl_lit " is not fresh\n")))
                       (\ _ ->
                         Error_Monad.catch_error
                           (Error_Monad.choice
                             [Error_Monad.bind (Term_Impl.check_linear_term t_i)
                                (\ _ -> check_constructor_term t_i r),
                               Error_Monad.bind
                                 (Term_Impl.check_ground_term t_i)
                                 (\ _ -> check_Ru_NF t_i r)])
                           (\ x ->
                             Sum_Type.Inl
                               (Shows_Literal.showsl_sep id
                                 (Shows_Literal.showsl_literal "\n") x))))
              (List.upt Arith.zero_nat (List.size_list (snd ra))))
            (\ x -> Sum_Type.Inl (snd x)))
        r)
      (\ x -> Sum_Type.Inl (snd x)))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit "the CTRS is not right stable\n" . x));

check_extended_properly_oriented ::
  forall a b.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a, Cardinality.Finite_UNIV b,
      Collection_Enum.Cenum b, Collection_Eq.Ceq b,
      Collection_Order.Cproper_interval b, Compare.Compare b, Eq b,
      Set_Impl.Set_impl b,
      Shows_Literal.Showl b) => [((Term.Term a b, Term.Term a b),
                                   [(Term.Term a b, Term.Term a b)])] ->
                                  Sum_Type.Sum (String -> String) ();
check_extended_properly_oriented r =
  Check_Monad.check
    (Conditional_Rewriting.extended_properly_oriented (List.set r))
    (Shows_Literal.showsl_lit
      "the given CTRS is not extended properly oriented\n");

}
