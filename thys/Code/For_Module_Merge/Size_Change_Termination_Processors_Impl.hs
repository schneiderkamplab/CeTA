{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Size_Change_Termination_Processors_Impl(sct_ur_af_proc, sct_subterm_proc)
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
import qualified Missing_List;
import qualified Product_Lexorder;
import qualified Q_Restricted_Rewriting_Impl;
import qualified Size_Change_Termination_Processors;
import qualified Generic_Usable_Rules_Impl;
import qualified Dependency_Graph_Impl;
import qualified Product_Type;
import qualified Term_Impl;
import qualified Trs_Impl;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified List;
import qualified Dependency_Pair_Problem_Spec;
import qualified Term_Order_Impl;
import qualified Size_Change_Termination;
import qualified Sum_Type;
import qualified Set;
import qualified Compare;
import qualified Str;
import qualified Term;
import qualified Compare_Order_Instances;
import qualified Shows_Literal;
import qualified Compare_Instances;
import qualified Arith;
import qualified Option;
import qualified Map;
import qualified HOL;

fun_of_default :: forall a b. (Eq a) => [(a, b)] -> b -> a -> b;
fun_of_default m d = let {
                       mm = Map.map_of m;
                     } in (\ i -> (case mm i of {
                                    Nothing -> d;
                                    Just e -> e;
                                  }));

sct_entry_to_sts ::
  forall a b c d.
    a -> Term.Term b c ->
           [(d, Arith.Nat)] -> [(d, Arith.Nat)] -> [(a, Term.Term b c)];
sct_entry_to_sts s t stri nstri =
  let {
    a = List.remdups (map snd (stri ++ nstri));
  } in map (\ j -> (s, Size_Change_Termination_Processors.get_arg t j)) a;

check_sct_entry ::
  forall a b c d e f.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => ((a, Arith.Nat) -> Bool) ->
                                  ((Term.Term a b, Term.Term a b) ->
                                    Sum_Type.Sum c d) ->
                                    ((Term.Term a b, Term.Term a b) ->
                                      Sum_Type.Sum e f) ->
                                      Term.Term a b ->
Term.Term a b ->
  [(Arith.Nat, Arith.Nat)] ->
    [(Arith.Nat, Arith.Nat)] -> Sum_Type.Sum (String -> String) ();
check_sct_entry is_def sa nst s t stri nstri =
  Error_Monad.catch_error
    (Error_Monad.bind (Term_Impl.check_no_var s)
      (\ _ ->
        Error_Monad.bind (Term_Impl.check_no_var t)
          (\ _ ->
            Error_Monad.bind
              (Q_Restricted_Rewriting_Impl.check_no_defined_root is_def t)
              (\ _ ->
                let {
                  m = List.size_list (Term.args t);
                  n = List.size_list (Term.args s);
                } in Error_Monad.bind
                       (Error_Monad.catch_error
                         (Error_Monad.forallM
                           (\ i ->
                             Check_Monad.check (Arith.less_eq_nat i n)
                               ((Shows_Literal.showsl_lit
                                   "left-index to large" .
                                  Shows_Literal.showsl_nat i) .
                                 Shows_Literal.showsl_literal "\n"))
                           (List.remdups (map fst (stri ++ nstri))))
                         (\ x -> Sum_Type.Inl (snd x)))
                       (\ _ ->
                         Error_Monad.bind
                           (Error_Monad.catch_error
                             (Error_Monad.forallM
                               (\ j ->
                                 Check_Monad.check (Arith.less_eq_nat j m)
                                   (Shows_Literal.showsl_lit
                                      "right-index to large or argument violates usable-rules condition" .
                                     Shows_Literal.showsl_nat j))
                               (List.remdups (map snd (stri ++ nstri))))
                             (\ x -> Sum_Type.Inl (snd x)))
                           (\ _ ->
                             let {
                               _ = Term.args s;
                               _ = Term.args t;
                             } in Error_Monad.bind
                                    (Error_Monad.catch_error
                                      (Error_Monad.forallM
(\ (i, j) ->
  Check_Monad.check
    (Error_Monad.isOK
      (sa (Size_Change_Termination_Processors.get_arg s i,
            Size_Change_Termination_Processors.get_arg t j)))
    (((Shows_Literal.showsl_lit "problem with edge " .
        Shows_Literal.showsl_nat i) .
       Shows_Literal.showsl_lit " -S-> ") .
      Shows_Literal.showsl_nat j))
stri)
                                      (\ x -> Sum_Type.Inl (snd x)))
                                    (\ _ ->
                                      Error_Monad.catch_error
(Error_Monad.forallM
  (\ (i, j) ->
    Check_Monad.check
      (Error_Monad.isOK
        (nst (Size_Change_Termination_Processors.get_arg s i,
               Size_Change_Termination_Processors.get_arg t j)))
      (((Shows_Literal.showsl_lit "problem with edge " .
          Shows_Literal.showsl_nat i) .
         Shows_Literal.showsl_lit " -NS-> ") .
        Shows_Literal.showsl_nat j))
  nstri)
(\ x -> Sum_Type.Inl (snd x)))))))))
    (\ x ->
      Sum_Type.Inl
        (((Shows_Literal.showsl_lit "problems with DP " .
            Trs_Impl.showsl_rule (s, t)) .
           Shows_Literal.showsl_literal "\n") .
          x));

sct_ur_af_proc ::
  forall a b.
    (Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b
                                  [Str.Char] () ->
                                  Term_Order_Impl.Rel_impl_ext b [Str.Char]
                                    () ->
                                    [((Term.Term b [Str.Char],
Term.Term b [Str.Char]),
                                       ([(Arith.Nat, Arith.Nat)],
 [(Arith.Nat, Arith.Nat)]))] ->
                                      Maybe [(Term.Term b [Str.Char],
       Term.Term b [Str.Char])] ->
a -> Sum_Type.Sum (String -> String) ();
sct_ur_af_proc i rp gs u_opt dpp =
  Error_Monad.catch_error
    (Error_Monad.bind (Term_Order_Impl.rel_impl_redtriple rp)
      (\ _ ->
        let {
          is_def =
            (\ fn ->
              not (null (Dependency_Pair_Problem_Spec.rules_map i dpp fn)));
          pi = Term_Order_Impl.af rp;
          s = Term_Order_Impl.s rp;
          ns = Term_Order_Impl.ns rp;
          nst = Term_Order_Impl.nst rp;
          p = Dependency_Pair_Problem_Spec.pairs i dpp;
          gGs = filter (\ g -> List.member p (fst g)) gs;
        } in Error_Monad.bind
               (Error_Monad.catch_error
                 (Error_Monad.forallM (\ (l, _) -> Term_Impl.check_no_var l)
                   (Dependency_Pair_Problem_Spec.rules i dpp))
                 (\ x -> Sum_Type.Inl (snd x)))
               (\ _ ->
                 Error_Monad.bind
                   (Error_Monad.catch_error
                     (Error_Monad.forallM
                       (\ (a, b) ->
                         (case a of {
                           (sa, t) ->
                             (\ (aa, ba) ->
                               check_sct_entry is_def s nst sa t aa ba);
                         })
                           b)
                       gGs)
                     (\ x -> Sum_Type.Inl (snd x)))
                   (\ _ ->
                     let {
                       sts = concatMap
                               (\ (a, b) ->
                                 (case a of {
                                   (sa, t) ->
                                     (\ (aa, ba) ->
                                       sct_entry_to_sts sa t aa ba);
                                 })
                                   b)
                               gGs;
                     } in Error_Monad.bind
                            (Generic_Usable_Rules_Impl.smart_usable_rules_checker_impl
                              i dpp
                              (Error_Monad.isOK (Term_Order_Impl.ce_compat rp))
                              pi u_opt sts)
                            (\ u ->
                              Error_Monad.bind
                                (Error_Monad.catch_error
                                  (Error_Monad.catch_error
                                    (Error_Monad.forallM ns u)
                                    (\ x -> Sum_Type.Inl (snd x)))
                                  (\ x ->
                                    Sum_Type.Inl
                                      (Shows_Literal.showsl_lit
 "problem when orienting usable rules\n" .
x)))
                                (\ _ ->
                                  let {
                                    eidg =
                                      Dependency_Graph_Impl.is_iedg_edge_dpp i
dpp;
                                  } in Error_Monad.bind
 (Error_Monad.catch_error (Check_Monad.check_subseteq p (map fst gs))
   (\ x ->
     Sum_Type.Inl
       (Shows_Literal.showsl_lit "there is no size-change graph for DP " .
         Trs_Impl.showsl_rule x)))
 (\ _ ->
   let {
     n = List.size_list p;
     nums = List.upt Arith.zero_nat n;
     numPs = zip p nums;
     num_of = fun_of_default numPs n;
   } in Check_Monad.check
          (Size_Change_Termination.check_SCT
            (\ (_, succs) (uv, _) -> List.member succs uv)
            (map (\ (st, (stri, nstri)) ->
                   let {
                     eidg_st = eidg st;
                     ia = num_of st;
                     e = (ia, List.map_filter
                                (\ x ->
                                  (if ((eidg_st . fst) . fst) x
                                    then Just (snd x) else Nothing))
                                numPs);
                   } in Size_Change_Termination.Scg e e stri nstri)
              gGs))
          (Shows_Literal.showsl_lit "size-change analysis failed\n"))))))))
    (\ x ->
      Sum_Type.Inl
        (((Shows_Literal.showsl_lit
             "could not apply the size-change processor with the following\n" .
            Term_Order_Impl.desc rp) .
           Shows_Literal.showsl_lit "\nfor the following reason\n") .
          x));

sct_subterm_precise_proc ::
  forall a b.
    (Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b
                                  [Str.Char] () ->
                                  [((Term.Term b [Str.Char],
                                      Term.Term b [Str.Char]),
                                     ([(Arith.Nat, Arith.Nat)],
                                       [(Arith.Nat, Arith.Nat)]))] ->
                                    a -> Sum_Type.Sum (String -> String) ();
sct_subterm_precise_proc i gs dpp =
  Error_Monad.catch_error
    (let {
       p = Dependency_Pair_Problem_Spec.pairs i dpp;
       is_def =
         (\ fn -> not (null (Dependency_Pair_Problem_Spec.rules_map i dpp fn)));
       eidg = Dependency_Graph_Impl.is_iedg_edge_dpp i dpp;
     } in Error_Monad.bind
            (Error_Monad.catch_error (Check_Monad.check_subseteq p (map fst gs))
              (\ x ->
                Sum_Type.Inl
                  (Shows_Literal.showsl_lit
                     "there is no size-change graph for the pair " .
                    Trs_Impl.showsl_rule x)))
            (\ _ ->
              let {
                gGs = filter (\ g -> List.member p (fst g)) gs;
              } in Error_Monad.bind
                     (Check_Monad.check
                       (Dependency_Pair_Problem_Spec.minimal i dpp ||
                         Dependency_Pair_Problem_Spec.nFQ_subset_NF_rules i dpp)
                       (Shows_Literal.showsl_lit
                         "minimality or innermost required"))
                     (\ _ ->
                       Error_Monad.bind
                         (Error_Monad.catch_error
                           (Error_Monad.forallM
                             (\ (l, _) -> Term_Impl.check_no_var l)
                             (Dependency_Pair_Problem_Spec.rules i dpp))
                           (\ x -> Sum_Type.Inl (snd x)))
                         (\ _ ->
                           Error_Monad.bind
                             (Error_Monad.catch_error
                               (Error_Monad.forallM
                                 (\ (a, b) ->
                                   (case a of {
                                     (s, t) ->
                                       (\ (stri, nstri) ->
 Error_Monad.catch_error
   (Error_Monad.bind (Term_Impl.check_no_var s)
     (\ _ ->
       Error_Monad.bind (Term_Impl.check_no_var t)
         (\ _ ->
           Error_Monad.bind
             (Q_Restricted_Rewriting_Impl.check_no_defined_root is_def t)
             (\ _ ->
               let {
                 m = List.size_list (Term.args t);
                 n = List.size_list (Term.args s);
               } in Error_Monad.bind
                      (Error_Monad.catch_error
                        (Error_Monad.forallM
                          (\ (ia, j) ->
                            Check_Monad.check
                              (Arith.less_eq_nat ia n &&
                                Arith.less_eq_nat j m &&
                                  Error_Monad.isOK
                                    (Term_Impl.check_supt
                                      (Size_Change_Termination_Processors.get_arg
s ia)
                                      (Size_Change_Termination_Processors.get_arg
t j)))
                              ((((Shows_Literal.showsl_lit
                                    "problem with edge " .
                                   Shows_Literal.showsl_nat ia) .
                                  Shows_Literal.showsl_lit " |> ") .
                                 Shows_Literal.showsl_nat j) .
                                Shows_Literal.showsl_literal "\n"))
                          stri)
                        (\ x -> Sum_Type.Inl (snd x)))
                      (\ _ ->
                        Error_Monad.catch_error
                          (Error_Monad.forallM
                            (\ (ia, j) ->
                              Check_Monad.check
                                (Arith.less_eq_nat ia n &&
                                  Arith.less_eq_nat j m &&
                                    Error_Monad.isOK
                                      (Term_Impl.check_supteq
(Size_Change_Termination_Processors.get_arg s ia)
(Size_Change_Termination_Processors.get_arg t j)))
                                ((((Shows_Literal.showsl_lit
                                      "problem with edge " .
                                     Shows_Literal.showsl_nat ia) .
                                    Shows_Literal.showsl_lit " |>= ") .
                                   Shows_Literal.showsl_nat j) .
                                  Shows_Literal.showsl_literal "\n"))
                            nstri)
                          (\ x -> Sum_Type.Inl (snd x)))))))
   (\ x ->
     Sum_Type.Inl
       (((Shows_Literal.showsl_lit "problem with pair " .
           Trs_Impl.showsl_rule (s, t)) .
          Shows_Literal.showsl_literal "\n") .
         x)));
                                   })
                                     b)
                                 gGs)
                               (\ x -> Sum_Type.Inl (snd x)))
                             (\ _ ->
                               let {
                                 n = List.size_list p;
                                 nums = List.upt Arith.zero_nat n;
                                 numPs = zip p nums;
                                 num_of = fun_of_default numPs n;
                               } in Check_Monad.check
                                      (Size_Change_Termination.check_SCT
(\ (_, succs) (uv, _) -> List.member succs uv)
(map (\ (st, (stri, nstri)) ->
       let {
         eidg_st = eidg st;
         ia = num_of st;
         e = (ia, List.map_filter
                    (\ x ->
                      (if ((eidg_st . fst) . fst) x then Just (snd x)
                        else Nothing))
                    numPs);
       } in Size_Change_Termination.Scg e e (Missing_List.remdups_sort stri)
              (Missing_List.remdups_sort nstri))
  gGs))
                                      (Shows_Literal.showsl_lit
"size-change analysis failed\n"))))))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "could not apply the size-change processor based on the subterm-relation\n" .
          x));

sct_subterm_approx_proc ::
  forall a b.
    (Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b
                                  [Str.Char] () ->
                                  [((Term.Term b [Str.Char],
                                      Term.Term b [Str.Char]),
                                     ([(Arith.Nat, Arith.Nat)],
                                       [(Arith.Nat, Arith.Nat)]))] ->
                                    a -> Sum_Type.Sum (String -> String) ();
sct_subterm_approx_proc i gs dpp =
  Error_Monad.catch_error
    (let {
       p = Dependency_Pair_Problem_Spec.pairs i dpp;
       is_def =
         (\ fn -> not (null (Dependency_Pair_Problem_Spec.rules_map i dpp fn)));
     } in Error_Monad.bind
            (Error_Monad.catch_error (Check_Monad.check_subseteq p (map fst gs))
              (\ x ->
                Sum_Type.Inl
                  (Shows_Literal.showsl_lit
                     "there is no size-change graph for the pair " .
                    Trs_Impl.showsl_rule x)))
            (\ _ ->
              let {
                gGs = filter (\ g -> List.member p (fst g)) gs;
              } in Error_Monad.bind
                     (Check_Monad.check
                       (Dependency_Pair_Problem_Spec.minimal i dpp ||
                         Dependency_Pair_Problem_Spec.nFQ_subset_NF_rules i dpp)
                       (Shows_Literal.showsl_lit
                         "minimality or innermost required"))
                     (\ _ ->
                       Error_Monad.bind
                         (Error_Monad.catch_error
                           (Error_Monad.forallM
                             (\ (l, _) -> Term_Impl.check_no_var l)
                             (Dependency_Pair_Problem_Spec.rules i dpp))
                           (\ x -> Sum_Type.Inl (snd x)))
                         (\ _ ->
                           Error_Monad.bind
                             (Error_Monad.catch_error
                               (Error_Monad.forallM
                                 (\ (a, b) ->
                                   (case a of {
                                     (s, t) ->
                                       (\ (stri, nstri) ->
 Error_Monad.catch_error
   (Error_Monad.bind (Term_Impl.check_no_var s)
     (\ _ ->
       Error_Monad.bind (Term_Impl.check_no_var t)
         (\ _ ->
           Error_Monad.bind
             (Q_Restricted_Rewriting_Impl.check_no_defined_root is_def t)
             (\ _ ->
               let {
                 m = List.size_list (Term.args t);
                 n = List.size_list (Term.args s);
               } in Error_Monad.bind
                      (Error_Monad.catch_error
                        (Error_Monad.forallM
                          (\ (ia, j) ->
                            Check_Monad.check
                              (Arith.less_eq_nat ia n &&
                                Arith.less_eq_nat j m &&
                                  Error_Monad.isOK
                                    (Term_Impl.check_supt
                                      (Size_Change_Termination_Processors.get_arg
s ia)
                                      (Size_Change_Termination_Processors.get_arg
t j)))
                              ((((Shows_Literal.showsl_lit
                                    "problem with edge " .
                                   Shows_Literal.showsl_nat ia) .
                                  Shows_Literal.showsl_lit " |> ") .
                                 Shows_Literal.showsl_nat j) .
                                Shows_Literal.showsl_literal "\n"))
                          stri)
                        (\ x -> Sum_Type.Inl (snd x)))
                      (\ _ ->
                        Error_Monad.catch_error
                          (Error_Monad.forallM
                            (\ (ia, j) ->
                              Check_Monad.check
                                (Arith.less_eq_nat ia n &&
                                  Arith.less_eq_nat j m &&
                                    Error_Monad.isOK
                                      (Term_Impl.check_supteq
(Size_Change_Termination_Processors.get_arg s ia)
(Size_Change_Termination_Processors.get_arg t j)))
                                ((((Shows_Literal.showsl_lit
                                      "problem with edge " .
                                     Shows_Literal.showsl_nat ia) .
                                    Shows_Literal.showsl_lit " |>= ") .
                                   Shows_Literal.showsl_nat j) .
                                  Shows_Literal.showsl_literal "\n"))
                            nstri)
                          (\ x -> Sum_Type.Inl (snd x)))))))
   (\ x ->
     Sum_Type.Inl
       (((Shows_Literal.showsl_lit "problem with pair " .
           Trs_Impl.showsl_rule (s, t)) .
          Shows_Literal.showsl_literal "\n") .
         x)));
                                   })
                                     b)
                                 gGs)
                               (\ x -> Sum_Type.Inl (snd x)))
                             (\ _ ->
                               Check_Monad.check
                                 (Size_Change_Termination.check_SCT
                                   (\ (_, g) (h, _) -> g == h)
                                   (List.remdups
                                     (map (\ (st, (stri, nstri)) ->
    let {
      e = (Option.the (Term.root (fst st)), Option.the (Term.root (snd st)));
    } in Size_Change_Termination.Scg e e (Missing_List.remdups_sort stri)
           (Missing_List.remdups_sort nstri))
                                       gGs)))
                                 (Shows_Literal.showsl_lit
                                   "size-change analysis failed\n"))))))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "could not apply the size-change processor based on the subterm-relation\n" .
          x));

sct_subterm_proc ::
  forall a b.
    (Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b
                                  [Str.Char] () ->
                                  [((Term.Term b [Str.Char],
                                      Term.Term b [Str.Char]),
                                     ([(Arith.Nat, Arith.Nat)],
                                       [(Arith.Nat, Arith.Nat)]))] ->
                                    a -> Sum_Type.Sum (String -> String) ();
sct_subterm_proc i gs dpp =
  (if Error_Monad.isOK (sct_subterm_approx_proc i gs dpp) then Sum_Type.Inr ()
    else sct_subterm_precise_proc i gs dpp);

}
