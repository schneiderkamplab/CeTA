{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Reduction_Pair_Proc_Impl(rule_removal_tt, mono_redpair_proc,
                            mono_urm_redpair_proc)
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
import qualified Usable_Replacement_Map_Impl;
import qualified Check_Monad;
import qualified Compare;
import qualified Dependency_Pair_Problem_Spec;
import qualified Arith;
import qualified Error_Monad;
import qualified HOL;
import qualified Termination_Problem_Spec;
import qualified Sum_Type;
import qualified Term_Rewriting;
import qualified Shows_Literal;

rule_removal_tt ::
  forall a b c.
    (Shows_Literal.Showl b,
      Shows_Literal.Showl c) => Termination_Problem_Spec.Tp_ops_ext a b c () ->
                                  Term_Rewriting.Rel_impl_ext b c () ->
                                    [(Term_Rewriting.Term b c,
                                       Term_Rewriting.Term b c)] ->
                                      a -> Sum_Type.Sum (String -> String) a;
rule_removal_tt i rp rremove trs =
  (case Error_Monad.catch_error
          (case Termination_Problem_Spec.split_rules i trs rremove of {
            (rs, rns) ->
              Error_Monad.bind (Term_Rewriting.rel_impl_mono_redpair rp rs rns)
                (\ _ ->
                  Error_Monad.bind
                    (Error_Monad.catch_error (Term_Rewriting.rel_impl_ns rp rns)
                      (\ x ->
                        Sum_Type.Inl
                          (Shows_Literal.showsl_lit
                             "problem when orienting TRS\n" .
                            x)))
                    (\ _ ->
                      Error_Monad.catch_error (Term_Rewriting.rel_impl_s rp rs)
                        (\ x ->
                          Sum_Type.Inl
                            (Shows_Literal.showsl_lit
                               "problem when orienting TRS\n" .
                              x))));
          })
          (\ x ->
            Sum_Type.Inl
              (((Shows_Literal.showsl_lit
                   "could not apply the reduction pair processor with the following\n" .
                  Term_Rewriting.desc rp) .
                 Shows_Literal.showsl_literal "\n") .
                x))
    of {
    Sum_Type.Inl a -> Sum_Type.Inl a;
    Sum_Type.Inr _ ->
      Sum_Type.Inr (Termination_Problem_Spec.delete_R_Rw i trs rremove rremove);
  });

mono_redpair_proc ::
  forall a b c.
    (Shows_Literal.Showl b,
      Shows_Literal.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b c
                                  () ->
                                  Term_Rewriting.Rel_impl_ext b c () ->
                                    [(Term_Rewriting.Term b c,
                                       Term_Rewriting.Term b c)] ->
                                      [(Term_Rewriting.Term b c,
 Term_Rewriting.Term b c)] ->
a -> Sum_Type.Sum (String -> String) a;
mono_redpair_proc i rp premove rremove dpp =
  (case Error_Monad.catch_error
          (case Dependency_Pair_Problem_Spec.split_pairs i dpp premove of {
            (ps, pns) ->
              (case Dependency_Pair_Problem_Spec.split_rules i dpp rremove of {
                (rs, rns) ->
                  Error_Monad.bind
                    (Term_Rewriting.rel_impl_mono_redpair rp (ps ++ rs)
                      (pns ++ rns))
                    (\ _ ->
                      Error_Monad.bind
                        (Error_Monad.catch_error
                          (Term_Rewriting.rel_impl_ns rp rns)
                          (\ x ->
                            Sum_Type.Inl
                              (Shows_Literal.showsl_lit
                                 "problem when orienting TRS\n" .
                                x)))
                        (\ _ ->
                          Error_Monad.bind
                            (Error_Monad.catch_error
                              (Term_Rewriting.rel_impl_s rp rs)
                              (\ x ->
                                Sum_Type.Inl
                                  (Shows_Literal.showsl_lit
                                     "problem when orienting TRS\n" .
                                    x)))
                            (\ _ ->
                              Error_Monad.bind
                                (Error_Monad.catch_error
                                  (Term_Rewriting.rel_impl_ns rp pns)
                                  (\ x ->
                                    Sum_Type.Inl
                                      (Shows_Literal.showsl_lit
 "problem when orienting DPs\n" .
x)))
                                (\ _ ->
                                  Error_Monad.catch_error
                                    (Term_Rewriting.rel_impl_s rp ps)
                                    (\ x ->
                                      Sum_Type.Inl
(Shows_Literal.showsl_lit "problem when orienting DPs\n" . x))))));
              });
          })
          (\ x ->
            Sum_Type.Inl
              (((Shows_Literal.showsl_lit
                   "could not apply the reduction pair processor with the following\n" .
                  Term_Rewriting.desc rp) .
                 Shows_Literal.showsl_literal "\n") .
                x))
    of {
    Sum_Type.Inl a -> Sum_Type.Inl a;
    Sum_Type.Inr _ ->
      Sum_Type.Inr
        (Dependency_Pair_Problem_Spec.delete_R_Rw i
          (Dependency_Pair_Problem_Spec.delete_P_Pw i dpp premove premove)
          rremove rremove);
  });

mono_urm_redpair_proc ::
  forall a b.
    (Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b
                                  [Arith.Char] () ->
                                  Term_Rewriting.Rel_impl_ext b [Arith.Char]
                                    () ->
                                    [(Term_Rewriting.Term b [Arith.Char],
                                       Term_Rewriting.Term b [Arith.Char])] ->
                                      [(Term_Rewriting.Term b [Arith.Char],
 Term_Rewriting.Term b [Arith.Char])] ->
a -> Sum_Type.Sum (String -> String) a;
mono_urm_redpair_proc i rp premove rremove dpp =
  (case Error_Monad.catch_error
          (case Dependency_Pair_Problem_Spec.split_pairs i dpp premove of {
            (ps, pns) ->
              (case Dependency_Pair_Problem_Spec.split_rules i dpp rremove of {
                (rs, rns) ->
                  let {
                    r = Dependency_Pair_Problem_Spec.rules i dpp;
                    _ = Dependency_Pair_Problem_Spec.q i dpp;
                    p = Dependency_Pair_Problem_Spec.pairs i dpp;
                  } in Error_Monad.bind (Term_Rewriting.check_wf_trs p)
                         (\ _ ->
                           Error_Monad.bind (Term_Rewriting.check_wf_trs r)
                             (\ _ ->
                               Error_Monad.bind
                                 (Check_Monad.check
                                   (Dependency_Pair_Problem_Spec.nFQ_subset_NF_rules
                                     i dpp)
                                   (Shows_Literal.showsl_lit
                                     "innermost required"))
                                 (\ _ ->
                                   (case Usable_Replacement_Map_Impl.get_innermost_strict_repl_map_dpp
   i dpp rs
                                     of {
                                     (fs, (mu, info)) ->
                                       Error_Monad.bind
 (Term_Rewriting.rel_impl_redpair rp)
 (\ _ ->
   let {
     mua = Term_Rewriting.mono_af rp;
   } in Error_Monad.bind
          (Error_Monad.catch_error
            (Error_Monad.catch_error
              (Error_Monad.forallM
                (\ f ->
                  Check_Monad.check (Arith.less_eq_set (mu f) (mua f))
                    (((((Shows_Literal.showsl_lit
                           "error in monotonicity: strict order for " .
                          Shows_Literal.showsl_prod f) .
                         Shows_Literal.showsl_lit
                           " ensures monotonicity in positions ") .
                        Usable_Replacement_Map_Impl.showsl_position_set f
                          (mua f)) .
                       Shows_Literal.showsl_lit
                         "\nbut usable replacement map is ") .
                      Usable_Replacement_Map_Impl.showsl_position_set f (mu f)))
                fs)
              (\ x -> Sum_Type.Inl (snd x)))
            (\ x ->
              Sum_Type.Inl
                (((((x . Shows_Literal.showsl_lit
                           "\nthe computed usable replacement map (") .
                     Shows_Literal.showsl_literal info) .
                    Shows_Literal.showsl_lit ") is\n") .
                   Shows_Literal.showsl_sep
                     (\ f ->
                       ((Shows_Literal.showsl_lit "mu(" .
                          Shows_Literal.showsl_prod f) .
                         Shows_Literal.showsl_lit ") = ") .
                         Usable_Replacement_Map_Impl.showsl_position_set f
                           (mu f))
                     (Shows_Literal.showsl_literal "\n") fs) .
                  Shows_Literal.showsl_lit
                    "\nand mu(f) = {} for all other symbols f")))
          (\ _ ->
            Error_Monad.bind
              (Error_Monad.catch_error (Term_Rewriting.rel_impl_ns rp rns)
                (\ x ->
                  Sum_Type.Inl
                    (Shows_Literal.showsl_lit "problem when orienting TRS\n" .
                      x)))
              (\ _ ->
                Error_Monad.bind
                  (Error_Monad.catch_error (Term_Rewriting.rel_impl_s rp rs)
                    (\ x ->
                      Sum_Type.Inl
                        (Shows_Literal.showsl_lit
                           "problem when orienting TRS\n" .
                          x)))
                  (\ _ ->
                    Error_Monad.bind
                      (Error_Monad.catch_error
                        (Term_Rewriting.rel_impl_ns rp pns)
                        (\ x ->
                          Sum_Type.Inl
                            (Shows_Literal.showsl_lit
                               "problem when orienting DPs\n" .
                              x)))
                      (\ _ ->
                        Error_Monad.catch_error
                          (Term_Rewriting.rel_impl_s rp ps)
                          (\ x ->
                            Sum_Type.Inl
                              (Shows_Literal.showsl_lit
                                 "problem when orienting DPs\n" .
                                x)))))));
                                   }))));
              });
          })
          (\ x ->
            Sum_Type.Inl
              (((Shows_Literal.showsl_lit
                   "could not apply the reduction pair processor with usable repl. maps and the following\n" .
                  Term_Rewriting.desc rp) .
                 Shows_Literal.showsl_literal "\n") .
                x))
    of {
    Sum_Type.Inl a -> Sum_Type.Inl a;
    Sum_Type.Inr _ ->
      Sum_Type.Inr
        (Dependency_Pair_Problem_Spec.delete_R_Rw i
          (Dependency_Pair_Problem_Spec.delete_P_Pw i dpp premove premove)
          rremove rremove);
  });

}
