{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Instantiation_Impl(Instantiation_complete_proc_prf(..), instantiation_proc,
                      forward_instantiation_proc, instantiation_complete_proc)
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
import qualified Innermost_Usable_Rules_Impl;
import qualified Dependency_Graph_Impl;
import qualified Icap_Impl;
import qualified Icap;
import qualified HOL;
import qualified Dependency_Pair_Problem_Spec;
import qualified Compare;
import qualified Error_Monad;
import qualified Check_Monad;
import qualified Sum_Type;
import qualified Mapping;
import qualified Arith;
import qualified Shows_Literal;
import qualified Term_Rewriting;

newtype Instantiation_complete_proc_prf a b = Instantiation_complete_proc_prf
  [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];

check_instance ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => [(Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b)] ->
                                  [(Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b)] ->
                                    Sum_Type.Sum (String -> String) ();
check_instance pa p =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ st ->
        Check_Monad.check (any (Term_Rewriting.instance_rule st) pa)
          (Term_Rewriting.showsl_rule st .
            Shows_Literal.showsl_lit
              " is not an instance of any original pair"))
      p)
    (\ x -> Sum_Type.Inl (snd x));

instantiation_proc ::
  forall a b.
    (Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b
                                  [Arith.Char] () ->
                                  (Term_Rewriting.Term b [Arith.Char],
                                    Term_Rewriting.Term b [Arith.Char]) ->
                                    [(Term_Rewriting.Term b [Arith.Char],
                                       Term_Rewriting.Term b [Arith.Char])] ->
                                      a -> Sum_Type.Sum (String -> String) a;
instantiation_proc i st sts dpp =
  (case let {
          ic = Icap_Impl.icap_impl_dpp_mv i dpp;
          isnf = Dependency_Pair_Problem_Spec.is_QNF i dpp;
        } in (case st of {
               (s, t) ->
                 let {
                   sy = Term_Rewriting.map_term (\ x -> x)
                          (\ a -> Arith.char_0x79 : a) s;
                   ty = Term_Rewriting.map_term (\ x -> x)
                          (\ a -> Arith.char_0x79 : a) t;
                   iedg = Dependency_Graph_Impl.is_iedg_edge_dpp i dpp;
                 } in Error_Monad.catch_error
                        (Error_Monad.forallM
                          (\ (u, v) ->
                            (case Icap.mgu_class (ic [u] v) s of {
                              Nothing -> Sum_Type.Inr ();
                              Just mu ->
                                Check_Monad.check
                                  (not (isnf
 (Term_Rewriting.eval_term Term_Rewriting.Fun sy mu)) ||
                                    (not (isnf
   (Term_Rewriting.eval_term Term_Rewriting.Fun
     (Term_Rewriting.map_term (\ x -> x) (\ a -> Arith.char_0x78 : a) u) mu)) ||
                                      any
(\ sta ->
  Term_Rewriting.instance_rule sta st &&
    Term_Rewriting.instance_rule
      (Term_Rewriting.eval_term Term_Rewriting.Fun sy mu,
        Term_Rewriting.eval_term Term_Rewriting.Fun ty mu)
      sta)
sts))
                                  (((Shows_Literal.showsl_lit
                                       "could not find instance of pair " .
                                      Term_Rewriting.showsl_rule
(Term_Rewriting.eval_term Term_Rewriting.Fun sy mu,
  Term_Rewriting.eval_term Term_Rewriting.Fun ty mu)) .
                                     Shows_Literal.showsl_lit
                                       "\nwhich resulted from DP ") .
                                    Term_Rewriting.showsl_rule (u, v));
                            }))
                          (filter (\ (u, v) -> iedg (u, v) s)
                            (Dependency_Pair_Problem_Spec.pairs i dpp)))
                        (\ x -> Sum_Type.Inl (snd x));
             })
    of {
    Sum_Type.Inl a -> Sum_Type.Inl a;
    Sum_Type.Inr _ ->
      Sum_Type.Inr (Dependency_Pair_Problem_Spec.replace_pair i dpp st sts);
  });

forward_instantiation_proc ::
  forall a b.
    (Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b
                                  [Arith.Char] () ->
                                  (Term_Rewriting.Term b [Arith.Char],
                                    Term_Rewriting.Term b [Arith.Char]) ->
                                    [(Term_Rewriting.Term b [Arith.Char],
                                       Term_Rewriting.Term b [Arith.Char])] ->
                                      Maybe [(Term_Rewriting.Term b
        [Arith.Char],
       Term_Rewriting.Term b [Arith.Char])] ->
a -> Sum_Type.Sum (String -> String) a;
forward_instantiation_proc i st sts u_opt dpp =
  (case let {
          isnf = Dependency_Pair_Problem_Spec.is_QNF i dpp;
        } in (case st of {
               (s, t) ->
                 let {
                   iedg = Dependency_Graph_Impl.is_iedg_edge_dpp i dpp (s, t);
                   sy = Term_Rewriting.map_term (\ x -> x)
                          (\ a -> Arith.char_0x79 : a) s;
                   ty = Term_Rewriting.map_term (\ x -> x)
                          (\ a -> Arith.char_0x79 : a) t;
                   u = (case u_opt of {
                         Nothing -> Dependency_Pair_Problem_Spec.rules i dpp;
                         Just u -> u;
                       });
                 } in Error_Monad.bind
                        (if Arith.is_none u_opt then Sum_Type.Inr ()
                          else let {
                                 urc = Innermost_Usable_Rules_Impl.is_ur_closed_impl_dpp_mv
 i dpp u;
                                 check_urc =
                                   (\ sa ta ->
                                     Check_Monad.check (urc sa ta)
                                       ((Shows_Literal.showsl_lit "term " .
  Term_Rewriting.showsl_terma ta) .
 Shows_Literal.showsl_lit " is not closed under usable rules"));
                               } in Error_Monad.bind
                                      (Check_Monad.check
(Dependency_Pair_Problem_Spec.nfs i dpp ||
  Dependency_Pair_Problem_Spec.minimal i dpp)
(Shows_Literal.showsl_lit "minimality or normal subst required"))
                                      (\ _ ->
Error_Monad.bind
  (Check_Monad.check (Dependency_Pair_Problem_Spec.nFQ_subset_NF_rules i dpp)
    (Shows_Literal.showsl_lit "innermost rewriting required"))
  (\ _ ->
    Error_Monad.bind
      (Error_Monad.catch_error
        (Error_Monad.forallM (\ (l, a) -> check_urc (Term_Rewriting.args l) a)
          u)
        (\ x -> Sum_Type.Inl (snd x)))
      (\ _ ->
        Error_Monad.bind (check_urc [s] t)
          (\ _ ->
            (if Dependency_Pair_Problem_Spec.nfs i dpp then Sum_Type.Inr ()
              else Error_Monad.catch_error
                     (Check_Monad.check_subseteq
                       (Term_Rewriting.vars_term_list t)
                       (Term_Rewriting.vars_term_list s))
                     (\ _ ->
                       Sum_Type.Inl
                         (Shows_Literal.showsl_lit
                           "variable condition in pair violated"))))))))
                        (\ _ ->
                          let {
                            ur = map (\ (l, r) -> (r, l)) u;
                            ic = Icap_Impl.icap_impl
                                   (Term_Rewriting.is_NF_terms []) ur [];
                          } in Error_Monad.catch_error
                                 (Error_Monad.forallM
                                   (\ (ua, v) ->
                                     (case Icap.mgu_class (ic ua) t of {
                                       Nothing -> Sum_Type.Inr ();
                                       Just mu ->
 Check_Monad.check
   (not (isnf (Term_Rewriting.eval_term Term_Rewriting.Fun sy mu)) ||
     (not (isnf (Term_Rewriting.eval_term Term_Rewriting.Fun
                  (Term_Rewriting.map_term (\ x -> x)
                    (\ a -> Arith.char_0x78 : a) ua)
                  mu)) ||
       any (\ sta ->
             Term_Rewriting.instance_rule sta st &&
               Term_Rewriting.instance_rule
                 (Term_Rewriting.eval_term Term_Rewriting.Fun sy mu,
                   Term_Rewriting.eval_term Term_Rewriting.Fun ty mu)
                 sta)
         sts))
   (((Shows_Literal.showsl_lit "could not find instance of pair " .
       Term_Rewriting.showsl_rule
         (Term_Rewriting.eval_term Term_Rewriting.Fun sy mu,
           Term_Rewriting.eval_term Term_Rewriting.Fun ty mu)) .
      Shows_Literal.showsl_lit "\nwhich resulted from DP ") .
     Term_Rewriting.showsl_rule (ua, v));
                                     }))
                                   (filter (\ (ua, _) -> iedg ua)
                                     (Dependency_Pair_Problem_Spec.pairs i
                                       dpp)))
                                 (\ x -> Sum_Type.Inl (snd x)));
             })
    of {
    Sum_Type.Inl a -> Sum_Type.Inl a;
    Sum_Type.Inr _ ->
      Sum_Type.Inr (Dependency_Pair_Problem_Spec.replace_pair i dpp st sts);
  });

instantiation_complete_proc ::
  forall a b c d.
    (Eq b, Shows_Literal.Showl b, Arith.Ccompare c, Eq c,
      Mapping.Mapping_impl c,
      Shows_Literal.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b c
                                  d ->
                                  a -> Instantiation_complete_proc_prf b c ->
 Sum_Type.Sum (String -> String) a;
instantiation_complete_proc i dpp (Instantiation_complete_proc_prf p) =
  let {
    pa = Dependency_Pair_Problem_Spec.pairs i dpp;
    q = Dependency_Pair_Problem_Spec.q i dpp;
    r = Dependency_Pair_Problem_Spec.rules i dpp;
    nfs = Dependency_Pair_Problem_Spec.nfs i dpp;
  } in Error_Monad.bind
         (Check_Monad.check (not nfs || null q)
           (Shows_Literal.showsl_lit
             "normal form subst. currently not supported for innermost"))
         (\ _ ->
           Error_Monad.bind (check_instance pa p)
             (\ _ ->
               Sum_Type.Inr
                 (Dependency_Pair_Problem_Spec.mk i nfs False p [] q [] r)));

}
