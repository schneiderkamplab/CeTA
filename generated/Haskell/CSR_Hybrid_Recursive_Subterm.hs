{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module CSR_Hybrid_Recursive_Subterm(csr_hybrid_recursive_subterm_proc) where {

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
import qualified Check_Monad;
import qualified Dependency_Pair_Problem_Spec;
import qualified Subterm_Criterion_Impl;
import qualified Sum_Type;
import qualified Compare;
import qualified CSR_Frozen_Recursive_Subterm;
import qualified Context_Sensitive_Impl;
import qualified HOL;
import qualified Term_Rewriting;
import qualified Labelings;
import qualified Arith;

csr_hybrid_one_layer_index_list ::
  forall a b c.
    (Eq a,
      Eq b) => ((Labelings.Lab a b, Arith.Nat) -> Arith.Set Arith.Nat) ->
                 [(Term_Rewriting.Term (Labelings.Lab a b) c,
                    Term_Rewriting.Term (Labelings.Lab a b) c)] ->
                   Term_Rewriting.Afs (Labelings.Lab a b) ->
                     Labelings.Lab a b ->
                       ((Labelings.Lab a b, Arith.Nat) -> Arith.Nat) ->
                         Term_Rewriting.Term (Labelings.Lab a b) c -> Bool;
csr_hybrid_one_layer_index_list mu r pi u p t =
  (case t of {
    Term_Rewriting.Var _ -> False;
    Term_Rewriting.Fun (Labelings.Lab _ _) _ -> False;
    Term_Rewriting.Fun (Labelings.FunLab _ _) _ -> False;
    Term_Rewriting.Fun (Labelings.UnLab _) _ -> False;
    Term_Rewriting.Fun (Labelings.Sharp f) ts ->
      let {
        i = p (Labelings.Sharp f, Arith.size_list ts);
      } in Arith.less_nat i (Arith.size_list ts) &&
             Arith.member i (mu (f, Arith.size_list ts)) &&
               (case Arith.nth ts i of {
                 Term_Rewriting.Var _ -> False;
                 Term_Rewriting.Fun g us ->
                   not (Arith.membera (Term_Rewriting.defined_list r)
                         (g, Arith.size_list us)) &&
                     (case Term_Rewriting.afs pi (g, Arith.size_list us) of {
                       Term_Rewriting.Collapse j ->
                         Arith.less_nat j (Arith.size_list us) &&
                           not (Arith.member j (mu (g, Arith.size_list us)));
                       Term_Rewriting.AFList _ -> False;
                     });
               });
  });

csr_hybrid_projection_pair_valid ::
  forall a b c.
    (Eq a,
      Eq b) => [((Labelings.Lab a b, Arith.Nat), [Arith.Nat])] ->
                 [(Term_Rewriting.Term (Labelings.Lab a b) c,
                    Term_Rewriting.Term (Labelings.Lab a b) c)] ->
                   Term_Rewriting.Afs (Labelings.Lab a b) ->
                     Labelings.Lab a b ->
                       ((Labelings.Lab a b, Arith.Nat) -> Arith.Nat) ->
                         (Term_Rewriting.Term (Labelings.Lab a b) c,
                           Term_Rewriting.Term (Labelings.Lab a b) c) ->
                           Bool;
csr_hybrid_projection_pair_valid mu r pi u p lr =
  (case lr of {
    (l, ra) ->
      (CSR_Frozen_Recursive_Subterm.csr_frozen_projection_index
         (Context_Sensitive_Impl.mu_of mu) u p l ||
        csr_hybrid_one_layer_index_list (Context_Sensitive_Impl.mu_of mu) r pi u
          p l) &&
        (CSR_Frozen_Recursive_Subterm.csr_frozen_projection_index
           (Context_Sensitive_Impl.mu_of mu) u p ra ||
          csr_hybrid_one_layer_index_list (Context_Sensitive_Impl.mu_of mu) r pi
            u p ra);
  });

csr_hybrid_recursive_subterm_proc ::
  forall a b c.
    (Compare.Compare_order b, Eq b, Term_Rewriting.Showl b,
      Compare.Compare_order c, Eq c,
      Term_Rewriting.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a
                                   (Labelings.Lab b c) [Arith.Char] () ->
                                   Labelings.Lab b c ->
                                     [((Labelings.Lab b c, Arith.Nat),
[Arith.Nat])] ->
                                       Subterm_Criterion_Impl.ProjL
 (Labelings.Lab b c) ->
 [((Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char],
     Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char]),
    [([Arith.Nat],
       ((Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char],
          Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char]),
         Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char]))])] ->
   [(Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char],
      Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char])] ->
     a -> Sum_Type.Sum (String -> String) a;
csr_hybrid_recursive_subterm_proc j u mu pL rseq pr dpp =
  (case Term_Rewriting.afs_of
          (CSR_Frozen_Recursive_Subterm.csr_projection_collapsing_afs pL)
    of {
    Nothing ->
      Sum_Type.Inl
        (Term_Rewriting.showsl_lit "invalid hybrid recursive projection");
    Just pi ->
      (case let {
              p = Subterm_Criterion_Impl.create_proj pL;
              pa = Dependency_Pair_Problem_Spec.pairs j dpp;
              r = Dependency_Pair_Problem_Spec.rules j dpp;
            } in (case Dependency_Pair_Problem_Spec.split_pairs j dpp pr of {
                   (ps, pns) ->
                     Check_Monad.check
                       (null rseq &&
                         all (csr_hybrid_projection_pair_valid mu r pi u p)
                           pa &&
                           all (CSR_Frozen_Recursive_Subterm.csr_frozen_projection_pair_strict
                                 pi p)
                             ps &&
                             all (CSR_Frozen_Recursive_Subterm.csr_frozen_projection_pair_weak
                                   pi p)
                               pns)
                       (Term_Rewriting.showsl_lit
                         "invalid hybrid recursive CSR subterm criterion");
                 })
        of {
        Sum_Type.Inl a -> Sum_Type.Inl a;
        Sum_Type.Inr _ ->
          Sum_Type.Inr (Dependency_Pair_Problem_Spec.delete_P_Pw j dpp pr pr);
      });
  });

}
