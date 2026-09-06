{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  CSR_Frozen_Recursive_Subterm(csr_frozen_projection_index,
                                csr_projection_collapsing_afs,
                                csr_frozen_projection_pair_weak,
                                csr_frozen_projection_pair_strict,
                                csr_frozen_recursive_subterm_proc)
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
import qualified Check_Monad;
import qualified HOL;
import qualified Dependency_Pair_Problem_Spec;
import qualified Sum_Type;
import qualified Compare;
import qualified Context_Sensitive_Impl;
import qualified Subterm_Criterion_Impl;
import qualified CSR_Checker_Base;
import qualified Labelings;
import qualified Subterm_Criterion;
import qualified Term_Rewriting;
import qualified Arith;

csr_frozen_recursive_view ::
  forall a b.
    Term_Rewriting.Afs a ->
      ((a, Arith.Nat) -> Arith.Nat) ->
        Term_Rewriting.Term a b -> Term_Rewriting.Term a b;
csr_frozen_recursive_view pi p t =
  Term_Rewriting.af_term pi (Subterm_Criterion.proj_term p t);

csr_frozen_projection_index ::
  forall a b c.
    (Eq a,
      Eq b) => ((Labelings.Lab a b, Arith.Nat) -> Arith.Set Arith.Nat) ->
                 Labelings.Lab a b ->
                   ((Labelings.Lab a b, Arith.Nat) -> Arith.Nat) ->
                     Term_Rewriting.Term (Labelings.Lab a b) c -> Bool;
csr_frozen_projection_index mu u p t =
  (case t of {
    Term_Rewriting.Var _ -> False;
    Term_Rewriting.Fun (Labelings.Lab lab l) ts ->
      Labelings.equal_lab (Labelings.Lab lab l) u &&
        Arith.equal_nat (Arith.size_list ts) Arith.one_nat &&
          Arith.equal_nat (p (Labelings.Lab lab l, Arith.one_nat))
            Arith.zero_nat;
    Term_Rewriting.Fun (Labelings.FunLab lab lista) ts ->
      Labelings.equal_lab (Labelings.FunLab lab lista) u &&
        Arith.equal_nat (Arith.size_list ts) Arith.one_nat &&
          Arith.equal_nat (p (Labelings.FunLab lab lista, Arith.one_nat))
            Arith.zero_nat;
    Term_Rewriting.Fun (Labelings.UnLab fa) ts ->
      Labelings.equal_lab (Labelings.UnLab fa) u &&
        Arith.equal_nat (Arith.size_list ts) Arith.one_nat &&
          Arith.equal_nat (p (Labelings.UnLab fa, Arith.one_nat))
            Arith.zero_nat;
    Term_Rewriting.Fun (Labelings.Sharp f) ts ->
      Arith.less_nat (p (Labelings.Sharp f, Arith.size_list ts))
        (Arith.size_list ts) &&
        not (Arith.member (p (Labelings.Sharp f, Arith.size_list ts))
              (CSR_Checker_Base.csr_dp_root_mu mu
                (Labelings.Sharp f, Arith.size_list ts)));
  });

csr_projection_collapsing_afs ::
  forall a.
    Subterm_Criterion_Impl.ProjL a ->
      [((a, Arith.Nat), Term_Rewriting.Af_entry)];
csr_projection_collapsing_afs (Subterm_Criterion_Impl.Projection xs) =
  map (\ (fn, i) -> (fn, Term_Rewriting.Collapse i)) xs;

csr_frozen_projection_pair_weak ::
  forall a b.
    (Eq a,
      Eq b) => Term_Rewriting.Afs a ->
                 ((a, Arith.Nat) -> Arith.Nat) ->
                   (Term_Rewriting.Term a b, Term_Rewriting.Term a b) -> Bool;
csr_frozen_projection_pair_weak pi p lr =
  (case lr of {
    (l, r) ->
      Term_Rewriting.equal_term (csr_frozen_recursive_view pi p l)
        (csr_frozen_recursive_view pi p r) ||
        Arith.membera
          (Term_Rewriting.supt_list (csr_frozen_recursive_view pi p l))
          (csr_frozen_recursive_view pi p r);
  });

csr_frozen_projection_pair_valid ::
  forall a b c d.
    (Eq a,
      Eq b) => [((Labelings.Lab a b, Arith.Nat), [Arith.Nat])] ->
                 Labelings.Lab a b ->
                   ((Labelings.Lab a b, Arith.Nat) -> Arith.Nat) ->
                     (Term_Rewriting.Term (Labelings.Lab a b) c,
                       Term_Rewriting.Term (Labelings.Lab a b) d) ->
                       Bool;
csr_frozen_projection_pair_valid mu u p lr =
  (case lr of {
    (l, r) ->
      csr_frozen_projection_index (Context_Sensitive_Impl.mu_of mu) u p l &&
        csr_frozen_projection_index (Context_Sensitive_Impl.mu_of mu) u p r;
  });

csr_frozen_projection_pair_strict ::
  forall a b.
    (Eq a,
      Eq b) => Term_Rewriting.Afs a ->
                 ((a, Arith.Nat) -> Arith.Nat) ->
                   (Term_Rewriting.Term a b, Term_Rewriting.Term a b) -> Bool;
csr_frozen_projection_pair_strict pi p lr =
  (case lr of {
    (l, r) ->
      Arith.membera
        (Term_Rewriting.supt_list (csr_frozen_recursive_view pi p l))
        (csr_frozen_recursive_view pi p r);
  });

csr_frozen_recursive_subterm_proc ::
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
csr_frozen_recursive_subterm_proc j u mu pL rseq pr dpp =
  (case Term_Rewriting.afs_of (csr_projection_collapsing_afs pL) of {
    Nothing ->
      Sum_Type.Inl (Term_Rewriting.showsl_lit "invalid recursive projection");
    Just pi ->
      (case let {
              p = Subterm_Criterion_Impl.create_proj pL;
              pa = Dependency_Pair_Problem_Spec.pairs j dpp;
            } in (case Dependency_Pair_Problem_Spec.split_pairs j dpp pr of {
                   (ps, pns) ->
                     Check_Monad.check
                       (null rseq &&
                         all (csr_frozen_projection_pair_valid mu u p) pa &&
                           all (csr_frozen_projection_pair_strict pi p) ps &&
                             all (csr_frozen_projection_pair_weak pi p) pns)
                       (Term_Rewriting.showsl_lit
                         "invalid frozen recursive CSR subterm criterion");
                 })
        of {
        Sum_Type.Inl a -> Sum_Type.Inl a;
        Sum_Type.Inr _ ->
          Sum_Type.Inr (Dependency_Pair_Problem_Spec.delete_P_Pw j dpp pr pr);
      });
  });

}
