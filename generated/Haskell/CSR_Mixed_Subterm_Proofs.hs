{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  CSR_Mixed_Subterm_Proofs(csr_mixed_subterm_proc, csr_mixed_unhiding_present)
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
import qualified CSR_Minimal_CSDP_Proofs;
import qualified CSR_Checker_Base;
import qualified Subterm_Criterion;
import qualified Check_Monad;
import qualified HOL;
import qualified Dependency_Pair_Problem_Spec;
import qualified Subterm_Criterion_Impl;
import qualified Sum_Type;
import qualified Compare;
import qualified Term_Rewriting;
import qualified Labelings;
import qualified Arith;

csr_mixed_projection_pair_strict ::
  forall a b.
    (Eq a,
      Eq b) => [((a, Arith.Nat), [Arith.Nat])] ->
                 ((a, Arith.Nat) -> Arith.Nat) ->
                   (Term_Rewriting.Term a b, Term_Rewriting.Term a b) -> Bool;
csr_mixed_projection_pair_strict mu p lr =
  (case lr of {
    (l, r) ->
      Arith.membera
        (CSR_Checker_Base.mu_supt_list mu (Subterm_Criterion.proj_term p l))
        (Subterm_Criterion.proj_term p r);
  });

csr_mixed_sct_index_check ::
  forall a b c.
    (Eq a,
      Eq b) => Labelings.Lab a b ->
                 Term_Rewriting.Term (Labelings.Lab a b) c -> Arith.Nat -> Bool;
csr_mixed_sct_index_check u (Term_Rewriting.Fun (Labelings.Sharp f) ts) i =
  Arith.less_nat Arith.zero_nat i && Arith.less_eq_nat i (Arith.size_list ts);
csr_mixed_sct_index_check u (Term_Rewriting.Fun (Labelings.Lab v va) ts) i =
  Labelings.equal_lab (Labelings.Lab v va) u &&
    Arith.equal_nat (Arith.size_list ts) Arith.one_nat &&
      Arith.equal_nat i Arith.one_nat;
csr_mixed_sct_index_check u (Term_Rewriting.Fun (Labelings.FunLab v va) ts) i =
  Labelings.equal_lab (Labelings.FunLab v va) u &&
    Arith.equal_nat (Arith.size_list ts) Arith.one_nat &&
      Arith.equal_nat i Arith.one_nat;
csr_mixed_sct_index_check u (Term_Rewriting.Fun (Labelings.UnLab v) ts) i =
  Labelings.equal_lab (Labelings.UnLab v) u &&
    Arith.equal_nat (Arith.size_list ts) Arith.one_nat &&
      Arith.equal_nat i Arith.one_nat;
csr_mixed_sct_index_check u (Term_Rewriting.Var v) i = False;

csr_mixed_projection_pair_valid ::
  forall a b c d.
    (Eq a,
      Eq b) => Labelings.Lab a b ->
                 ((Labelings.Lab a b, Arith.Nat) -> Arith.Nat) ->
                   (Term_Rewriting.Term (Labelings.Lab a b) c,
                     Term_Rewriting.Term (Labelings.Lab a b) d) ->
                     Bool;
csr_mixed_projection_pair_valid u p lr =
  (case lr of {
    (l, r) ->
      CSR_Minimal_CSDP_Proofs.csr_u3_mixed_term_check u l &&
        CSR_Minimal_CSDP_Proofs.csr_u3_mixed_term_check u r &&
          csr_mixed_sct_index_check u l
            (Arith.suc (p (Arith.the (Term_Rewriting.root l)))) &&
            csr_mixed_sct_index_check u r
              (Arith.suc (p (Arith.the (Term_Rewriting.root r))));
  });

csr_mixed_projection_pair_weak ::
  forall a b.
    (Eq a,
      Eq b) => [((a, Arith.Nat), [Arith.Nat])] ->
                 ((a, Arith.Nat) -> Arith.Nat) ->
                   (Term_Rewriting.Term a b, Term_Rewriting.Term a b) -> Bool;
csr_mixed_projection_pair_weak mu p lr =
  (case lr of {
    (l, r) ->
      Term_Rewriting.equal_term (Subterm_Criterion.proj_term p l)
        (Subterm_Criterion.proj_term p r) ||
        Arith.membera
          (CSR_Checker_Base.mu_supt_list mu (Subterm_Criterion.proj_term p l))
          (Subterm_Criterion.proj_term p r);
  });

csr_mixed_subterm_proc ::
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
csr_mixed_subterm_proc j u mu pL rseq pr dpp =
  (case let {
          p = Subterm_Criterion_Impl.create_proj pL;
          pa = Dependency_Pair_Problem_Spec.pairs j dpp;
        } in (case Dependency_Pair_Problem_Spec.split_pairs j dpp pr of {
               (ps, pns) ->
                 Check_Monad.check
                   (null rseq &&
                     all (csr_mixed_projection_pair_valid u p) pa &&
                       all (csr_mixed_projection_pair_strict mu p) ps &&
                         all (csr_mixed_projection_pair_weak mu p) pns)
                   (Term_Rewriting.showsl_lit
                     "invalid mixed marked/unhiding CSR subterm criterion");
             })
    of {
    Sum_Type.Inl a -> Sum_Type.Inl a;
    Sum_Type.Inr _ ->
      Sum_Type.Inr (Dependency_Pair_Problem_Spec.delete_P_Pw j dpp pr pr);
  });

csr_mixed_unhiding_present ::
  forall a b c.
    (Eq a) => a -> [(Term_Rewriting.Term a b, Term_Rewriting.Term a c)] -> Bool;
csr_mixed_unhiding_present u p =
  any (\ (l, r) ->
        (case Term_Rewriting.root l of {
          Nothing -> False;
          Just (f, _) -> f == u;
        }) ||
          (case Term_Rewriting.root r of {
            Nothing -> False;
            Just (f, _) -> f == u;
          }))
    p;

}
