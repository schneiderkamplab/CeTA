{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Term_Order_Impl(Rel_impl_ext(..), Rel_impl_type(..), prc_nat, prl_nat, s,
                   rel_impl_s, sn, af, ns, rel_impl_ns, rel_impl_of,
                   showsl_funa, cpx, nst, rel_impl_nst, desc, mono, valid,
                   no_complexity_check, faulty_rel_impl, top_af, co_rewr,
                   mono_af, not_sst, not_wst, subst_s, standard,
                   rel_impl_redpair, top_refl, ce_compat, rel_impl_redtriple,
                   rel_impl_mono_redpair, rel_impl_root_redtriple,
                   rel_impl_co_rewrite_pair, rel_impl_mono_ce_redpair,
                   rel_impl_co_discrimination_pair,
                   rel_impl_quasi_reduction_triple)
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
import qualified Trs;
import qualified Term_Order;
import qualified Shows_Literal;
import qualified Error_Monad;
import qualified HOL;
import qualified Complexity;
import qualified Sum_Type;
import qualified Term;
import qualified Set;
import qualified Arith;

data Rel_impl_ext a b c =
  Rel_impl_ext (Sum_Type.Sum (String -> String) ())
    (Sum_Type.Sum (String -> String) ()) (String -> String)
    ((Term.Term a b, Term.Term a b) -> Sum_Type.Sum (String -> String) ())
    ((Term.Term a b, Term.Term a b) -> Sum_Type.Sum (String -> String) ())
    ((Term.Term a b, Term.Term a b) -> Sum_Type.Sum (String -> String) ())
    ((a, Arith.Nat) -> Set.Set Arith.Nat) ((a, Arith.Nat) -> Set.Set Arith.Nat)
    (Sum_Type.Sum (String -> String) ()) (Sum_Type.Sum (String -> String) ())
    (Sum_Type.Sum (String -> String) ()) (Sum_Type.Sum (String -> String) ())
    (Sum_Type.Sum (String -> String) ()) (Sum_Type.Sum (String -> String) ())
    ((a, Arith.Nat) -> Set.Set Arith.Nat)
    ([(a, Arith.Nat)] -> Sum_Type.Sum (String -> String) ())
    (Maybe [(a, Arith.Nat)]) (Maybe [(a, Arith.Nat)])
    (Complexity.Complexity_measure a b ->
      Complexity.Complexity_class -> Sum_Type.Sum (String -> String) ())
    c;

newtype Rel_impl_type b a c = Abs_rel_impl_type (c -> Rel_impl_ext b a ());

prc_nat ::
  forall a.
    ((a, Arith.Nat) -> Arith.Nat) ->
      (a, Arith.Nat) -> (a, Arith.Nat) -> (Bool, Bool);
prc_nat pr = (\ f g -> let {
                         pf = pr f;
                         pg = pr g;
                       } in (Arith.less_nat pg pf, Arith.less_eq_nat pg pf));

prl_nat :: forall a. ((a, Arith.Nat) -> Arith.Nat) -> (a, Arith.Nat) -> Bool;
prl_nat pr = (\ f -> Arith.equal_nat (pr f) Arith.zero_nat);

s :: forall a b c.
       Rel_impl_ext a b c ->
         (Term.Term a b, Term.Term a b) -> Sum_Type.Sum (String -> String) ();
s (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
    co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = s;

rel_impl_s ::
  forall a b.
    Rel_impl_ext a b () ->
      [(Term.Term a b, Term.Term a b)] -> Sum_Type.Sum (String -> String) ();
rel_impl_s ri =
  (\ xs ->
    Error_Monad.catch_error (Error_Monad.forallM (s ri) xs)
      (\ x -> Sum_Type.Inl (snd x)));

sn :: forall a b c. Rel_impl_ext a b c -> Sum_Type.Sum (String -> String) ();
sn (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
     co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = sn;

af :: forall a b c. Rel_impl_ext a b c -> (a, Arith.Nat) -> Set.Set Arith.Nat;
af (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
     co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = af;

ns :: forall a b c.
        Rel_impl_ext a b c ->
          (Term.Term a b, Term.Term a b) -> Sum_Type.Sum (String -> String) ();
ns (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
     co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = ns;

rel_impl_ns ::
  forall a b.
    Rel_impl_ext a b () ->
      [(Term.Term a b, Term.Term a b)] -> Sum_Type.Sum (String -> String) ();
rel_impl_ns ri =
  (\ xs ->
    Error_Monad.catch_error (Error_Monad.forallM (ns ri) xs)
      (\ x -> Sum_Type.Inl (snd x)));

rep_rel_impl_type ::
  forall b a c. Rel_impl_type b a c -> c -> Rel_impl_ext b a ();
rep_rel_impl_type (Abs_rel_impl_type x) = x;

rel_impl_of :: forall a b c. Rel_impl_type a b c -> c -> Rel_impl_ext a b ();
rel_impl_of xa = rep_rel_impl_type xa;

showsl_funa ::
  forall a. (Shows_Literal.Showl a) => (a, Arith.Nat) -> String -> String;
showsl_funa (f, n) =
  (Shows_Literal.showsl f . Shows_Literal.showsl_lit "/") .
    Shows_Literal.showsl_nat n;

cpx ::
  forall a b c.
    Rel_impl_ext a b c ->
      Complexity.Complexity_measure a b ->
        Complexity.Complexity_class -> Sum_Type.Sum (String -> String) ();
cpx (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
      co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = cpx;

nst ::
  forall a b c.
    Rel_impl_ext a b c ->
      (Term.Term a b, Term.Term a b) -> Sum_Type.Sum (String -> String) ();
nst (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
      co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = nst;

rel_impl_nst ::
  forall a b.
    Rel_impl_ext a b () ->
      [(Term.Term a b, Term.Term a b)] -> Sum_Type.Sum (String -> String) ();
rel_impl_nst ri =
  (\ xs ->
    Error_Monad.catch_error (Error_Monad.forallM (nst ri) xs)
      (\ x -> Sum_Type.Inl (snd x)));

desc :: forall a b c. Rel_impl_ext a b c -> String -> String;
desc (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
       co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = desc;

mono ::
  forall a b c.
    Rel_impl_ext a b c ->
      [(a, Arith.Nat)] -> Sum_Type.Sum (String -> String) ();
mono (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
       co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = mono;

valid :: forall a b c. Rel_impl_ext a b c -> Sum_Type.Sum (String -> String) ();
valid (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
        co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = valid;

no_complexity_check :: forall a b. a -> b -> Sum_Type.Sum (String -> String) ();
no_complexity_check =
  (\ _ _ ->
    Sum_Type.Inl
      (Shows_Literal.showsl_literal "complexity analysis unsupported"));

faulty_rel_impl ::
  forall a b.
    HOL.Itself a ->
      HOL.Itself b ->
        (String -> String) -> (String -> String) -> Rel_impl_ext a b ();
faulty_rel_impl uu uv err desc =
  Rel_impl_ext (Sum_Type.Inl err) (Sum_Type.Inr ()) desc
    (\ _ -> Sum_Type.Inr ()) (\ _ -> Sum_Type.Inr ()) (\ _ -> Sum_Type.Inr ())
    Term_Order.full_af Term_Order.full_af (Sum_Type.Inr ()) (Sum_Type.Inr ())
    (Sum_Type.Inr ()) (Sum_Type.Inr ()) (Sum_Type.Inr ()) (Sum_Type.Inr ())
    Term_Order.empty_af (\ _ -> Sum_Type.Inr ()) Nothing Nothing
    no_complexity_check ();

top_af ::
  forall a b c. Rel_impl_ext a b c -> (a, Arith.Nat) -> Set.Set Arith.Nat;
top_af
  (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
    co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = top_af;

co_rewr ::
  forall a b c. Rel_impl_ext a b c -> Sum_Type.Sum (String -> String) ();
co_rewr
  (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
    co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = co_rewr;

mono_af ::
  forall a b c. Rel_impl_ext a b c -> (a, Arith.Nat) -> Set.Set Arith.Nat;
mono_af
  (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
    co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = mono_af;

not_sst :: forall a b c. Rel_impl_ext a b c -> Maybe [(a, Arith.Nat)];
not_sst
  (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
    co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = not_sst;

not_wst :: forall a b c. Rel_impl_ext a b c -> Maybe [(a, Arith.Nat)];
not_wst
  (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
    co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = not_wst;

subst_s ::
  forall a b c. Rel_impl_ext a b c -> Sum_Type.Sum (String -> String) ();
subst_s
  (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
    co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = subst_s;

standard ::
  forall a b c. Rel_impl_ext a b c -> Sum_Type.Sum (String -> String) ();
standard
  (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
    co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = standard;

rel_impl_redpair ::
  forall a b. Rel_impl_ext a b () -> Sum_Type.Sum (String -> String) ();
rel_impl_redpair ri =
  Error_Monad.catch_error
    (Error_Monad.bind (valid ri)
      (\ _ ->
        Error_Monad.bind (standard ri)
          (\ _ ->
            Error_Monad.bind
              (Error_Monad.catch_error (sn ri)
                (\ x ->
                  Sum_Type.Inl
                    (x . Shows_Literal.showsl_lit
                           "\nproblem in ensuring strong normalization of relation")))
              (\ _ ->
                Error_Monad.catch_error (subst_s ri)
                  (\ x ->
                    Sum_Type.Inl
                      (x . Shows_Literal.showsl_lit
                             "\nproblem in ensuring stability of strict relation"))))))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit "problem with being a reduction pair\n" . x));

top_mono ::
  forall a b c. Rel_impl_ext a b c -> Sum_Type.Sum (String -> String) ();
top_mono
  (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
    co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = top_mono;

top_refl ::
  forall a b c. Rel_impl_ext a b c -> Sum_Type.Sum (String -> String) ();
top_refl
  (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
    co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = top_refl;

ce_compat ::
  forall a b c. Rel_impl_ext a b c -> Sum_Type.Sum (String -> String) ();
ce_compat
  (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
    co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = ce_compat;

rel_impl_redtriple ::
  forall a b. Rel_impl_ext a b () -> Sum_Type.Sum (String -> String) ();
rel_impl_redtriple ri =
  Error_Monad.catch_error
    (Error_Monad.bind (valid ri)
      (\ _ ->
        Error_Monad.bind (standard ri)
          (\ _ ->
            Error_Monad.bind
              (Error_Monad.catch_error (top_refl ri)
                (\ x ->
                  Sum_Type.Inl
                    (x . Shows_Literal.showsl_lit
                           "\nproblem in ensuring reflexivity of top-non-strict relation")))
              (\ _ ->
                Error_Monad.bind
                  (Error_Monad.catch_error (sn ri)
                    (\ x ->
                      Sum_Type.Inl
                        (x . Shows_Literal.showsl_lit
                               "\nproblem in ensuring strong normalization of relation")))
                  (\ _ ->
                    Error_Monad.catch_error (subst_s ri)
                      (\ x ->
                        Sum_Type.Inl
                          (x . Shows_Literal.showsl_lit
                                 "\nproblem in ensuring stability of strict relation")))))))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit "problem with being a reduction triple\n" .
          x));

rel_impl_mono_redpair ::
  forall a b.
    Rel_impl_ext a b () ->
      [(Term.Term a b, Term.Term a b)] ->
        [(Term.Term a b, Term.Term a b)] -> Sum_Type.Sum (String -> String) ();
rel_impl_mono_redpair ri s ns =
  Error_Monad.catch_error
    (Error_Monad.bind (valid ri)
      (\ _ ->
        Error_Monad.bind (standard ri)
          (\ _ ->
            Error_Monad.bind
              (Error_Monad.catch_error (sn ri)
                (\ x ->
                  Sum_Type.Inl
                    (x . Shows_Literal.showsl_lit
                           "\nproblem in ensuring strong normalization of relation")))
              (\ _ ->
                Error_Monad.bind
                  (Error_Monad.catch_error (subst_s ri)
                    (\ x ->
                      Sum_Type.Inl
                        (x . Shows_Literal.showsl_lit
                               "\nproblem in ensuring stability of strict relation")))
                  (\ _ ->
                    Error_Monad.catch_error
                      (mono ri (Trs.funas_trs_list (s ++ ns)))
                      (\ x ->
                        Sum_Type.Inl
                          (x . Shows_Literal.showsl_lit
                                 "\nproblem in ensuring monotonicity of strict relation")))))))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "problem with being a monotone reduction pair\n" .
          x));

rel_impl_root_redtriple ::
  forall a b. Rel_impl_ext a b () -> Sum_Type.Sum (String -> String) ();
rel_impl_root_redtriple ri =
  Error_Monad.catch_error
    (Error_Monad.bind (valid ri)
      (\ _ ->
        Error_Monad.bind
          (Error_Monad.catch_error (sn ri)
            (\ x ->
              Sum_Type.Inl
                (x . Shows_Literal.showsl_lit
                       "\nproblem in ensuring strong normalization of relation")))
          (\ _ ->
            Error_Monad.bind
              (Error_Monad.catch_error (subst_s ri)
                (\ x ->
                  Sum_Type.Inl
                    (x . Shows_Literal.showsl_lit
                           "\nproblem in ensuring stability of strict relation")))
              (\ _ ->
                Error_Monad.catch_error (top_mono ri)
                  (\ x ->
                    Sum_Type.Inl
                      (x . Shows_Literal.showsl_lit
                             "\nproblem in monotonicity from non-root to root"))))))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "problem with being a root-reduction triple\n" .
          x));

rel_impl_co_rewrite_pair ::
  forall a b. Rel_impl_ext a b () -> Sum_Type.Sum (String -> String) ();
rel_impl_co_rewrite_pair ri =
  Error_Monad.catch_error
    (Error_Monad.bind (valid ri)
      (\ _ ->
        Error_Monad.bind
          (Error_Monad.catch_error (co_rewr ri)
            (\ x ->
              Sum_Type.Inl
                (x . Shows_Literal.showsl_lit
                       "\nproblem in ensuring disjointness property")))
          (\ _ ->
            Error_Monad.catch_error (subst_s ri)
              (\ x ->
                Sum_Type.Inl
                  (x . Shows_Literal.showsl_lit
                         "\nproblem in ensuring stability of strict relation")))))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit "problem with being a co-rewrite pair\n" .
          x));

rel_impl_mono_ce_redpair ::
  forall a b.
    Rel_impl_ext a b () ->
      [(Term.Term a b, Term.Term a b)] ->
        [(Term.Term a b, Term.Term a b)] -> Sum_Type.Sum (String -> String) ();
rel_impl_mono_ce_redpair ri s ns =
  Error_Monad.catch_error
    (Error_Monad.bind (valid ri)
      (\ _ ->
        Error_Monad.bind (standard ri)
          (\ _ ->
            Error_Monad.bind
              (Error_Monad.catch_error (sn ri)
                (\ x ->
                  Sum_Type.Inl
                    (x . Shows_Literal.showsl_lit
                           "\nproblem in ensuring strong normalization of relation")))
              (\ _ ->
                Error_Monad.bind
                  (Error_Monad.catch_error (subst_s ri)
                    (\ x ->
                      Sum_Type.Inl
                        (x . Shows_Literal.showsl_lit
                               "\nproblem in ensuring stability of strict relation")))
                  (\ _ ->
                    Error_Monad.bind
                      (Error_Monad.catch_error (ce_compat ri)
                        (\ x ->
                          Sum_Type.Inl
                            (x . Shows_Literal.showsl_lit
                                   "\nproblem in ensuring ce-compatibility")))
                      (\ _ ->
                        Error_Monad.catch_error
                          (mono ri (Trs.funas_trs_list (s ++ ns)))
                          (\ x ->
                            Sum_Type.Inl
                              (x . Shows_Literal.showsl_lit
                                     "\nproblem in ensuring monotonicity of strict relation"))))))))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "problem with being a ce-compatible monotone reduction pair\n" .
          x));

rel_impl_co_discrimination_pair ::
  forall a b. Rel_impl_ext a b () -> Sum_Type.Sum (String -> String) ();
rel_impl_co_discrimination_pair ri =
  Error_Monad.catch_error
    (Error_Monad.bind (valid ri)
      (\ _ ->
        Error_Monad.catch_error (co_rewr ri)
          (\ x ->
            Sum_Type.Inl
              (x . Shows_Literal.showsl_lit
                     "\nproblem in ensuring disjointness property"))))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "problem with being a co-discrimination pair\n" .
          x));

rel_impl_quasi_reduction_triple ::
  forall a b. Rel_impl_ext a b () -> Sum_Type.Sum (String -> String) ();
rel_impl_quasi_reduction_triple ri =
  Error_Monad.catch_error
    (Error_Monad.bind (valid ri)
      (\ _ ->
        Error_Monad.bind
          (Error_Monad.catch_error (subst_s ri)
            (\ x ->
              Sum_Type.Inl
                (x . Shows_Literal.showsl_lit
                       "\nproblem in ensuring stability of strict relation")))
          (\ _ ->
            Error_Monad.bind
              (Error_Monad.catch_error (sn ri)
                (\ x ->
                  Sum_Type.Inl
                    (x . Shows_Literal.showsl_lit
                           "\nproblem in ensuring strong normalization of strict relation")))
              (\ _ ->
                Error_Monad.bind
                  (Error_Monad.catch_error (top_mono ri)
                    (\ x ->
                      Sum_Type.Inl
                        (x . Shows_Literal.showsl_lit
                               "\nproblem in ensuring top-monotonicity of non-strict relations")))
                  (\ _ ->
                    Error_Monad.catch_error (top_refl ri)
                      (\ x ->
                        Sum_Type.Inl
                          (x . Shows_Literal.showsl_lit
                                 "\nproblem in ensuring top-reflexivity")))))))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "problem with being a quasi-reduction triple\n" .
          x));

}
