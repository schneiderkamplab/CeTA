{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  CSR_GM_Transformation(Gm_extended_csr_termination_proof(..),
                         check_gm_extended_csr_termination_proof)
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
import qualified Context_Sensitive_Impl;
import qualified FOR_Preliminaries;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Map;
import qualified Dependency_Pair_Problem_Spec;
import qualified Termination_Problem_Spec;
import qualified Sum_Type;
import qualified Countable;
import qualified Compare;
import qualified HOL;
import qualified Name;
import qualified Term_Rewriting;
import qualified CSR_Conservative_Checker;
import qualified Check_Termination;
import qualified Labelings;
import qualified Arith;

data Gm_extended_csr_termination_proof a b c =
  Existing_CSR_Proof
    (CSR_Conservative_Checker.Extended_csr_termination_proof a b c)
  | GM_CSR_Transformation (Labelings.Lab a b) (Labelings.Lab a b)
      [((Labelings.Lab a b, Arith.Nat), Labelings.Lab a b)]
      (Check_Termination.Trs_termination_proof a b c);

gm_nf ::
  forall a b.
    (Arith.Ceq a,
      Arith.Ccompare a) => ((a, Arith.Nat) -> Arith.Set Arith.Nat) ->
                             Arith.Set (a, Arith.Nat) ->
                               ((a, Arith.Nat) -> a) ->
                                 a -> Term_Rewriting.Term a b ->
Term_Rewriting.Term a b;
gm_nf mu d act mark (Term_Rewriting.Var x) =
  Term_Rewriting.Fun mark [Term_Rewriting.Var x];
gm_nf mu d act mark (Term_Rewriting.Fun f ts) =
  Term_Rewriting.Fun
    (if Arith.member (f, Arith.size_list ts) d then act (f, Arith.size_list ts)
      else f)
    (gm_nf_args mu d act mark f (Arith.size_list ts) Arith.zero_nat ts);

gm_nf_args ::
  forall a b.
    (Arith.Ceq a,
      Arith.Ccompare a) => ((a, Arith.Nat) -> Arith.Set Arith.Nat) ->
                             Arith.Set (a, Arith.Nat) ->
                               ((a, Arith.Nat) -> a) ->
                                 a -> a ->
Arith.Nat ->
  Arith.Nat -> [Term_Rewriting.Term a b] -> [Term_Rewriting.Term a b];
gm_nf_args mu d act mark f n i [] = [];
gm_nf_args mu d act mark f n i (t : ts) =
  (if Arith.member i (mu (f, n)) then gm_nf mu d act mark t else t) :
    gm_nf_args mu d act mark f n (Arith.suc i) ts;

gm_lhs ::
  forall a b.
    (Arith.Ceq a,
      Arith.Ccompare a) => Arith.Set (a, Arith.Nat) ->
                             ((a, Arith.Nat) -> a) ->
                               Term_Rewriting.Term a b ->
                                 Term_Rewriting.Term a b;
gm_lhs d act (Term_Rewriting.Var x) = Term_Rewriting.Var x;
gm_lhs d act (Term_Rewriting.Fun f ts) =
  Term_Rewriting.Fun
    (if Arith.member (f, Arith.size_list ts) d then act (f, Arith.size_list ts)
      else f)
    ts;

gm_rule ::
  forall a b c.
    (Arith.Ceq a,
      Arith.Ccompare a) => ((a, Arith.Nat) -> Arith.Set Arith.Nat) ->
                             Arith.Set (a, Arith.Nat) ->
                               ((a, Arith.Nat) -> a) ->
                                 a -> (Term_Rewriting.Term a b,
Term_Rewriting.Term a c) ->
(Term_Rewriting.Term a b, Term_Rewriting.Term a c);
gm_rule mu d act mark lr =
  (gm_lhs d act (fst lr), gm_nf mu d act mark (snd lr));

gm_vars :: forall a. Arith.Nat -> [Term_Rewriting.Term a [Arith.Char]];
gm_vars n = map Term_Rewriting.Var (Name.x_1_to_x_n n);

gm_mark_rule ::
  forall a.
    (Arith.Ceq a,
      Arith.Ccompare a) => ((a, Arith.Nat) -> Arith.Set Arith.Nat) ->
                             Arith.Set (a, Arith.Nat) ->
                               ((a, Arith.Nat) -> a) ->
                                 a -> (a, Arith.Nat) ->
(Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char]);
gm_mark_rule mu d act mark fn =
  let {
    f = fst fn;
    n = snd fn;
    xs = gm_vars n;
  } in (Term_Rewriting.Fun mark [Term_Rewriting.Fun f xs],
         gm_nf mu d act mark (Term_Rewriting.Fun f xs));

gm_deactivate_rule ::
  forall a.
    ((a, Arith.Nat) -> a) ->
      (a, Arith.Nat) ->
        (Term_Rewriting.Term a [Arith.Char],
          Term_Rewriting.Term a [Arith.Char]);
gm_deactivate_rule act fn =
  let {
    f = fst fn;
    n = snd fn;
    xs = gm_vars n;
  } in (Term_Rewriting.Fun (act fn) xs, Term_Rewriting.Fun f xs);

gm_transformed_rules_list ::
  forall a.
    (Arith.Ceq a,
      Arith.Ccompare a) => ((a, Arith.Nat) -> Arith.Set Arith.Nat) ->
                             Arith.Set (a, Arith.Nat) ->
                               ((a, Arith.Nat) -> a) ->
                                 a -> [(a, Arith.Nat)] ->
[(Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char])] ->
  [(a, Arith.Nat)] ->
    [(Term_Rewriting.Term a [Arith.Char], Term_Rewriting.Term a [Arith.Char])];
gm_transformed_rules_list mu d act mark f r ds =
  map (gm_rule mu d act mark) r ++
    map (gm_mark_rule mu d act mark) f ++ map (gm_deactivate_rule act) ds;

check_gm_extended_csr_termination_proof ::
  forall a b c.
    (Compare.Compare_order b, Countable.Countable b, Eq b,
      Term_Rewriting.Showl b) => Termination_Problem_Spec.Tp_ops_ext a
                                   (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                   () ->
                                   Dependency_Pair_Problem_Spec.Dpp_ops_ext c
                                     (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                     () ->
                                     Bool ->
                                       (String -> String) ->
 [((Labelings.Lab b [Arith.Nat], Arith.Nat), [Arith.Nat])] ->
   [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
      Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
     Gm_extended_csr_termination_proof b [Arith.Nat] [Arith.Char] ->
       Sum_Type.Sum (String -> String) ();
check_gm_extended_csr_termination_proof ia j a i mu r (Existing_CSR_Proof prf) =
  CSR_Conservative_Checker.check_extended_csr_termination_proof ia j a i mu r
    prf;
check_gm_extended_csr_termination_proof ia j a i mu r
  (GM_CSR_Transformation mark c active prf) =
  FOR_Preliminaries.debug i "Giesl-Middeldorp CSR transformation"
    (Error_Monad.bind (Term_Rewriting.check_wf_trs r)
      (\ _ ->
        let {
          d = Term_Rewriting.defined_list r;
          f = Arith.remdups (Term_Rewriting.funas_trs_list r);
        } in Error_Monad.bind
               (Check_Monad.check
                 (Arith.distinct (map fst active) &&
                   Arith.set_eq (Arith.set (map fst active)) (Arith.set d))
                 (Term_Rewriting.showsl_lit
                   "active-symbol map does not cover the defined signature exactly"))
               (\ _ ->
                 Error_Monad.bind
                   (Check_Monad.check (Arith.membera f (c, Arith.zero_nat))
                     (Term_Rewriting.showsl_lit
                       "ground source-signature constant is missing"))
                   (\ _ ->
                     let {
                       act = (\ fn -> Arith.the (Map.map_of active fn));
                       t = gm_transformed_rules_list
                             (Context_Sensitive_Impl.mu_of mu) (Arith.set d) act
                             mark f r d;
                     } in Check_Termination.check_trs_termination_proof ia j
                            False (Term_Rewriting.add_index i Arith.one_nat)
                            (Termination_Problem_Spec.mk ia False [] t [])
                            prf))));

}
