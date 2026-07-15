{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Equational_Reasoning_Impl(showsl_eq, showsl_eqs, eq_proof_lines,
                             check_subsumption_guided, check_subsumption,
                             check_single_subsumption)
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
import qualified Check_Joins;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Mapping;
import qualified Compare;
import qualified HOL;
import qualified Equational_Reasoning;
import qualified Arith;
import qualified Term_Rewriting;
import qualified Shows_Literal;

showsl_eq ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => (Term_Rewriting.Term a b,
                                  Term_Rewriting.Term a b) ->
                                  String -> String;
showsl_eq =
  Term_Rewriting.showsl_rulea Shows_Literal.showsl Shows_Literal.showsl " = ";

showsl_ln :: Arith.Nat -> String -> String;
showsl_ln i =
  (Shows_Literal.showsl_literal "\n" . Shows_Literal.showsl_nat i) .
    Shows_Literal.showsl_lit ": ";

showsl_eqs ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => [(Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b)] ->
                                  String -> String;
showsl_eqs =
  Term_Rewriting.showsl_trsa Shows_Literal.showsl Shows_Literal.showsl
    "equational system:" " = ";

eq_proof_lines ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => Equational_Reasoning.Eq_proof a b ->
                                  Arith.Nat ->
                                    (String -> String,
                                      (Arith.Nat,
(Term_Rewriting.Term a b, Term_Rewriting.Term a b)));
eq_proof_lines (Equational_Reasoning.Refl s) i =
  ((showsl_ln (Arith.suc i) . showsl_eq (s, s)) .
     Shows_Literal.showsl_lit " [refl]",
    (Arith.suc i, (s, s)));
eq_proof_lines (Equational_Reasoning.Sym p) i =
  (case eq_proof_lines p i of {
    (s, (ia, (l, r))) ->
      (((((s . showsl_ln (Arith.suc ia)) . showsl_eq (r, l)) .
          Shows_Literal.showsl_lit " [sym ") .
         Shows_Literal.showsl_nat ia) .
         Shows_Literal.showsl_lit "]",
        (Arith.suc ia, (r, l)));
  });
eq_proof_lines (Equational_Reasoning.Trans p1 p2) i =
  (case eq_proof_lines p1 i of {
    (s1, (i1, (s, _))) ->
      (case eq_proof_lines p2 i1 of {
        (s2, (i2, (_, v))) ->
          ((((((((s1 . s2) . showsl_ln (Arith.suc i2)) . showsl_eq (s, v)) .
                Shows_Literal.showsl_lit " [trans ") .
               Shows_Literal.showsl_nat i1) .
              Shows_Literal.showsl_lit ", ") .
             Shows_Literal.showsl_nat i2) .
             Shows_Literal.showsl_lit "]",
            (Arith.suc i2, (s, v)));
      });
  });
eq_proof_lines (Equational_Reasoning.Assm (l, r) sigma) i =
  let {
    eq = (Term_Rewriting.eval_term Term_Rewriting.Fun l sigma,
           Term_Rewriting.eval_term Term_Rewriting.Fun r sigma);
  } in ((((showsl_ln (Arith.suc i) . showsl_eq eq) .
           Shows_Literal.showsl_lit " [assm ") .
          showsl_eq (l, r)) .
          Shows_Literal.showsl_lit "]",
         (Arith.suc i, eq));
eq_proof_lines (Equational_Reasoning.Cong f ps) i =
  (case eq_proofs_lines ps i of {
    (s, (is, (ls, rs))) ->
      let {
        eq = (Term_Rewriting.Fun f ls, Term_Rewriting.Fun f rs);
        ia = Arith.last is;
        isa = Arith.butlast is;
      } in (((s . showsl_ln (Arith.suc ia)) . showsl_eq eq) .
              Shows_Literal.showsl_list_gen Shows_Literal.showsl_nat " [cong]"
                " [cong " ", " "]" isa,
             (Arith.suc ia, eq));
  });

eq_proofs_lines ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => [Equational_Reasoning.Eq_proof a b] ->
                                  Arith.Nat ->
                                    (String -> String,
                                      ([Arith.Nat],
([Term_Rewriting.Term a b], [Term_Rewriting.Term a b])));
eq_proofs_lines [] i = (id, ([i], ([], [])));
eq_proofs_lines (p : ps) i =
  (case eq_proof_lines p i of {
    (s1, (ia, (l, r))) ->
      (case eq_proofs_lines ps ia of {
        (s2, (is, (ls, rs))) -> (s1 . s2, (ia : is, (l : ls, r : rs)));
      });
  });

check_subsumptions_guided ::
  forall a b.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a, Arith.Ccompare b,
      Compare.Compare b, Eq b, Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => [(Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b)] ->
                                  [((Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b),
                                     [Term_Rewriting.Term a b])] ->
                                    Sum_Type.Sum (String -> String) ();
check_subsumptions_guided e [] = Sum_Type.Inr ();
check_subsumptions_guided ea ((e, seq) : convs) =
  Error_Monad.bind
    (Error_Monad.catch_error
      (Check_Joins.check_conversion_sequence ea (fst e) (snd e) seq)
      (\ x ->
        Sum_Type.Inl
          (((Shows_Literal.showsl_lit "problem in conversion for equation " .
              showsl_eq e) .
             Shows_Literal.showsl_literal "\n") .
            x)))
    (\ _ -> check_subsumptions_guided (e : ea) convs);

check_subsumption_guided ::
  forall a b.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a, Arith.Ccompare b,
      Compare.Compare b, Eq b, Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => [(Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b)] ->
                                  [(Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b)] ->
                                    [((Term_Rewriting.Term a b,
Term_Rewriting.Term a b),
                                       [Term_Rewriting.Term a b])] ->
                                      Sum_Type.Sum (String -> String) ();
check_subsumption_guided ea e convs =
  Error_Monad.bind
    (Error_Monad.catch_error (Check_Monad.check_subseteq ea (map fst convs))
      (\ x ->
        Sum_Type.Inl
          (Shows_Literal.showsl_lit "could not find conversion for equation " .
            showsl_eq x)))
    (\ _ -> check_subsumptions_guided e convs);

check_subsumption_NF ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => [(Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b)] ->
                                  [(Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b)] ->
                                    Sum_Type.Sum (String -> String) ();
check_subsumption_NF e r =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ ea ->
        Error_Monad.catch_error
          (Term_Rewriting.check_join_NF r (fst ea) (snd ea))
          (\ x ->
            Sum_Type.Inl
              (((Shows_Literal.showsl_lit "could not join equation " .
                  showsl_eq ea) .
                 Shows_Literal.showsl_literal "\n") .
                x)))
      e)
    (\ x -> Sum_Type.Inl (snd x));

check_subsumption ::
  forall a b.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a, Arith.Ccompare b,
      Compare.Compare b, Eq b, Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => [(Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b)] ->
                                  [(Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b)] ->
                                    Maybe [((Term_Rewriting.Term a b,
      Term_Rewriting.Term a b),
     [Term_Rewriting.Term a b])] ->
                                      Sum_Type.Sum (String -> String) ();
check_subsumption e r convs_o = (case convs_o of {
                                  Nothing -> check_subsumption_NF e r;
                                  Just a -> check_subsumption_guided e r a;
                                });

check_single_subsumption ::
  forall a b.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a, Arith.Ccompare b,
      Compare.Compare b, Eq b, Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => (Term_Rewriting.Term a b,
                                  Term_Rewriting.Term a b) ->
                                  [(Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b)] ->
                                    [((Term_Rewriting.Term a b,
Term_Rewriting.Term a b),
                                       [Term_Rewriting.Term a b])] ->
                                      Sum_Type.Sum (String -> String) ();
check_single_subsumption eq e convs =
  Error_Monad.bind
    (Check_Monad.check (Arith.membera (map fst convs) eq)
      (Shows_Literal.showsl_lit "could not find conversion for equation " .
        showsl_eq eq))
    (\ _ -> check_subsumptions_guided e convs);

}
