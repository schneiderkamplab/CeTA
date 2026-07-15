{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Max_Polynomial(Sig(..), simplify, le_via_IA, less_via_IA) where {

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
import qualified Term_More;
import qualified Formula;
import qualified HOL;
import qualified List;
import qualified Integer_Arithmetic;
import qualified Term;
import qualified Arith;
import qualified Shows_Literal;

data Sig = ConstF Arith.Nat | SumF | ProdF | MaxF;

equal_sig :: Sig -> Sig -> Bool;
equal_sig ProdF MaxF = False;
equal_sig MaxF ProdF = False;
equal_sig SumF MaxF = False;
equal_sig MaxF SumF = False;
equal_sig SumF ProdF = False;
equal_sig ProdF SumF = False;
equal_sig (ConstF x1) MaxF = False;
equal_sig MaxF (ConstF x1) = False;
equal_sig (ConstF x1) ProdF = False;
equal_sig ProdF (ConstF x1) = False;
equal_sig (ConstF x1) SumF = False;
equal_sig SumF (ConstF x1) = False;
equal_sig (ConstF x1) (ConstF y1) = Arith.equal_nat x1 y1;
equal_sig MaxF MaxF = True;
equal_sig ProdF ProdF = True;
equal_sig SumF SumF = True;

instance Eq Sig where {
  a == b = equal_sig a b;
};

showsl_sig :: Sig -> String -> String;
showsl_sig (ConstF n) = Shows_Literal.showsl_nat n;
showsl_sig MaxF = Shows_Literal.showsl_lit "max";
showsl_sig ProdF = Shows_Literal.showsl_lit "prod";
showsl_sig SumF = Shows_Literal.showsl_lit "sum";

showsl_list_sig :: [Sig] -> String -> String;
showsl_list_sig xs = Shows_Literal.default_showsl_list showsl_sig xs;

instance Shows_Literal.Showl Sig where {
  showsl = showsl_sig;
  showsl_list = showsl_list_sig;
};

to_IA ::
  forall a.
    Term.Term Sig a ->
      [Term.Term Integer_Arithmetic.Sig (a, Integer_Arithmetic.Ty)];
to_IA (Term.Var x) = [Term.Var (x, Integer_Arithmetic.IntT)];
to_IA (Term.Fun f ss) =
  (case f of {
    ConstF n -> [Term.Fun (Integer_Arithmetic.ConstF (Arith.int_of_nat n)) []];
    SumF ->
      (if null ss then [Term.Fun (Integer_Arithmetic.SumF Arith.zero_nat) []]
        else map (Term.Fun (Integer_Arithmetic.SumF (List.size_list ss)))
               (List.product_lists (map to_IA ss)));
    ProdF ->
      (if null ss then [Term.Fun (Integer_Arithmetic.ProdF Arith.zero_nat) []]
        else map (Term.Fun (Integer_Arithmetic.ProdF (List.size_list ss)))
               (List.product_lists (map to_IA ss)));
    MaxF ->
      (if null ss then [Term.Fun (Integer_Arithmetic.ConstF Arith.zero_int) []]
        else concatMap to_IA ss);
  });

simplify :: forall a. (Eq a) => Term.Term Sig a -> Term.Term Sig a;
simplify (Term.Var x) = Term.Var x;
simplify (Term.Fun (ConstF n) ss) = Term.Fun (ConstF n) [];
simplify (Term.Fun SumF ss) =
  let {
    ssa = filter
            (\ s ->
              not (Term.equal_term s (Term.Fun (ConstF Arith.zero_nat) [])))
            (map simplify ss);
  } in (case ssa of {
         [] -> Term.Fun (ConstF Arith.zero_nat) [];
         [s] -> s;
         _ : _ : _ -> Term.Fun SumF ssa;
       });
simplify (Term.Fun ProdF ss) =
  let {
    ssa = filter
            (\ s ->
              not (Term.equal_term s (Term.Fun (ConstF Arith.one_nat) [])))
            (map simplify ss);
  } in (if List.member ssa (Term.Fun (ConstF Arith.zero_nat) [])
         then Term.Fun (ConstF Arith.zero_nat) []
         else (case ssa of {
                [] -> Term.Fun (ConstF Arith.one_nat) [];
                [s] -> s;
                _ : _ : _ -> Term.Fun ProdF ssa;
              }));
simplify (Term.Fun MaxF ss) =
  let {
    ssa = filter
            (\ s ->
              not (Term.equal_term s (Term.Fun (ConstF Arith.zero_nat) [])))
            (map simplify ss);
  } in (case ssa of {
         [] -> Term.Fun (ConstF Arith.zero_nat) [];
         [s] -> s;
         _ : _ : _ -> Term.Fun MaxF ssa;
       });

le_via_IA ::
  forall a.
    Term.Term Sig a ->
      Term.Term Sig a ->
        Formula.Formula
          (Term.Term Integer_Arithmetic.Sig (a, Integer_Arithmetic.Ty));
le_via_IA s t =
  Formula.form_or
    (Formula.form_not
      (Formula.Conjunction
        (map (\ x ->
               Formula.Atom
                 (Term.Fun Integer_Arithmetic.LeF
                   [Term.Fun (Integer_Arithmetic.ConstF Arith.zero_int) [],
                     Term.Var (x, Integer_Arithmetic.IntT)]))
          (Term_More.vars_term_list s ++ Term_More.vars_term_list t))))
    (Formula.Conjunction
      (map (\ sa ->
             Formula.Disjunction
               (map (\ ta ->
                      Formula.Atom (Term.Fun Integer_Arithmetic.LeF [sa, ta]))
                 (to_IA t)))
        (to_IA s)));

less_via_IA ::
  forall a.
    Term.Term Sig a ->
      Term.Term Sig a ->
        Formula.Formula
          (Term.Term Integer_Arithmetic.Sig (a, Integer_Arithmetic.Ty));
less_via_IA s t =
  Formula.form_or
    (Formula.form_not
      (Formula.Conjunction
        (map (\ x ->
               Formula.Atom
                 (Term.Fun Integer_Arithmetic.LeF
                   [Term.Fun (Integer_Arithmetic.ConstF Arith.zero_int) [],
                     Term.Var (x, Integer_Arithmetic.IntT)]))
          (Term_More.vars_term_list s ++ Term_More.vars_term_list t))))
    (Formula.Conjunction
      (map (\ sa ->
             Formula.Disjunction
               (map (\ ta ->
                      Formula.Atom (Term.Fun Integer_Arithmetic.LessF [sa, ta]))
                 (to_IA t)))
        (to_IA s)));

}
