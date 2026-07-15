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
import qualified HOL;
import qualified Arith;
import qualified Term_Rewriting;

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
showsl_sig (ConstF n) = Term_Rewriting.showsl_nat n;
showsl_sig MaxF = Term_Rewriting.showsl_lit "max";
showsl_sig ProdF = Term_Rewriting.showsl_lit "prod";
showsl_sig SumF = Term_Rewriting.showsl_lit "sum";

showsl_list_sig :: [Sig] -> String -> String;
showsl_list_sig xs = Term_Rewriting.default_showsl_list showsl_sig xs;

instance Term_Rewriting.Showl Sig where {
  showsl = showsl_sig;
  showsl_list = showsl_list_sig;
};

to_IA ::
  forall a.
    Term_Rewriting.Term Sig a ->
      [Term_Rewriting.Term Term_Rewriting.Sig (a, Term_Rewriting.Ty)];
to_IA (Term_Rewriting.Var x) = [Term_Rewriting.Var (x, Term_Rewriting.IntT)];
to_IA (Term_Rewriting.Fun f ss) =
  (case f of {
    ConstF n ->
      [Term_Rewriting.Fun (Term_Rewriting.ConstF (Arith.int_of_nat n)) []];
    SumF ->
      (if null ss
        then [Term_Rewriting.Fun (Term_Rewriting.SumF Arith.zero_nat) []]
        else map (Term_Rewriting.Fun (Term_Rewriting.SumF (Arith.size_list ss)))
               (Arith.product_lists (map to_IA ss)));
    ProdF ->
      (if null ss
        then [Term_Rewriting.Fun (Term_Rewriting.ProdF Arith.zero_nat) []]
        else map (Term_Rewriting.Fun
                   (Term_Rewriting.ProdF (Arith.size_list ss)))
               (Arith.product_lists (map to_IA ss)));
    MaxF ->
      (if null ss
        then [Term_Rewriting.Fun (Term_Rewriting.ConstF Arith.zero_int) []]
        else concatMap to_IA ss);
  });

simplify ::
  forall a. (Eq a) => Term_Rewriting.Term Sig a -> Term_Rewriting.Term Sig a;
simplify (Term_Rewriting.Var x) = Term_Rewriting.Var x;
simplify (Term_Rewriting.Fun (ConstF n) ss) = Term_Rewriting.Fun (ConstF n) [];
simplify (Term_Rewriting.Fun SumF ss) =
  let {
    ssa = filter
            (\ s ->
              not (Term_Rewriting.equal_term s
                    (Term_Rewriting.Fun (ConstF Arith.zero_nat) [])))
            (map simplify ss);
  } in (case ssa of {
         [] -> Term_Rewriting.Fun (ConstF Arith.zero_nat) [];
         [s] -> s;
         _ : _ : _ -> Term_Rewriting.Fun SumF ssa;
       });
simplify (Term_Rewriting.Fun ProdF ss) =
  let {
    ssa = filter
            (\ s ->
              not (Term_Rewriting.equal_term s
                    (Term_Rewriting.Fun (ConstF Arith.one_nat) [])))
            (map simplify ss);
  } in (if Arith.membera ssa (Term_Rewriting.Fun (ConstF Arith.zero_nat) [])
         then Term_Rewriting.Fun (ConstF Arith.zero_nat) []
         else (case ssa of {
                [] -> Term_Rewriting.Fun (ConstF Arith.one_nat) [];
                [s] -> s;
                _ : _ : _ -> Term_Rewriting.Fun ProdF ssa;
              }));
simplify (Term_Rewriting.Fun MaxF ss) =
  let {
    ssa = filter
            (\ s ->
              not (Term_Rewriting.equal_term s
                    (Term_Rewriting.Fun (ConstF Arith.zero_nat) [])))
            (map simplify ss);
  } in (case ssa of {
         [] -> Term_Rewriting.Fun (ConstF Arith.zero_nat) [];
         [s] -> s;
         _ : _ : _ -> Term_Rewriting.Fun MaxF ssa;
       });

le_via_IA ::
  forall a.
    Term_Rewriting.Term Sig a ->
      Term_Rewriting.Term Sig a ->
        Term_Rewriting.Formula
          (Term_Rewriting.Term Term_Rewriting.Sig (a, Term_Rewriting.Ty));
le_via_IA s t =
  Term_Rewriting.form_or
    (Term_Rewriting.form_not
      (Term_Rewriting.Conjunction
        (map (\ x ->
               Term_Rewriting.Atom
                 (Term_Rewriting.Fun Term_Rewriting.LeF
                   [Term_Rewriting.Fun (Term_Rewriting.ConstF Arith.zero_int)
                      [],
                     Term_Rewriting.Var (x, Term_Rewriting.IntT)]))
          (Term_Rewriting.vars_term_list s ++
            Term_Rewriting.vars_term_list t))))
    (Term_Rewriting.Conjunction
      (map (\ sa ->
             Term_Rewriting.Disjunction
               (map (\ ta ->
                      Term_Rewriting.Atom
                        (Term_Rewriting.Fun Term_Rewriting.LeF [sa, ta]))
                 (to_IA t)))
        (to_IA s)));

less_via_IA ::
  forall a.
    Term_Rewriting.Term Sig a ->
      Term_Rewriting.Term Sig a ->
        Term_Rewriting.Formula
          (Term_Rewriting.Term Term_Rewriting.Sig (a, Term_Rewriting.Ty));
less_via_IA s t =
  Term_Rewriting.form_or
    (Term_Rewriting.form_not
      (Term_Rewriting.Conjunction
        (map (\ x ->
               Term_Rewriting.Atom
                 (Term_Rewriting.Fun Term_Rewriting.LeF
                   [Term_Rewriting.Fun (Term_Rewriting.ConstF Arith.zero_int)
                      [],
                     Term_Rewriting.Var (x, Term_Rewriting.IntT)]))
          (Term_Rewriting.vars_term_list s ++
            Term_Rewriting.vars_term_list t))))
    (Term_Rewriting.Conjunction
      (map (\ sa ->
             Term_Rewriting.Disjunction
               (map (\ ta ->
                      Term_Rewriting.Atom
                        (Term_Rewriting.Fun Term_Rewriting.LessF [sa, ta]))
                 (to_IA t)))
        (to_IA s)));

}
