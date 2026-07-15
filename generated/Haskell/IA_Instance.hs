{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module IA_Instance(check_termination) where {

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
import qualified LTS_Termination_Prover;
import qualified Phantom_Type;
import qualified Sum_Type;
import qualified Mapping;
import qualified Quasi_Order;
import qualified Arith;
import qualified Compare;
import qualified IA_Checker;
import qualified Term_Rewriting;

is_constant :: forall a b. Term_Rewriting.Term a b -> Bool;
is_constant (Term_Rewriting.Fun uu []) = True;
is_constant (Term_Rewriting.Var v) = False;
is_constant (Term_Rewriting.Fun v (vb : vc)) = False;

check_termination ::
  forall a b c.
    (Arith.Ccompare a, Compare.Compare a, Eq a, Mapping.Mapping_impl a,
      Quasi_Order.Linorder a, Term_Rewriting.Showl a, Arith.Cenum b,
      Arith.Ceq b, Arith.Ccompare b, Compare.Compare_order b, Eq b,
      Mapping.Mapping_impl b, Arith.Set_impl b, Term_Rewriting.Showl b,
      Arith.Ceq c, Arith.Ccompare c, Eq c, Mapping.Mapping_impl c,
      Arith.Set_impl c,
      Term_Rewriting.Showl c) => Term_Rewriting.Lts_impl Term_Rewriting.Sig a
                                   Term_Rewriting.Ty b c ->
                                   LTS_Termination_Prover.Termination_proof
                                     Term_Rewriting.Sig a Term_Rewriting.Ty b c
                                     IA_Checker.La_solver_type ->
                                     Sum_Type.Sum (String -> String) ();
check_termination =
  LTS_Termination_Prover.check Term_Rewriting.type_of_fun
    (Arith.insert Term_Rewriting.BoolT
      (Arith.set_empty (Phantom_Type.of_phantom Term_Rewriting.set_impl_ty)))
    IA_Checker.check_clause IA_Checker.check_clause Term_Rewriting.showsl_IA_exp
    Term_Rewriting.showsl_IA_exp IA_Checker.lit_normalize
    IA_Checker.lit_normalize Term_Rewriting.IntT
    (\ s t ->
      Term_Rewriting.Atom (Term_Rewriting.Fun Term_Rewriting.LeF [s, t]))
    (\ s t ->
      Term_Rewriting.Atom (Term_Rewriting.Fun Term_Rewriting.LessF [s, t]))
    is_constant Term_Rewriting.def_checker;

}
