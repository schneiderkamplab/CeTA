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
import qualified Formula;
import qualified Sum_Type;
import qualified Set;
import qualified Mapping_Impl;
import qualified Collection_Order;
import qualified Collection_Enum;
import qualified Shows_Literal;
import qualified Orderings;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Compare;
import qualified Integer_Arithmetic;
import qualified IA_Checker;
import qualified Container_Setup;
import qualified LTS;
import qualified Term;

is_constant :: forall a b. Term.Term a b -> Bool;
is_constant (Term.Fun uu []) = True;
is_constant (Term.Var v) = False;
is_constant (Term.Fun v (vb : vc)) = False;

check_termination ::
  forall a b c.
    (Collection_Order.Ccompare a, Compare.Compare a, Eq a,
      Mapping_Impl.Mapping_impl a, Orderings.Linorder a, Shows_Literal.Showl a,
      Collection_Enum.Cenum b, Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Compare.Compare_order b, Eq b, Mapping_Impl.Mapping_impl b,
      Set_Impl.Set_impl b, Shows_Literal.Showl b, Collection_Eq.Ceq c,
      Collection_Order.Ccompare c, Eq c, Mapping_Impl.Mapping_impl c,
      Set_Impl.Set_impl c,
      Shows_Literal.Showl c) => LTS.Lts_impl Integer_Arithmetic.Sig a
                                  Integer_Arithmetic.Ty b c ->
                                  LTS_Termination_Prover.Termination_proof
                                    Integer_Arithmetic.Sig a
                                    Integer_Arithmetic.Ty b c
                                    IA_Checker.La_solver_type ->
                                    Sum_Type.Sum (String -> String) ();
check_termination =
  LTS_Termination_Prover.check Integer_Arithmetic.type_of_fun
    (Set.insert Integer_Arithmetic.BoolT
      (Set_Impl.set_empty
        (Phantom_Type.of_phantom Container_Setup.set_impl_ty)))
    IA_Checker.check_clause IA_Checker.check_clause
    Integer_Arithmetic.showsl_IA_exp Integer_Arithmetic.showsl_IA_exp
    IA_Checker.lit_normalize IA_Checker.lit_normalize Integer_Arithmetic.IntT
    (\ s t -> Formula.Atom (Term.Fun Integer_Arithmetic.LeF [s, t]))
    (\ s t -> Formula.Atom (Term.Fun Integer_Arithmetic.LessF [s, t]))
    is_constant Integer_Arithmetic.def_checker;

}
