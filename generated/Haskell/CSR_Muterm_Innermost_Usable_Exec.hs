{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  CSR_Muterm_Innermost_Usable_Exec(muterm_innermost_typed_shape_check,
                                    muterm_expanded_innermost_usable_check)
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
import qualified CSR_Checker_Base;
import qualified CSR_Muterm_Usable_Rules;
import qualified Term_Rewriting;
import qualified Labelings;
import qualified Arith;

muterm_marked_target_check ::
  forall a b c.
    (Eq a,
      Eq b) => [((Labelings.Lab a b, Arith.Nat), [Arith.Nat])] ->
                 Term_Rewriting.Term (Labelings.Lab a b) c -> Bool;
muterm_marked_target_check mu (Term_Rewriting.Fun (Labelings.Sharp f) ts) =
  CSR_Muterm_Usable_Rules.muterm_mu_positions_list mu
    (Labelings.Sharp f, Arith.size_list ts) ==
    CSR_Muterm_Usable_Rules.muterm_mu_positions_list mu (f, Arith.size_list ts);
muterm_marked_target_check mu (Term_Rewriting.Var v) = False;
muterm_marked_target_check mu (Term_Rewriting.Fun (Labelings.Lab vb vc) va) =
  False;
muterm_marked_target_check mu (Term_Rewriting.Fun (Labelings.FunLab vb vc) va) =
  False;
muterm_marked_target_check mu (Term_Rewriting.Fun (Labelings.UnLab vb) va) =
  False;

muterm_innermost_typed_shape_check ::
  forall a b c d e f g.
    (Eq a,
      Eq b) => [((Labelings.Lab a b, Arith.Nat), [Arith.Nat])] ->
                 [(Term_Rewriting.Term (Labelings.Lab a b) c,
                    Term_Rewriting.Term (Labelings.Lab a b) d)] ->
                   [(Term_Rewriting.Term e f,
                      Term_Rewriting.Term (Labelings.Lab a b) g)] ->
                     Bool;
muterm_innermost_typed_shape_check mu p s =
  all (\ (l, r) ->
        muterm_marked_target_check mu l &&
          (Term_Rewriting.is_Var r || muterm_marked_target_check mu r))
    p &&
    all (\ (l, r) ->
          not (Term_Rewriting.is_Var l) && muterm_marked_target_check mu r)
      s;

muterm_expanded_innermost_usable_check ::
  forall a b c.
    (Eq a, Eq b,
      Eq c) => [(Term_Rewriting.Term (Labelings.Lab a b) c,
                  Term_Rewriting.Term (Labelings.Lab a b) c)] ->
                 [(Term_Rewriting.Term (Labelings.Lab a b) c,
                    Term_Rewriting.Term (Labelings.Lab a b) c)] ->
                   [((Labelings.Lab a b, Arith.Nat), [Arith.Nat])] ->
                     [(Term_Rewriting.Term (Labelings.Lab a b) c,
                        Term_Rewriting.Term (Labelings.Lab a b) c)] ->
                       [(Term_Rewriting.Term (Labelings.Lab a b) c,
                          Term_Rewriting.Term (Labelings.Lab a b) c)] ->
                         Bool;
muterm_expanded_innermost_usable_check r u mu p s =
  CSR_Muterm_Usable_Rules.muterm_innermost_ur_closed_check r u mu (p ++ s) &&
    CSR_Checker_Base.rhs_mu_vars_condition_list mu (p ++ s ++ u) &&
      muterm_innermost_typed_shape_check mu p s;

}
