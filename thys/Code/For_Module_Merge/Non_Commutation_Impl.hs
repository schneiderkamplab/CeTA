{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Non_Commutation_Impl(check_non_commute) where {

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
import qualified Q_Restricted_Rewriting_Impl;
import qualified Term_Impl;
import qualified Trs_Impl;
import qualified Error_Monad;
import qualified Non_Confluence_Impl;
import qualified Sum_Type;
import qualified Term;
import qualified Set;
import qualified Collection_Enum;
import qualified Cardinality;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified HOL;
import qualified Compare;
import qualified Labelings_Impl;
import qualified Container_Setup;
import qualified Labelings;
import qualified Str;
import qualified Mapping_Impl;
import qualified Collection_Order;
import qualified Shows_Literal;
import qualified Compare_Instances;
import qualified Arith;

check_non_commute ::
  forall a b c.
    (Compare.Compare_order a, HOL.Default a, Eq a, Shows_Literal.Showl a,
      Cardinality.Card_UNIV b, Collection_Enum.Cenum b, Collection_Eq.Ceq b,
      Collection_Order.Cproper_interval b, Compare.Compare_order b, Eq b,
      Set_Impl.Set_impl b,
      Shows_Literal.Showl b) => Set.Set
                                  (Labelings.Lab a [Arith.Nat], Arith.Nat) ->
                                  [(Term.Term (Labelings.Lab a [Arith.Nat])
                                      [Str.Char],
                                     Term.Term (Labelings.Lab a [Arith.Nat])
                                       [Str.Char])] ->
                                    [(Term.Term (Labelings.Lab a [Arith.Nat])
[Str.Char],
                                       Term.Term (Labelings.Lab a [Arith.Nat])
 [Str.Char])] ->
                                      Term.Term (Labelings.Lab a [Arith.Nat])
[Str.Char] ->
[([Arith.Nat],
   ((Term.Term (Labelings.Lab a [Arith.Nat]) [Str.Char],
      Term.Term (Labelings.Lab a [Arith.Nat]) [Str.Char]),
     Term.Term (Labelings.Lab a [Arith.Nat]) [Str.Char]))] ->
  [([Arith.Nat],
     ((Term.Term (Labelings.Lab a [Arith.Nat]) [Str.Char],
        Term.Term (Labelings.Lab a [Arith.Nat]) [Str.Char]),
       Term.Term (Labelings.Lab a [Arith.Nat]) [Str.Char]))] ->
    Non_Confluence_Impl.Non_join_info (Labelings.Lab a [Arith.Nat]) [Str.Char] b
      c ->
      Sum_Type.Sum (String -> String) ();
check_non_commute f r sa s seq1 seq2 reason =
  Error_Monad.bind (Term_Impl.check_funas_term f s)
    (\ _ ->
      let {
        chk = (\ name ra seq ->
                Error_Monad.catch_error
                  (Q_Restricted_Rewriting_Impl.check_rsteps_last ra s seq)
                  (\ x ->
                    Sum_Type.Inl
                      (((((Shows_Literal.showsl_lit
                             "problem when checking rewrite steps with TRS " .
                            Shows_Literal.showsl_lit name) .
                           Shows_Literal.showsl_literal "\n") .
                          Trs_Impl.showsl_trs ra) .
                         Shows_Literal.showsl_literal "\n") .
                        x)));
      } in Error_Monad.bind (chk "S" sa seq1)
             (\ _ ->
               Error_Monad.bind (chk "R" r seq2)
                 (\ _ ->
                   Non_Confluence_Impl.check_non_join r sa
                     (Q_Restricted_Rewriting_Impl.rseq_last s seq1)
                     (Q_Restricted_Rewriting_Impl.rseq_last s seq2) reason)));

}
