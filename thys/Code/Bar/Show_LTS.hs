{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Show_LTS(showsl_cooperation_program, showsl_transition, showsl_lts)
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
import qualified Arith;
import qualified HOL;
import qualified Term_Rewriting;
import qualified Shows_Literal;

showsl_cooperation_program ::
  forall a b c d e.
    (Shows_Literal.Showl d,
      Shows_Literal.Showl e) => Term_Rewriting.Lts_impl a b c
                                  (Term_Rewriting.Sharp d) e ->
                                  String -> String;
showsl_cooperation_program (Term_Rewriting.Lts_Impl i tran lc) =
  let {
    trana =
      filter (\ (_, tt) -> Term_Rewriting.is_sharp (Term_Rewriting.target tt))
        tran;
    tranb =
      (case Arith.partition
              (\ (_, tt) -> Term_Rewriting.is_sharp (Term_Rewriting.source tt))
              trana
        of {
        (ss, fs) -> fs ++ ss;
      });
  } in Shows_Literal.showsl_lit "Cooperation program (only sharp-part)\n" .
         Shows_Literal.showsl_sep
           (\ (t, tt) ->
             (((Shows_Literal.showsl t . Shows_Literal.showsl_lit ": ") .
                Term_Rewriting.showsl_sharp (Term_Rewriting.source tt)) .
               Shows_Literal.showsl_lit " --> ") .
               Term_Rewriting.showsl_sharp (Term_Rewriting.target tt))
           (Shows_Literal.showsl_literal "\n") tranb .
    Shows_Literal.showsl_literal "\n";

showsl_transition ::
  forall a b c d.
    (Shows_Literal.Showl d) => (Term_Rewriting.Term a
                                  (Term_Rewriting.Trans_var b, c) ->
                                 String -> String) ->
                                 Term_Rewriting.Transition_rule a b c d ->
                                   String -> String;
showsl_transition showsl_tatom (Term_Rewriting.Transition s t phi) =
  (((Shows_Literal.showsl s . Shows_Literal.showsl_lit " ---> ") .
     Shows_Literal.showsl t) .
    Shows_Literal.showsl_lit ": ") .
    Term_Rewriting.showsl_formula showsl_tatom phi;

showsl_labeled_transition ::
  forall a b c d e.
    (Shows_Literal.Showl d,
      Shows_Literal.Showl e) => (Term_Rewriting.Term a
                                   (Term_Rewriting.Trans_var b, c) ->
                                  String -> String) ->
                                  (d, Term_Rewriting.Transition_rule a b c e) ->
                                    String -> String;
showsl_labeled_transition showsl_tatom (lab, tran) =
  (Shows_Literal.showsl lab . Shows_Literal.showsl_lit ": ") .
    showsl_transition showsl_tatom tran;

showsl_lts ::
  forall a b c d e.
    (Shows_Literal.Showl d,
      Shows_Literal.Showl e) => (Term_Rewriting.Term a (b, c) ->
                                  String -> String) ->
                                  (Term_Rewriting.Term a
                                     (Term_Rewriting.Trans_var b, c) ->
                                    String -> String) ->
                                    Term_Rewriting.Lts_impl a b c d e ->
                                      String -> String;
showsl_lts showsl_atom showsl_tatom (Term_Rewriting.Lts_Impl i tran lc) =
  (((((Shows_Literal.showsl_lit "LTS:\nInitial locations: " .
        Shows_Literal.showsl_list i) .
       Shows_Literal.showsl_lit "\nTransitions\n") .
      Shows_Literal.showsl_sep (showsl_labeled_transition showsl_tatom)
        (Shows_Literal.showsl_literal "\n") tran) .
     Shows_Literal.showsl_lit "\nLocation conditions") .
    Shows_Literal.showsl_sep
      (\ (l, f) ->
        (Shows_Literal.showsl l . Shows_Literal.showsl_lit ": ") .
          Term_Rewriting.showsl_formula showsl_atom f)
      (Shows_Literal.showsl_literal "\n") lc) .
    Shows_Literal.showsl_literal "\n";

}
