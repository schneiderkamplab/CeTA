{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module RPO_More(create_RPO_rel_impl) where {

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
import qualified RPO_Unbounded;
import qualified Check_Monad;
import qualified Term_Order;
import qualified HOL;
import qualified Complexity;
import qualified Sum_Type;
import qualified Term_Rewriting;
import qualified WPO;
import qualified Arith;
import qualified Shows_Literal;

showsl_rpo_repr ::
  forall a.
    (Shows_Literal.Showl a) => [((a, Arith.Nat), (Arith.Nat, WPO.Order_tag))] ->
                                 String -> String;
showsl_rpo_repr prs =
  (((Shows_Literal.showsl_literal "RPO with the following precedence\n" .
      Arith.foldr
        (\ (a, b) ->
          (case a of {
            (f, n) ->
              (\ (pr, _) ->
                (((((Shows_Literal.showsl_literal "precedence(" .
                      Shows_Literal.showsl f) .
                     Shows_Literal.showsl_literal "[") .
                    Shows_Literal.showsl_nat n) .
                   Shows_Literal.showsl_literal "]) = ") .
                  Shows_Literal.showsl_nat pr) .
                  Shows_Literal.showsl_literal "\n");
          })
            b)
        prs) .
     Shows_Literal.showsl_literal
       "\nprecedence(_) = 0\nand the following status\n") .
    Arith.foldr
      (\ (a, b) ->
        (case a of {
          (f, n) ->
            (\ (_, s) ->
              (((((Shows_Literal.showsl_literal "status(" .
                    Shows_Literal.showsl f) .
                   Shows_Literal.showsl_literal "[") .
                  Shows_Literal.showsl_nat n) .
                 Shows_Literal.showsl_literal "]) = ") .
                Shows_Literal.showsl_literal (case s of {
       WPO.Lex -> "lex";
       WPO.Mul -> "mul";
     })) .
                Shows_Literal.showsl_literal "\n");
        })
          b)
      prs) .
    Shows_Literal.showsl_literal "\nstatus(_) = lex\n";

rpo_nstrict_unbounded ::
  forall a b.
    (Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => ((a, Arith.Nat) ->
                                   (a, Arith.Nat) -> (Bool, Bool),
                                  (a, Arith.Nat) -> Bool) ->
                                  ((a, Arith.Nat) -> WPO.Order_tag) ->
                                    (Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b) ->
                                      Sum_Type.Sum (String -> String) ();
rpo_nstrict_unbounded pr c =
  (\ (s, t) ->
    Check_Monad.check (snd (RPO_Unbounded.rpo_unbounded pr c s t))
      ((((Shows_Literal.showsl_literal "could not orient " .
           Term_Rewriting.showsl_terma s) .
          Shows_Literal.showsl_literal " >=RPO ") .
         Term_Rewriting.showsl_terma t) .
        Shows_Literal.showsl_literal "\n"));

rpo_strict_unbounded ::
  forall a b.
    (Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => ((a, Arith.Nat) ->
                                   (a, Arith.Nat) -> (Bool, Bool),
                                  (a, Arith.Nat) -> Bool) ->
                                  ((a, Arith.Nat) -> WPO.Order_tag) ->
                                    (Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b) ->
                                      Sum_Type.Sum (String -> String) ();
rpo_strict_unbounded pr c =
  (\ (s, t) ->
    Check_Monad.check (fst (RPO_Unbounded.rpo_unbounded pr c s t))
      ((((Shows_Literal.showsl_literal "could not orient " .
           Term_Rewriting.showsl_terma s) .
          Shows_Literal.showsl_literal " >RPO ") .
         Term_Rewriting.showsl_terma t) .
        Shows_Literal.showsl_literal "\n"));

create_RPO_rel_impl ::
  forall a b c.
    (Shows_Literal.Showl a, Shows_Literal.Showl b, Eq c,
      Shows_Literal.Showl c) => ([((a, Arith.Nat),
                                    (Arith.Nat, WPO.Order_tag))] ->
                                  ((b, Arith.Nat) -> Arith.Nat,
                                    (b, Arith.Nat) -> WPO.Order_tag)) ->
                                  [((a, Arith.Nat),
                                     (Arith.Nat, WPO.Order_tag))] ->
                                    Term_Rewriting.Rel_impl_ext b c ();
create_RPO_rel_impl prec_repr_to_pr pr =
  (case prec_repr_to_pr pr of {
    (p, tau) ->
      let {
        ns = rpo_nstrict_unbounded
               (Term_Rewriting.prc_nat p, Term_Rewriting.prl_nat p) tau;
      } in Term_Rewriting.Rel_impl_ext (Sum_Type.Inr ()) (Sum_Type.Inr ())
             (showsl_rpo_repr pr)
             (rpo_strict_unbounded
               (Term_Rewriting.prc_nat p, Term_Rewriting.prl_nat p) tau)
             ns ns Term_Order.full_af Term_Order.full_af (Sum_Type.Inr ())
             (Sum_Type.Inr ()) (Sum_Type.Inr ()) (Sum_Type.Inr ())
             (Sum_Type.Inr ()) (Sum_Type.Inr ()) Term_Order.full_af
             (\ _ -> Sum_Type.Inr ()) (Just []) (Just [])
             Term_Rewriting.no_complexity_check ();
  });

}
