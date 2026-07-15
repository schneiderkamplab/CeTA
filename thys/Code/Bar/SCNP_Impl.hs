{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module SCNP_Impl(scnp_arity, generate_scnp_rp) where {

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
import qualified Option_Util;
import qualified Map_Choice;
import qualified Term_Order;
import qualified HOL;
import qualified Complexity;
import qualified Compare;
import qualified Compare_Order_Instances;
import qualified Check_Monad;
import qualified SCNP;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Term_Rewriting;
import qualified Utility;
import qualified Arith;
import qualified Shows_Literal;

scnp_desc ::
  forall a.
    (Shows_Literal.Showl a) => [((a, Arith.Nat), [(Arith.Nat, Arith.Nat)])] ->
                                 (String -> String) -> String -> String;
scnp_desc af mu =
  (((Shows_Literal.showsl_lit "SCNP-version with mu = " . mu) .
     Shows_Literal.showsl_lit " and the level mapping defined by\n") .
    Shows_Literal.showsl_sep
      (\ (a, b) ->
        (case a of {
          (f, n) ->
            (\ asa ->
              ((Shows_Literal.showsl_lit "pi(" . Shows_Literal.showsl f) .
                Shows_Literal.showsl_lit ") = ") .
                Shows_Literal.default_showsl_list
                  (\ (p, l) ->
                    (((Shows_Literal.showsl_lit "(" .
                        (if Arith.less_nat p n
                          then Shows_Literal.showsl_nat (Arith.suc p)
                          else Shows_Literal.showsl_lit "epsilon")) .
                       Shows_Literal.showsl_lit ",") .
                      Shows_Literal.showsl_nat l) .
                      Shows_Literal.showsl_lit ")")
                  asa);
        })
          b)
      (Shows_Literal.showsl_literal "\n") af) .
    Shows_Literal.showsl_literal "\n";

scnp_arity ::
  forall a. [((a, Arith.Nat), [(Arith.Nat, Arith.Nat)])] -> Arith.Nat;
scnp_arity af = Utility.max_list (map (\ (_, a) -> Arith.size_list a) af);

label_s_ns_impl ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => ((Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b) ->
                                  Sum_Type.Sum (String -> String) ()) ->
                                  ((Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b) ->
                                    Sum_Type.Sum (String -> String) ()) ->
                                    (Term_Rewriting.Term a b, Arith.Nat) ->
                                      (Term_Rewriting.Term a b, Arith.Nat) ->
(Bool, Bool);
label_s_ns_impl cS cNS s t =
  (case s of {
    (sa, i) ->
      (case t of {
        (ta, j) ->
          (if Error_Monad.isOK (cS (sa, ta)) then (True, True)
            else (if Error_Monad.isOK (cNS (sa, ta))
                   then (Arith.less_nat j i, Arith.less_eq_nat j i)
                   else (False, False)));
      });
  });

s_label_mul_impl ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => (((Term_Rewriting.Term a b, Arith.Nat) ->
                                   (Term_Rewriting.Term a b, Arith.Nat) ->
                                     (Bool, Bool)) ->
                                  [(Term_Rewriting.Term a b, Arith.Nat)] ->
                                    [(Term_Rewriting.Term a b, Arith.Nat)] ->
                                      (Bool, Bool)) ->
                                  ((a, Arith.Nat) ->
                                    [(Arith.Nat, Arith.Nat)]) ->
                                    ((Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b) ->
                                      Sum_Type.Sum (String -> String) ()) ->
                                      ((Term_Rewriting.Term a b,
 Term_Rewriting.Term a b) ->
Sum_Type.Sum (String -> String) ()) ->
(Term_Rewriting.Term a b, Term_Rewriting.Term a b) ->
  Sum_Type.Sum (String -> String) ();
s_label_mul_impl list_ext af cS cNS st =
  (case st of {
    (Term_Rewriting.Var _, _) ->
      Sum_Type.Inl
        ((Shows_Literal.showsl_lit "roots of " .
           Term_Rewriting.showsl_rule st) .
          Shows_Literal.showsl_lit " must be non-variable");
    (Term_Rewriting.Fun _ _, Term_Rewriting.Var _) ->
      Sum_Type.Inl
        ((Shows_Literal.showsl_lit "roots of " .
           Term_Rewriting.showsl_rule st) .
          Shows_Literal.showsl_lit " must be non-variable");
    (Term_Rewriting.Fun f ss, Term_Rewriting.Fun g ts) ->
      Check_Monad.check
        (fst (list_ext (label_s_ns_impl cS cNS)
                (SCNP.lterms af (Term_Rewriting.Fun f ss))
               (SCNP.lterms af (Term_Rewriting.Fun g ts))))
        ((((((Shows_Literal.showsl_lit "cannot orient pair " .
               Term_Rewriting.showsl_rule st) .
              Shows_Literal.showsl_lit " strictly:\n") .
             Shows_Literal.showsl_list_prod
               (SCNP.lterms af (Term_Rewriting.Fun f ss))) .
            Shows_Literal.showsl_lit " >mu ") .
           Shows_Literal.showsl_list_prod
             (SCNP.lterms af (Term_Rewriting.Fun g ts))) .
          Shows_Literal.showsl_lit " could not be ensured");
  });

nST_label_mul_impl ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => (((Term_Rewriting.Term a b, Arith.Nat) ->
                                   (Term_Rewriting.Term a b, Arith.Nat) ->
                                     (Bool, Bool)) ->
                                  [(Term_Rewriting.Term a b, Arith.Nat)] ->
                                    [(Term_Rewriting.Term a b, Arith.Nat)] ->
                                      (Bool, Bool)) ->
                                  ((a, Arith.Nat) ->
                                    [(Arith.Nat, Arith.Nat)]) ->
                                    ((Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b) ->
                                      Sum_Type.Sum (String -> String) ()) ->
                                      ((Term_Rewriting.Term a b,
 Term_Rewriting.Term a b) ->
Sum_Type.Sum (String -> String) ()) ->
(Term_Rewriting.Term a b, Term_Rewriting.Term a b) ->
  Sum_Type.Sum (String -> String) ();
nST_label_mul_impl list_ext af cS cNS st =
  (case st of {
    (Term_Rewriting.Var _, _) ->
      Sum_Type.Inl
        ((Shows_Literal.showsl_literal "roots of " .
           Term_Rewriting.showsl_rule st) .
          Shows_Literal.showsl_literal " must be non-variable");
    (Term_Rewriting.Fun _ _, Term_Rewriting.Var _) ->
      Sum_Type.Inl
        ((Shows_Literal.showsl_literal "roots of " .
           Term_Rewriting.showsl_rule st) .
          Shows_Literal.showsl_literal " must be non-variable");
    (Term_Rewriting.Fun f ss, Term_Rewriting.Fun g ts) ->
      Check_Monad.check
        (snd (list_ext (label_s_ns_impl cS cNS)
                (SCNP.lterms af (Term_Rewriting.Fun f ss))
               (SCNP.lterms af (Term_Rewriting.Fun g ts))))
        ((((((Shows_Literal.showsl_literal "cannot orient pair " .
               Term_Rewriting.showsl_rule st) .
              Shows_Literal.showsl_literal " weakly:\n") .
             Shows_Literal.showsl_list_prod
               (SCNP.lterms af (Term_Rewriting.Fun f ss))) .
            Shows_Literal.showsl_literal " >=mu ") .
           Shows_Literal.showsl_list_prod
             (SCNP.lterms af (Term_Rewriting.Fun g ts))) .
          Shows_Literal.showsl_literal " could not be ensured");
  });

generate_scnp_rp ::
  forall a b.
    (Compare.Compare_order a, Shows_Literal.Showl a,
      Shows_Literal.Showl b) => (((Term_Rewriting.Term a b, Arith.Nat) ->
                                   (Term_Rewriting.Term a b, Arith.Nat) ->
                                     (Bool, Bool)) ->
                                  [(Term_Rewriting.Term a b, Arith.Nat)] ->
                                    [(Term_Rewriting.Term a b, Arith.Nat)] ->
                                      (Bool, Bool)) ->
                                  (String -> String) ->
                                    [((a, Arith.Nat),
                                       [(Arith.Nat, Arith.Nat)])] ->
                                      Term_Rewriting.Rel_impl_ext a b () ->
Term_Rewriting.Rel_impl_ext a b ();
generate_scnp_rp list_ext list_ext_name af rt =
  let {
    afa = Option_Util.fun_of_map (Map_Choice.ceta_map_of af) [];
    pi = Term_Rewriting.af rt;
    cS = Term_Rewriting.s rt;
    cNS = Term_Rewriting.ns rt;
  } in Term_Rewriting.Rel_impl_ext (Term_Rewriting.rel_impl_redpair rt)
         (Sum_Type.Inl
           (Shows_Literal.showsl_lit
             "SCNP does not satisfy standard requirements such as S subset NS"))
         (scnp_desc af list_ext_name . Term_Rewriting.desc rt)
         (s_label_mul_impl list_ext afa cS cNS) (Term_Rewriting.ns rt)
         (nST_label_mul_impl list_ext afa cS cNS) pi (SCNP.scnp_af_to_af afa pi)
         (Sum_Type.Inr ()) (Sum_Type.Inr ()) (Term_Rewriting.ce_compat rt)
         (Sum_Type.Inl
           (Shows_Literal.showsl_lit "SCNP cannot be used as co-rewrite pair"))
         (Sum_Type.Inr ())
         (Sum_Type.Inl
           (Shows_Literal.showsl_lit
             "SCNP does not ensure top-non-strict refl."))
         Term_Order.empty_af
         (\ _ ->
           Sum_Type.Inl
             (Shows_Literal.showsl_lit
               "SCNP does not support strictly monotone orders"))
         Nothing Nothing Term_Rewriting.no_complexity_check ();

}
