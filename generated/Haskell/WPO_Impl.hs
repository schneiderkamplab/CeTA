{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module WPO_Impl(check_status_ws_info, showsl_wpo_params, wpo_rel_impl) where {

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
import qualified Autoref_Bindings_HOL;
import qualified Map_Choice;
import qualified Status_Impl;
import qualified Term_Order;
import qualified WPO_Approx;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified WPO;
import qualified Sum_Type;
import qualified Compare;
import qualified Compare_Order_Instances;
import qualified Term_Rewriting;
import qualified Utility;
import qualified HOL;
import qualified Status;
import qualified Arith;

af_wpo ::
  forall a.
    ((a, Arith.Nat) -> Arith.Set Arith.Nat) ->
      Status.Status a -> (a, Arith.Nat) -> Arith.Set Arith.Nat;
af_wpo pi sigma f = Arith.sup_set (Arith.set (Status.status sigma f)) (pi f);

large_of ::
  forall a.
    ((a, Arith.Nat) -> Arith.Nat) ->
      Status.Status a -> [(a, Arith.Nat)] -> Maybe Arith.Nat;
large_of pr sigma fs =
  let {
    m = Utility.max_list (map pr fs);
    ls = filter (\ f -> Arith.equal_nat (pr f) m) fs;
  } in (if Arith.less_nat Arith.zero_nat m &&
             all (\ f -> null (Status.status sigma f)) ls
         then Just m else Nothing);

check_status_ws_info ::
  forall a.
    (Term_Rewriting.Showl a) => Status.Status a ->
                                  ((Term_Rewriting.Term a [Arith.Char],
                                     Term_Rewriting.Term a [Arith.Char]) ->
                                    Sum_Type.Sum (String -> String) ()) ->
                                    Maybe [(a, Arith.Nat)] ->
                                      Sum_Type.Sum (String -> String) ();
check_status_ws_info sigma cns Nothing =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit
      "missing weak-subterm status of base reduction pair");
check_status_ws_info sigma cns (Just fs) =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ (f, n) ->
        Error_Monad.catch_error
          (Error_Monad.forallM
            (\ i ->
              let {
                s = Term_Rewriting.Fun f
                      (map (\ ia ->
                             Term_Rewriting.Var
                               ([Arith.char_0x78] ++
                                 Term_Rewriting.shows_prec_nat Arith.zero_nat ia
                                   []))
                        (Arith.upt Arith.zero_nat n));
                t = Term_Rewriting.Var
                      ([Arith.char_0x78] ++
                        Term_Rewriting.shows_prec_nat Arith.zero_nat i []);
              } in Error_Monad.catch_error (cns (s, t))
                     (\ _ ->
                       Sum_Type.Inl
                         (((((((((Term_Rewriting.showsl_lit "argument #" .
                                   Term_Rewriting.showsl_nat (Arith.suc i)) .
                                  Term_Rewriting.showsl_lit
                                    " is in status of ") .
                                 Term_Rewriting.showsl_funa (f, n)) .
                                Term_Rewriting.showsl_literal "\n") .
                               Term_Rewriting.showsl_lit "but ") .
                              Term_Rewriting.showsl_terma s) .
                             Term_Rewriting.showsl_lit " >= ") .
                            Term_Rewriting.showsl_lit "x" .
                              Term_Rewriting.showsl_nat i) .
                           Term_Rewriting.showsl_lit " is not satisfied")))
            (Status.status sigma (f, n)))
          (\ x -> Sum_Type.Inl (snd x)))
      fs)
    (\ x -> Sum_Type.Inl (snd x));

showsl_wpo_params ::
  forall a.
    (Term_Rewriting.Showl a) => [((a, Arith.Nat),
                                   (Arith.Nat,
                                     ([Arith.Nat], WPO.Order_tag)))] ->
                                  String -> String;
showsl_wpo_params params =
  Term_Rewriting.showsl_lit "status and precedence:\n" .
    Term_Rewriting.showsl_sep
      (\ (f, (p, (s, lm))) ->
        (((((((((((((Term_Rewriting.showsl_lit "precedence(" .
                      Term_Rewriting.showsl_funa f) .
                     Term_Rewriting.showsl_lit ") = ") .
                    Term_Rewriting.showsl_nat p) .
                   Term_Rewriting.showsl_literal "\n") .
                  Term_Rewriting.showsl_lit "  status(") .
                 Term_Rewriting.showsl_funa f) .
                Term_Rewriting.showsl_lit ") = ") .
               Term_Rewriting.showsl_list_nat s) .
              Term_Rewriting.showsl_literal "\n") .
             Term_Rewriting.showsl_lit "  arg-status(") .
            Term_Rewriting.showsl_funa f) .
           Term_Rewriting.showsl_lit ") = ") .
          Term_Rewriting.showsl_literal (case lm of {
  WPO.Lex -> "lex";
  WPO.Mul -> "mul";
})) .
          Term_Rewriting.showsl_literal "\n")
      (Term_Rewriting.showsl_literal "\n") params;

wpo_rel_impl ::
  forall a.
    (Compare.Compare_order a, Eq a,
      Term_Rewriting.Showl a) => Term_Rewriting.Rel_impl_ext a [Arith.Char]
                                   () ->
                                   [((a, Arith.Nat),
                                      (Arith.Nat,
([Arith.Nat], WPO.Order_tag)))] ->
                                     Term_Rewriting.Rel_impl_ext a [Arith.Char]
                                       ();
wpo_rel_impl rt params =
  let {
    stat = map (\ (f, ps) -> (f, fst (snd ps))) params;
    mparams = Map_Choice.ceta_map_of params;
    pr = Map_Choice.fun_of_map_funa mparams (\ _ -> Arith.zero_nat) fst;
    ot = Map_Choice.fun_of_map_funa mparams (\ _ -> WPO.Lex) (snd . snd);
    desc1 = Term_Rewriting.showsl_lit "WPO ";
    desc2 =
      ((Term_Rewriting.showsl_lit "with " . showsl_wpo_params params) .
        Term_Rewriting.showsl_lit "\nover the following reduction pair:\n") .
        Term_Rewriting.desc rt;
  } in (case Status_Impl.status_of stat of {
         Nothing ->
           Term_Rewriting.faulty_rel_impl HOL.Type HOL.Type
             (Term_Rewriting.showsl_lit
               "problem with indices in status of WPO!")
             (desc1 . desc2);
         Just sigma ->
           let {
             large_opt = large_of pr sigma (map fst params);
             ssimple =
               not (Autoref_Bindings_HOL.is_None large_opt) &&
                 Error_Monad.isOK
                   (check_status_ws_info sigma (Term_Rewriting.s rt)
                     (Term_Rewriting.not_sst rt));
             large =
               (if ssimple
                 then (\ f -> Arith.equal_nat (pr f) (Arith.the large_opt))
                 else (\ _ -> False));
             s = (\ s t -> Error_Monad.isOK (Term_Rewriting.s rt (s, t)));
             ns = (\ sa t -> Error_Monad.isOK (Term_Rewriting.ns rt (sa, t)));
             wpo = WPO_Approx.wpo_ub (Term_Rewriting.prc_nat pr)
                     (Term_Rewriting.prl_nat pr) ssimple large s ns sigma ot;
             wpo_s =
               (\ (sa, t) ->
                 Check_Monad.check (fst (wpo sa t))
                   (((Term_Rewriting.showsl_terma sa .
                       Term_Rewriting.showsl_lit " >wpo ") .
                      Term_Rewriting.showsl_terma t) .
                     Term_Rewriting.showsl_lit " could not be ensured"));
             wpo_ns =
               (\ (sa, t) ->
                 Check_Monad.check (snd (wpo sa t))
                   (((Term_Rewriting.showsl_terma sa .
                       Term_Rewriting.showsl_lit " >=wpo ") .
                      Term_Rewriting.showsl_terma t) .
                     Term_Rewriting.showsl_lit " could not be ensured"));
           } in Term_Rewriting.Rel_impl_ext
                  (Error_Monad.bind (Term_Rewriting.valid rt)
                    (\ _ ->
                      Error_Monad.bind (Term_Rewriting.standard rt)
                        (\ _ ->
                          Error_Monad.bind
                            (Error_Monad.catch_error (Term_Rewriting.subst_s rt)
                              (\ x ->
                                Sum_Type.Inl
                                  (Term_Rewriting.showsl_lit
                                     "WPO requires stability of strict base relation\n" .
                                    x)))
                            (\ _ ->
                              check_status_ws_info sigma (Term_Rewriting.ns rt)
                                (Term_Rewriting.not_wst rt)))))
                  (Sum_Type.Inr ())
                  (if ssimple
                    then (desc1 .
                           Term_Rewriting.showsl_lit "(strictly simple) ") .
                           desc2
                    else desc1 . desc2)
                  wpo_s wpo_ns wpo_ns (af_wpo (Term_Rewriting.af rt) sigma)
                  (af_wpo (Term_Rewriting.af rt) sigma) (Term_Rewriting.sn rt)
                  (Sum_Type.Inr ()) (Sum_Type.Inr ()) (Sum_Type.Inr ())
                  (Sum_Type.Inr ()) (Sum_Type.Inr ()) Term_Order.empty_af
                  (\ _ ->
                    Error_Monad.catch_error
                      (Error_Monad.forallM
                        (\ (a, b) ->
                          (case a of {
                            (f, n) ->
                              (\ idx ->
                                Check_Monad.check
                                  (Arith.set_eq (Arith.set idx)
                                    (Arith.set (Arith.upt Arith.zero_nat n)))
                                  (((Term_Rewriting.showsl_lit
                                       "for monotonicity, status must be complete, but status of " .
                                      Term_Rewriting.showsl_funa (f, n)) .
                                     Term_Rewriting.showsl_lit " is ") .
                                    Term_Rewriting.showsl_lista
                                      (map Arith.suc idx)));
                          })
                            b)
                        stat)
                      (\ x -> Sum_Type.Inl (snd x)))
                  (Just (map fst stat)) (Just (map fst stat))
                  Term_Rewriting.no_complexity_check ();
       });

}
