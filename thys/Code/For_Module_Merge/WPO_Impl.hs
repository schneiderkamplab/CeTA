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
import qualified Show_Instances;
import qualified Term_More;
import qualified Autoref_Bindings_HOL;
import qualified Product_Type;
import qualified Map_Choice;
import qualified Status_Impl;
import qualified Term_Order;
import qualified WPO_Approx;
import qualified Option;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Term_Order_Impl;
import qualified Complexity;
import qualified WPO;
import qualified Sum_Type;
import qualified Term;
import qualified Compare;
import qualified Compare_Order_Instances;
import qualified Str;
import qualified Compare_Instances;
import qualified Collection_Enum;
import qualified Shows_Literal;
import qualified Utility;
import qualified HOL;
import qualified List;
import qualified Status;
import qualified Set;
import qualified Arith;
import qualified Collection_Order;
import qualified Set_Impl;
import qualified Collection_Eq;

af_wpo ::
  forall a.
    ((a, Arith.Nat) -> Set.Set Arith.Nat) ->
      Status.Status a -> (a, Arith.Nat) -> Set.Set Arith.Nat;
af_wpo pi sigma f = Set.sup_set (List.set (Status.status sigma f)) (pi f);

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
    (Shows_Literal.Showl a) => Status.Status a ->
                                 ((Term.Term a [Str.Char],
                                    Term.Term a [Str.Char]) ->
                                   Sum_Type.Sum (String -> String) ()) ->
                                   Maybe [(a, Arith.Nat)] ->
                                     Sum_Type.Sum (String -> String) ();
check_status_ws_info sigma cns Nothing =
  Sum_Type.Inl
    (Shows_Literal.showsl_lit
      "missing weak-subterm status of base reduction pair");
check_status_ws_info sigma cns (Just fs) =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ (f, n) ->
        Error_Monad.catch_error
          (Error_Monad.forallM
            (\ i ->
              let {
                s = Term.Fun f
                      (map (\ ia ->
                             Term.Var
                               ([Str.char_0x78] ++
                                 Show_Instances.shows_prec_nat Arith.zero_nat ia
                                   []))
                        (List.upt Arith.zero_nat n));
                t = Term.Var
                      ([Str.char_0x78] ++
                        Show_Instances.shows_prec_nat Arith.zero_nat i []);
              } in Error_Monad.catch_error (cns (s, t))
                     (\ _ ->
                       Sum_Type.Inl
                         (((((((((Shows_Literal.showsl_lit "argument #" .
                                   Shows_Literal.showsl_nat (Arith.suc i)) .
                                  Shows_Literal.showsl_lit
                                    " is in status of ") .
                                 Term_Order_Impl.showsl_funa (f, n)) .
                                Shows_Literal.showsl_literal "\n") .
                               Shows_Literal.showsl_lit "but ") .
                              Term_More.showsl_terma s) .
                             Shows_Literal.showsl_lit " >= ") .
                            Shows_Literal.showsl_lit "x" .
                              Shows_Literal.showsl_nat i) .
                           Shows_Literal.showsl_lit " is not satisfied")))
            (Status.status sigma (f, n)))
          (\ x -> Sum_Type.Inl (snd x)))
      fs)
    (\ x -> Sum_Type.Inl (snd x));

showsl_wpo_params ::
  forall a.
    (Shows_Literal.Showl a) => [((a, Arith.Nat),
                                  (Arith.Nat, ([Arith.Nat], WPO.Order_tag)))] ->
                                 String -> String;
showsl_wpo_params params =
  Shows_Literal.showsl_lit "status and precedence:\n" .
    Shows_Literal.showsl_sep
      (\ (f, (p, (s, lm))) ->
        (((((((((((((Shows_Literal.showsl_lit "precedence(" .
                      Term_Order_Impl.showsl_funa f) .
                     Shows_Literal.showsl_lit ") = ") .
                    Shows_Literal.showsl_nat p) .
                   Shows_Literal.showsl_literal "\n") .
                  Shows_Literal.showsl_lit "  status(") .
                 Term_Order_Impl.showsl_funa f) .
                Shows_Literal.showsl_lit ") = ") .
               Shows_Literal.showsl_list_nat s) .
              Shows_Literal.showsl_literal "\n") .
             Shows_Literal.showsl_lit "  arg-status(") .
            Term_Order_Impl.showsl_funa f) .
           Shows_Literal.showsl_lit ") = ") .
          Shows_Literal.showsl_literal (case lm of {
 WPO.Lex -> "lex";
 WPO.Mul -> "mul";
                                       })) .
          Shows_Literal.showsl_literal "\n")
      (Shows_Literal.showsl_literal "\n") params;

wpo_rel_impl ::
  forall a.
    (Compare.Compare_order a, Eq a,
      Shows_Literal.Showl a) => Term_Order_Impl.Rel_impl_ext a [Str.Char] () ->
                                  [((a, Arith.Nat),
                                     (Arith.Nat,
                                       ([Arith.Nat], WPO.Order_tag)))] ->
                                    Term_Order_Impl.Rel_impl_ext a [Str.Char]
                                      ();
wpo_rel_impl rt params =
  let {
    stat = map (\ (f, ps) -> (f, fst (snd ps))) params;
    mparams = Map_Choice.ceta_map_of params;
    pr = Map_Choice.fun_of_map_funa mparams (\ _ -> Arith.zero_nat) fst;
    ot = Map_Choice.fun_of_map_funa mparams (\ _ -> WPO.Lex) (snd . snd);
    desc1 = Shows_Literal.showsl_lit "WPO ";
    desc2 =
      ((Shows_Literal.showsl_lit "with " . showsl_wpo_params params) .
        Shows_Literal.showsl_lit "\nover the following reduction pair:\n") .
        Term_Order_Impl.desc rt;
  } in (case Status_Impl.status_of stat of {
         Nothing ->
           Term_Order_Impl.faulty_rel_impl HOL.Type HOL.Type
             (Shows_Literal.showsl_lit "problem with indices in status of WPO!")
             (desc1 . desc2);
         Just sigma ->
           let {
             large_opt = large_of pr sigma (map fst params);
             ssimple =
               not (Autoref_Bindings_HOL.is_None large_opt) &&
                 Error_Monad.isOK
                   (check_status_ws_info sigma (Term_Order_Impl.s rt)
                     (Term_Order_Impl.not_sst rt));
             large =
               (if ssimple
                 then (\ f -> Arith.equal_nat (pr f) (Option.the large_opt))
                 else (\ _ -> False));
             s = (\ s t -> Error_Monad.isOK (Term_Order_Impl.s rt (s, t)));
             ns = (\ sa t -> Error_Monad.isOK (Term_Order_Impl.ns rt (sa, t)));
             wpo = WPO_Approx.wpo_ub (Term_Order_Impl.prc_nat pr)
                     (Term_Order_Impl.prl_nat pr) ssimple large s ns sigma ot;
             wpo_s =
               (\ (sa, t) ->
                 Check_Monad.check (fst (wpo sa t))
                   (((Term_More.showsl_terma sa .
                       Shows_Literal.showsl_lit " >wpo ") .
                      Term_More.showsl_terma t) .
                     Shows_Literal.showsl_lit " could not be ensured"));
             wpo_ns =
               (\ (sa, t) ->
                 Check_Monad.check (snd (wpo sa t))
                   (((Term_More.showsl_terma sa .
                       Shows_Literal.showsl_lit " >=wpo ") .
                      Term_More.showsl_terma t) .
                     Shows_Literal.showsl_lit " could not be ensured"));
           } in Term_Order_Impl.Rel_impl_ext
                  (Error_Monad.bind (Term_Order_Impl.valid rt)
                    (\ _ ->
                      Error_Monad.bind (Term_Order_Impl.standard rt)
                        (\ _ ->
                          Error_Monad.bind
                            (Error_Monad.catch_error
                              (Term_Order_Impl.subst_s rt)
                              (\ x ->
                                Sum_Type.Inl
                                  (Shows_Literal.showsl_lit
                                     "WPO requires stability of strict base relation\n" .
                                    x)))
                            (\ _ ->
                              check_status_ws_info sigma (Term_Order_Impl.ns rt)
                                (Term_Order_Impl.not_wst rt)))))
                  (Sum_Type.Inr ())
                  (if ssimple
                    then (desc1 .
                           Shows_Literal.showsl_lit "(strictly simple) ") .
                           desc2
                    else desc1 . desc2)
                  wpo_s wpo_ns wpo_ns (af_wpo (Term_Order_Impl.af rt) sigma)
                  (af_wpo (Term_Order_Impl.af rt) sigma) (Term_Order_Impl.sn rt)
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
                                  (Collection_Eq.set_eq (List.set idx)
                                    (List.set (List.upt Arith.zero_nat n)))
                                  (((Shows_Literal.showsl_lit
                                       "for monotonicity, status must be complete, but status of " .
                                      Term_Order_Impl.showsl_funa (f, n)) .
                                     Shows_Literal.showsl_lit " is ") .
                                    Shows_Literal.showsl_lista
                                      (map Arith.suc idx)));
                          })
                            b)
                        stat)
                      (\ x -> Sum_Type.Inl (snd x)))
                  (Just (map fst stat)) (Just (map fst stat))
                  Term_Order_Impl.no_complexity_check ();
       });

}
