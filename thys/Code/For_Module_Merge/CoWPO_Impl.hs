{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module CoWPO_Impl(cowpo_rel_impl) where {

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
import qualified Term_More;
import qualified Product_Type;
import qualified WPO_Impl;
import qualified Option;
import qualified Map_Choice;
import qualified Status_Impl;
import qualified Term_Order;
import qualified WPO_Approx;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Term_Order_Impl;
import qualified Complexity;
import qualified WPO;
import qualified Status;
import qualified Sum_Type;
import qualified Term;
import qualified Set;
import qualified Arith;
import qualified HOL;
import qualified Compare;
import qualified Compare_Order_Instances;
import qualified Str;
import qualified Shows_Literal;
import qualified Compare_Instances;

cowpo_rel_impl ::
  forall a.
    (Compare.Compare_order a, Eq a,
      Shows_Literal.Showl a) => Term_Order_Impl.Rel_impl_ext a [Str.Char] () ->
                                  [((a, Arith.Nat),
                                     (Arith.Nat,
                                       ([Arith.Nat], WPO.Order_tag)))] ->
                                    Term_Order_Impl.Rel_impl_ext a [Str.Char]
                                      ();
cowpo_rel_impl rt params =
  let {
    stat = map (\ (f, ps) -> (f, fst (snd ps))) params;
    mparams = Map_Choice.ceta_map_of params;
    pr = Map_Choice.fun_of_map_funa mparams (\ _ -> Arith.zero_nat) fst;
    ot = (\ _ -> WPO.Lex);
    desc1 = Shows_Literal.showsl_lit "Co-WPO ";
    desc2 =
      ((Shows_Literal.showsl_lit "with " . WPO_Impl.showsl_wpo_params params) .
        Shows_Literal.showsl_lit "\nover the following relation:\n") .
        Term_Order_Impl.desc rt;
  } in (case Status_Impl.status_of stat of {
         Nothing ->
           Term_Order_Impl.faulty_rel_impl HOL.Type HOL.Type
             (Shows_Literal.showsl_lit
               "problem with indices in status of co-WPO!")
             (desc1 . desc2);
         Just sigma ->
           let {
             large = (\ _ -> False);
             ssimple = False;
             s = (\ s t -> Error_Monad.isOK (Term_Order_Impl.s rt (s, t)));
             ns = (\ sa t -> Error_Monad.isOK (Term_Order_Impl.ns rt (sa, t)));
             wpo = WPO_Approx.wpo_ub (Term_Order_Impl.prc_nat pr) (\ _ -> False)
                     ssimple large s ns sigma ot;
             invS = ns;
             invNS = s;
             cowpo =
               WPO_Approx.wpo_ub
                 (\ f g ->
                   (not (snd (Term_Order_Impl.prc_nat pr g f)),
                     not (fst (Term_Order_Impl.prc_nat pr g f))))
                 (\ _ -> False) ssimple large invNS invS sigma ot;
             wpo_s =
               (\ (sa, t) ->
                 Check_Monad.check (fst (cowpo sa t))
                   (((Term_More.showsl_terma sa .
                       Shows_Literal.showsl_lit " >co-wpo ") .
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
                                     "Co-WPO requires stability of strict base relation\n" .
                                    x)))
                            (\ _ ->
                              WPO_Impl.check_status_ws_info sigma
                                (Term_Order_Impl.ns rt)
                                (Term_Order_Impl.not_wst rt)))))
                  (Sum_Type.Inl
                    (Shows_Literal.showsl_lit
                      "Co-WPO does not support standard properties"))
                  (desc1 . desc2) wpo_s wpo_ns
                  (\ _ ->
                    Sum_Type.Inl
                      (Shows_Literal.showsl_lit
                        "Co-WPO does not support nst-comparisons"))
                  Term_Order.full_af Term_Order.full_af
                  (Sum_Type.Inl
                    (Shows_Literal.showsl_lit "Co-WPO does not support SN"))
                  (Sum_Type.Inr ())
                  (Sum_Type.Inl
                    (Shows_Literal.showsl_lit "Co-WPO does not support Ce"))
                  (Sum_Type.Inr ())
                  (Sum_Type.Inl
                    (Shows_Literal.showsl_lit
                      "Co-WPO does not support top-mono"))
                  (Sum_Type.Inl
                    (Shows_Literal.showsl_lit
                      "Co-WPO does not support top-refl"))
                  Term_Order.empty_af
                  (\ _ ->
                    Sum_Type.Inl
                      (Shows_Literal.showsl_lit
                        "Co-WPO does not support strong monotonicity"))
                  Nothing Nothing Term_Order_Impl.no_complexity_check ();
       });

}
