{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Cut_Transition_Split(Cut_transition_split_info(..), cut_transition_split)
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
import qualified Product_Type;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified List;
import qualified HOL;
import qualified Cooperation_Program;
import qualified Formula;
import qualified Sum_Type;
import qualified LTS;
import qualified Term;
import qualified Set;
import qualified Collection_Order;
import qualified Shows_Literal;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Container_Setup;

newtype Cut_transition_split_info a = Cut_Transition_Split_Info [[a]];

cut_transition_split ::
  forall a b c d e.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Eq a,
      Set_Impl.Set_impl a, Shows_Literal.Showl a, Collection_Order.Ccompare e,
      Eq e,
      Shows_Literal.Showl e) => Cut_transition_split_info a ->
                                  LTS.Lts_impl b c d
                                    (Cooperation_Program.Sharp e) a ->
                                    Sum_Type.Sum (String -> String)
                                      [LTS.Lts_impl b c d
 (Cooperation_Program.Sharp e) a];
cut_transition_split (Cut_Transition_Split_Info ct_ids) cp =
  Error_Monad.catch_error
    (case List.partition
            ((\ tau -> Cooperation_Program.is_sharp (LTS.source tau)) . snd)
            (LTS.transitions_impl cp)
      of {
      (p, r) ->
        (case List.partition ((Cooperation_Program.is_sharp . LTS.target) . snd)
                r
          of {
          (ct, rr) ->
            let {
              slist = map (LTS.source . snd) p;
              s = List.set slist;
              cT_ids = List.set (concat ct_ids);
            } in Error_Monad.bind
                   (Error_Monad.catch_error
                     (Error_Monad.forallM
                       (\ l ->
                         Check_Monad.check
                           (not (Cooperation_Program.is_sharp l))
                           ((Shows_Literal.showsl_lit "initial state " .
                              Cooperation_Program.showsl_sharp l) .
                             Shows_Literal.showsl_lit " must not be sharped"))
                       (LTS.initiala cp))
                     (\ x -> Sum_Type.Inl (snd x)))
                   (\ _ ->
                     Error_Monad.bind
                       (Error_Monad.catch_error
                         (Error_Monad.forallM
                           (\ (t_id, cta) ->
                             Check_Monad.check
                               (if Set.member (LTS.target cta) s
                                 then Set.member t_id cT_ids else True)
                               (((Shows_Literal.showsl_lit
                                    "did not find cut-transition " .
                                   Shows_Literal.showsl t_id) .
                                  Shows_Literal.showsl_lit
                                    " in partition\nrelevant cut-points are: ") .
                                 Cooperation_Program.showsl_list_sharp slist))
                           ct)
                         (\ x -> Sum_Type.Inl (snd x)))
                       (\ _ ->
                         let {
                           rrp = rr ++ p;
                         } in Sum_Type.Inr
                                (map (\ ct_idsa ->
                                       LTS.Lts_Impl (LTS.initiala cp)
 (filter (\ cta -> List.member ct_idsa (fst cta)) ct ++ rrp)
 (LTS.assertion_impl cp))
                                  ct_ids)));
        });
    })
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "error in splitting cut transitions on LTS\n" .
          x));

}
