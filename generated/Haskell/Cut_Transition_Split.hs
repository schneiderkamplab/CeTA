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
import qualified Check_Monad;
import qualified Error_Monad;
import qualified HOL;
import qualified Sum_Type;
import qualified Arith;
import qualified Term_Rewriting;

newtype Cut_transition_split_info a = Cut_Transition_Split_Info [[a]];

cut_transition_split ::
  forall a b c d e.
    (Arith.Ceq a, Arith.Ccompare a, Eq a, Arith.Set_impl a,
      Term_Rewriting.Showl a, Arith.Ccompare e, Eq e,
      Term_Rewriting.Showl e) => Cut_transition_split_info a ->
                                   Term_Rewriting.Lts_impl b c d
                                     (Term_Rewriting.Sharp e) a ->
                                     Sum_Type.Sum (String -> String)
                                       [Term_Rewriting.Lts_impl b c d
  (Term_Rewriting.Sharp e) a];
cut_transition_split (Cut_Transition_Split_Info ct_ids) cp =
  Error_Monad.catch_error
    (case Arith.partition
            ((\ tau -> Term_Rewriting.is_sharp (Term_Rewriting.source tau)) .
              snd)
            (Term_Rewriting.transitions_impl cp)
      of {
      (p, r) ->
        (case Arith.partition
                ((Term_Rewriting.is_sharp . Term_Rewriting.target) . snd) r
          of {
          (ct, rr) ->
            let {
              slist = map (Term_Rewriting.source . snd) p;
              s = Arith.set slist;
              cT_ids = Arith.set (concat ct_ids);
            } in Error_Monad.bind
                   (Error_Monad.catch_error
                     (Error_Monad.forallM
                       (\ l ->
                         Check_Monad.check (not (Term_Rewriting.is_sharp l))
                           ((Term_Rewriting.showsl_lit "initial state " .
                              Term_Rewriting.showsl_sharp l) .
                             Term_Rewriting.showsl_lit " must not be sharped"))
                       (Term_Rewriting.initiala cp))
                     (\ x -> Sum_Type.Inl (snd x)))
                   (\ _ ->
                     Error_Monad.bind
                       (Error_Monad.catch_error
                         (Error_Monad.forallM
                           (\ (t_id, cta) ->
                             Check_Monad.check
                               (if Arith.member (Term_Rewriting.target cta) s
                                 then Arith.member t_id cT_ids else True)
                               (((Term_Rewriting.showsl_lit
                                    "did not find cut-transition " .
                                   Term_Rewriting.showsl t_id) .
                                  Term_Rewriting.showsl_lit
                                    " in partition\nrelevant cut-points are: ") .
                                 Term_Rewriting.showsl_list_sharp slist))
                           ct)
                         (\ x -> Sum_Type.Inl (snd x)))
                       (\ _ ->
                         let {
                           rrp = rr ++ p;
                         } in Sum_Type.Inr
                                (map (\ ct_idsa ->
                                       Term_Rewriting.Lts_Impl
 (Term_Rewriting.initiala cp)
 (filter (\ cta -> Arith.membera ct_idsa (fst cta)) ct ++ rrp)
 (Term_Rewriting.assertion_impl cp))
                                  ct_ids)));
        });
    })
    (\ x ->
      Sum_Type.Inl
        (Term_Rewriting.showsl_lit
           "error in splitting cut transitions on LTS\n" .
          x));

}
