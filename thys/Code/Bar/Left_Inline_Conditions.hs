{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Left_Inline_Conditions(left_inline) where {

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
import qualified HOL;
import qualified Term_Rewriting;
import qualified Arith;

left_inline ::
  forall a b.
    (Eq b) => Arith.Nat ->
                ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                  [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]) ->
                  ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
                    [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]);
left_inline i rho =
  let {
    cs = snd rho;
  } in (case Arith.nth cs i of {
         (s, t) ->
           let {
             sigma = Term_Rewriting.subst (Term_Rewriting.the_Var s) t;
             csa = Arith.take i cs ++ Arith.drop (Arith.suc i) cs;
           } in ((Term_Rewriting.eval_term Term_Rewriting.Fun (fst (fst rho))
                    sigma,
                   snd (fst rho)),
                  map (\ (sa, ta) ->
                        (sa, Term_Rewriting.eval_term Term_Rewriting.Fun ta
                               sigma))
                    csa);
       });

}
