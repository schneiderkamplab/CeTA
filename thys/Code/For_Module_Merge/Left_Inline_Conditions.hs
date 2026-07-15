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
import qualified Product_Type;
import qualified List;
import qualified HOL;
import qualified Term;
import qualified Arith;

left_inline ::
  forall a b.
    (Eq b) => Arith.Nat ->
                ((Term.Term a b, Term.Term a b),
                  [(Term.Term a b, Term.Term a b)]) ->
                  ((Term.Term a b, Term.Term a b),
                    [(Term.Term a b, Term.Term a b)]);
left_inline i rho =
  let {
    cs = snd rho;
  } in (case List.nth cs i of {
         (s, t) ->
           let {
             sigma = Term.subst (Term.the_Var s) t;
             csa = List.take i cs ++ List.drop (Arith.suc i) cs;
           } in ((Term.eval_term Term.Fun (fst (fst rho)) sigma, snd (fst rho)),
                  map (\ (sa, ta) -> (sa, Term.eval_term Term.Fun ta sigma))
                    csa);
       });

}
