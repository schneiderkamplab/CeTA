{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  AC_Termination_Problem_Spec(Ac_tp_ops_ext(..), a, c, e, r, mk, delete_rules)
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
import qualified Term_Rewriting;
import qualified Arith;

data Ac_tp_ops_ext a b c d =
  Ac_tp_ops_ext
    (a -> (Arith.Set (Term_Rewriting.Term b c, Term_Rewriting.Term b c),
            (Arith.Set b, Arith.Set b)))
    (a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)]) (a -> [b])
    (a -> [b])
    ([(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] -> [b] -> [b] -> a)
    (a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] -> a)
    (a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)]) d;

a :: forall a b c d. Ac_tp_ops_ext a b c d -> a -> [b];
a (Ac_tp_ops_ext ac_tp r a c mk delete_rules e more) = a;

c :: forall a b c d. Ac_tp_ops_ext a b c d -> a -> [b];
c (Ac_tp_ops_ext ac_tp r a c mk delete_rules e more) = c;

e :: forall a b c d.
       Ac_tp_ops_ext a b c d ->
         a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)];
e (Ac_tp_ops_ext ac_tp r a c mk delete_rules e more) = e;

r :: forall a b c d.
       Ac_tp_ops_ext a b c d ->
         a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)];
r (Ac_tp_ops_ext ac_tp r a c mk delete_rules e more) = r;

mk :: forall a b c d.
        Ac_tp_ops_ext a b c d ->
          [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
            [b] -> [b] -> a;
mk (Ac_tp_ops_ext ac_tp r a c mk delete_rules e more) = mk;

delete_rules ::
  forall a b c d.
    Ac_tp_ops_ext a b c d ->
      a -> [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] -> a;
delete_rules (Ac_tp_ops_ext ac_tp r a c mk delete_rules e more) = delete_rules;

}
