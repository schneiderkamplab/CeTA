{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module QDP_To_SRS_Zantema(zantema_transform_impl) where {

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
import qualified Arith;
import qualified Term_Rewriting;

unary_term ::
  forall a b. [a] -> Term_Rewriting.Term a b -> Term_Rewriting.Term a b;
unary_term [] t = t;
unary_term (f : fs) t = Term_Rewriting.Fun f [unary_term fs t];

dest_unary_var :: forall a b. Term_Rewriting.Term a b -> Maybe ([a], b);
dest_unary_var (Term_Rewriting.Var x) = Just ([], x);
dest_unary_var (Term_Rewriting.Fun f [t]) =
  Arith.map_option (\ (fs, a) -> (f : fs, a)) (dest_unary_var t);
dest_unary_var (Term_Rewriting.Fun f []) = Nothing;
dest_unary_var (Term_Rewriting.Fun f (v : vb : vc)) = Nothing;

zantema_pair_impl ::
  forall a b.
    (Eq a,
      Eq b) => (Term_Rewriting.Term a b, Term_Rewriting.Term a b) ->
                 Maybe (Maybe (Term_Rewriting.Term a b,
                                Term_Rewriting.Term a b));
zantema_pair_impl
  (Term_Rewriting.Fun f [Term_Rewriting.Var x, t],
    Term_Rewriting.Fun g [s, Term_Rewriting.Var y])
  = (if f == g && not (x == y)
      then (case (dest_unary_var t, dest_unary_var s) of {
             (Nothing, _) -> Nothing;
             (Just (_, _), Nothing) -> Nothing;
             (Just (lhs, ya), Just (rhs, xa)) ->
               (if ya == y && xa == x && not (null lhs) && not (null rhs)
                 then Just (Just (unary_term lhs (Term_Rewriting.Var x),
                                   unary_term (reverse rhs)
                                     (Term_Rewriting.Var x)))
                 else Nothing);
           })
      else Nothing);
zantema_pair_impl
  (Term_Rewriting.Fun f
     [Term_Rewriting.Fun a [Term_Rewriting.Var xa], Term_Rewriting.Var ya],
    Term_Rewriting.Fun g
      [Term_Rewriting.Var x, Term_Rewriting.Fun b [Term_Rewriting.Var y]])
  = (if f == g && a == b && xa == x && ya == y && not (xa == ya)
      then Just Nothing else Nothing);
zantema_pair_impl (Term_Rewriting.Var vb, va) = Nothing;
zantema_pair_impl (Term_Rewriting.Fun vb [], va) = Nothing;
zantema_pair_impl (Term_Rewriting.Fun vb (Term_Rewriting.Fun vf [] : ve), va) =
  Nothing;
zantema_pair_impl
  (Term_Rewriting.Fun vb
     (Term_Rewriting.Fun vf (Term_Rewriting.Fun vd vh : vc) : ve),
    va)
  = Nothing;
zantema_pair_impl
  (Term_Rewriting.Fun vb (Term_Rewriting.Fun vf (v : vd : vh) : ve), va) =
  Nothing;
zantema_pair_impl (Term_Rewriting.Fun vb [Term_Rewriting.Fun vf vg], va) =
  Nothing;
zantema_pair_impl
  (Term_Rewriting.Fun vb
     (Term_Rewriting.Fun vf vg : Term_Rewriting.Fun vd vh : vc),
    va)
  = Nothing;
zantema_pair_impl
  (Term_Rewriting.Fun vb (Term_Rewriting.Fun vf vg : v : vd : vh), va) =
  Nothing;
zantema_pair_impl
  (Term_Rewriting.Fun vb (Term_Rewriting.Fun vf vg : ve), Term_Rewriting.Var v)
  = Nothing;
zantema_pair_impl
  (Term_Rewriting.Fun vb (Term_Rewriting.Fun vf vg : ve),
    Term_Rewriting.Fun v [])
  = Nothing;
zantema_pair_impl
  (Term_Rewriting.Fun vb (Term_Rewriting.Fun vf vg : ve),
    Term_Rewriting.Fun v (Term_Rewriting.Fun vi vj : vh))
  = Nothing;
zantema_pair_impl
  (Term_Rewriting.Fun vb (Term_Rewriting.Fun vf vg : ve),
    Term_Rewriting.Fun v [vd])
  = Nothing;
zantema_pair_impl
  (Term_Rewriting.Fun vb (Term_Rewriting.Fun vf vg : ve),
    Term_Rewriting.Fun v (vd : Term_Rewriting.Var vk : vj))
  = Nothing;
zantema_pair_impl
  (Term_Rewriting.Fun vb (Term_Rewriting.Fun vf vg : ve),
    Term_Rewriting.Fun v (vd : Term_Rewriting.Fun vk [] : vj))
  = Nothing;
zantema_pair_impl
  (Term_Rewriting.Fun vb (Term_Rewriting.Fun vf vg : ve),
    Term_Rewriting.Fun v
      (vd : Term_Rewriting.Fun vk (Term_Rewriting.Fun vo vp : vn) : vj))
  = Nothing;
zantema_pair_impl
  (Term_Rewriting.Fun vb (Term_Rewriting.Fun vf vg : ve),
    Term_Rewriting.Fun v (vd : Term_Rewriting.Fun vk (vm : vo : vp) : vj))
  = Nothing;
zantema_pair_impl
  (Term_Rewriting.Fun vb (Term_Rewriting.Fun vf vg : ve),
    Term_Rewriting.Fun v (vd : vi : vk : vl))
  = Nothing;
zantema_pair_impl (Term_Rewriting.Fun vb [vd], va) = Nothing;
zantema_pair_impl (Term_Rewriting.Fun vb (vd : vf : vh : vi), va) = Nothing;
zantema_pair_impl (v, Term_Rewriting.Var vb) = Nothing;
zantema_pair_impl (v, Term_Rewriting.Fun vb []) = Nothing;
zantema_pair_impl (v, Term_Rewriting.Fun vb [vd]) = Nothing;
zantema_pair_impl
  (Term_Rewriting.Fun va (Term_Rewriting.Var vj : vf),
    Term_Rewriting.Fun vb (vd : Term_Rewriting.Fun vh vi : vg))
  = Nothing;
zantema_pair_impl
  (Term_Rewriting.Fun va (ve : Term_Rewriting.Fun vl vm : vk),
    Term_Rewriting.Fun vb (vd : Term_Rewriting.Fun vh vi : vg))
  = Nothing;
zantema_pair_impl
  (v, Term_Rewriting.Fun vb
        (Term_Rewriting.Fun va vc : Term_Rewriting.Fun vh vi : vg))
  = Nothing;
zantema_pair_impl
  (v, Term_Rewriting.Fun vb (vd : Term_Rewriting.Fun vh [] : vg)) = Nothing;
zantema_pair_impl
  (v, Term_Rewriting.Fun vb
        (vd : Term_Rewriting.Fun vh (Term_Rewriting.Fun ve vf : vc) : vg))
  = Nothing;
zantema_pair_impl
  (v, Term_Rewriting.Fun vb (vd : Term_Rewriting.Fun vh (va : ve : vf) : vg)) =
  Nothing;
zantema_pair_impl
  (v, Term_Rewriting.Fun vb (vd : Term_Rewriting.Fun vh vi : va : vc)) =
  Nothing;
zantema_pair_impl (v, Term_Rewriting.Fun vb (vd : vf : vh : vi)) = Nothing;

zantema_transform_impl ::
  forall a b.
    (Eq a,
      Eq b) => [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                 Maybe [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
zantema_transform_impl [] = Just [];
zantema_transform_impl (lr : p) =
  (case (zantema_pair_impl lr, zantema_transform_impl p) of {
    (Nothing, _) -> Nothing;
    (Just Nothing, Nothing) -> Nothing;
    (Just Nothing, Just a) -> Just a;
    (Just (Just _), Nothing) -> Nothing;
    (Just (Just r), Just s) -> Just (r : s);
  });

}
