{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Uncurry(aarity, hvf_top, hvf_term, get_symbol, aarity_term, uncurry_top,
           generate_var, uncurry_term, generate_f_xs)
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
import qualified Quasi_Order;
import qualified HOL;
import qualified Term_Rewriting;
import qualified Arith;

unapp ::
  forall a b.
    (Eq a) => a -> Term_Rewriting.Term a b ->
                     (Term_Rewriting.Term a b, [Term_Rewriting.Term a b]);
unapp a (Term_Rewriting.Var x) = (Term_Rewriting.Var x, []);
unapp a (Term_Rewriting.Fun f ss) =
  (if f == a &&
        Arith.equal_nat (Arith.size_list ss)
          (Arith.nat_of_integer (2 :: Integer))
    then (case unapp a (Arith.nth ss Arith.zero_nat) of {
           (r, ts) -> (r, ts ++ [Arith.nth ss Arith.one_nat]);
         })
    else (Term_Rewriting.Fun f ss, []));

aarity :: forall a. (a -> Arith.Nat -> [a]) -> a -> Arith.Nat -> Arith.Nat;
aarity sm f n = Arith.minus_nat (Arith.size_list (sm f n)) Arith.one_nat;

hvf_top ::
  forall a b. (Eq a) => a -> Arith.Nat -> Term_Rewriting.Term a b -> Bool;
hvf_top a n (Term_Rewriting.Fun f ts) =
  (if f == a && Arith.equal_nat (Arith.size_list ts) n
    then not (Term_Rewriting.is_Var (Arith.hda ts)) else True);
hvf_top a n (Term_Rewriting.Var uu) = False;

hvf_term :: forall a b. (Eq a) => a -> Term_Rewriting.Term a b -> Bool;
hvf_term a t = (case unapp a t of {
                 (Term_Rewriting.Var _, ts) -> null ts;
                 (Term_Rewriting.Fun _ us, ts) -> all (hvf_term a) (us ++ ts);
               });

apply_args ::
  forall a b.
    a -> Term_Rewriting.Term a b ->
           [Term_Rewriting.Term a b] -> Term_Rewriting.Term a b;
apply_args a t [] = t;
apply_args a t (s : ss) = apply_args a (Term_Rewriting.Fun a [t, s]) ss;

get_symbol ::
  forall a. (a -> Arith.Nat -> [a]) -> a -> Arith.Nat -> Arith.Nat -> a;
get_symbol sm f n i = Arith.nth (sm f n) i;

aarity_term ::
  forall a b.
    (Eq a) => a -> (a -> Arith.Nat -> [a]) ->
                     Term_Rewriting.Term a b -> Maybe Arith.Nat;
aarity_term a sm t =
  (case unapp a t of {
    (Term_Rewriting.Var _, _) -> Nothing;
    (Term_Rewriting.Fun f ss, ts) ->
      Just (Arith.minus_nat (aarity sm f (Arith.size_list ss))
             (Arith.size_list ts));
  });

uncurry_top ::
  forall a b.
    (Eq a) => a -> Arith.Nat ->
                     (a -> Arith.Nat -> [a]) ->
                       Term_Rewriting.Term a b -> Term_Rewriting.Term a b;
uncurry_top a n sm (Term_Rewriting.Fun f ts) =
  let {
    mt = map (Term_Rewriting.map_funs_term_wa
               (\ (fa, na) -> get_symbol sm fa na Arith.zero_nat));
    t = Arith.hda ts;
  } in (if f == a &&
             Arith.equal_nat (Arith.size_list ts) n &&
               not (Term_Rewriting.is_Var t) &&
                 (case Arith.the (Term_Rewriting.root t) of {
                   (h, m) ->
                     not (Arith.equal_nat (aarity sm h m) Arith.zero_nat);
                 })
         then (case t of {
                Term_Rewriting.Fun g ss ->
                  Term_Rewriting.Fun
                    (get_symbol sm g (Arith.size_list ss) Arith.one_nat)
                    (mt (ss ++ Arith.tla ts));
              })
         else Term_Rewriting.Fun
                (case (f, Arith.size_list ts) of {
                  (fa, na) -> get_symbol sm fa na Arith.zero_nat;
                })
                (mt ts));
uncurry_top a n sm (Term_Rewriting.Var x) = Term_Rewriting.Var x;

generate_var :: Arith.Nat -> [Arith.Char];
generate_var i =
  Arith.char_0x78 : Term_Rewriting.shows_prec_nat Arith.zero_nat i [];

uncurry_term ::
  forall a b.
    (Eq a) => a -> (a -> Arith.Nat -> [a]) ->
                     Term_Rewriting.Term a b -> Term_Rewriting.Term a b;
uncurry_term a sm t =
  (case unapp a t of {
    (Term_Rewriting.Var x, ts) ->
      apply_args a (Term_Rewriting.Var x) (map (uncurry_term a sm) ts);
    (Term_Rewriting.Fun f ss, ts) ->
      let {
        n = Arith.size_list ss;
        uss = map (uncurry_term a sm) ss;
        uts = map (uncurry_term a sm) ts;
        aa = aarity sm f n;
        m = Quasi_Order.min (Arith.size_list ts) aa;
        fm = get_symbol sm f n m;
      } in apply_args a (Term_Rewriting.Fun fm (uss ++ Arith.take m uts))
             (Arith.drop m uts);
  });

generate_f_xs :: forall a. a -> Arith.Nat -> Term_Rewriting.Term a [Arith.Char];
generate_f_xs f n =
  Term_Rewriting.Fun f
    (map (\ i -> Term_Rewriting.Var (generate_var i))
      (Arith.upt Arith.zero_nat n));

}
