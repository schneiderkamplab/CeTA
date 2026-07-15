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
import qualified Orderings;
import qualified Show_Instances;
import qualified Str;
import qualified Term_More;
import qualified Option;
import qualified HOL;
import qualified Product_Type;
import qualified List;
import qualified Term;
import qualified Arith;

unapp ::
  forall a b. (Eq a) => a -> Term.Term a b -> (Term.Term a b, [Term.Term a b]);
unapp a (Term.Var x) = (Term.Var x, []);
unapp a (Term.Fun f ss) =
  (if f == a &&
        Arith.equal_nat (List.size_list ss)
          (Arith.nat_of_integer (2 :: Integer))
    then (case unapp a (List.nth ss Arith.zero_nat) of {
           (r, ts) -> (r, ts ++ [List.nth ss Arith.one_nat]);
         })
    else (Term.Fun f ss, []));

aarity :: forall a. (a -> Arith.Nat -> [a]) -> a -> Arith.Nat -> Arith.Nat;
aarity sm f n = Arith.minus_nat (List.size_list (sm f n)) Arith.one_nat;

hvf_top :: forall a b. (Eq a) => a -> Arith.Nat -> Term.Term a b -> Bool;
hvf_top a n (Term.Fun f ts) =
  (if f == a && Arith.equal_nat (List.size_list ts) n
    then not (Term.is_Var (List.hd ts)) else True);
hvf_top a n (Term.Var uu) = False;

hvf_term :: forall a b. (Eq a) => a -> Term.Term a b -> Bool;
hvf_term a t = (case unapp a t of {
                 (Term.Var _, ts) -> null ts;
                 (Term.Fun _ us, ts) -> all (hvf_term a) (us ++ ts);
               });

apply_args ::
  forall a b. a -> Term.Term a b -> [Term.Term a b] -> Term.Term a b;
apply_args a t [] = t;
apply_args a t (s : ss) = apply_args a (Term.Fun a [t, s]) ss;

get_symbol ::
  forall a. (a -> Arith.Nat -> [a]) -> a -> Arith.Nat -> Arith.Nat -> a;
get_symbol sm f n i = List.nth (sm f n) i;

aarity_term ::
  forall a b.
    (Eq a) => a -> (a -> Arith.Nat -> [a]) -> Term.Term a b -> Maybe Arith.Nat;
aarity_term a sm t =
  (case unapp a t of {
    (Term.Var _, _) -> Nothing;
    (Term.Fun f ss, ts) ->
      Just (Arith.minus_nat (aarity sm f (List.size_list ss))
             (List.size_list ts));
  });

uncurry_top ::
  forall a b.
    (Eq a) => a -> Arith.Nat ->
                     (a -> Arith.Nat -> [a]) -> Term.Term a b -> Term.Term a b;
uncurry_top a n sm (Term.Fun f ts) =
  let {
    mt = map (Term_More.map_funs_term_wa
               (\ (fa, na) -> get_symbol sm fa na Arith.zero_nat));
    t = List.hd ts;
  } in (if f == a &&
             Arith.equal_nat (List.size_list ts) n &&
               not (Term.is_Var t) &&
                 (case Option.the (Term.root t) of {
                   (h, m) ->
                     not (Arith.equal_nat (aarity sm h m) Arith.zero_nat);
                 })
         then (case t of {
                Term.Fun g ss ->
                  Term.Fun (get_symbol sm g (List.size_list ss) Arith.one_nat)
                    (mt (ss ++ List.tl ts));
              })
         else Term.Fun (case (f, List.size_list ts) of {
                         (fa, na) -> get_symbol sm fa na Arith.zero_nat;
                       })
                (mt ts));
uncurry_top a n sm (Term.Var x) = Term.Var x;

generate_var :: Arith.Nat -> [Str.Char];
generate_var i =
  Str.char_0x78 : Show_Instances.shows_prec_nat Arith.zero_nat i [];

uncurry_term ::
  forall a b.
    (Eq a) => a -> (a -> Arith.Nat -> [a]) -> Term.Term a b -> Term.Term a b;
uncurry_term a sm t =
  (case unapp a t of {
    (Term.Var x, ts) -> apply_args a (Term.Var x) (map (uncurry_term a sm) ts);
    (Term.Fun f ss, ts) ->
      let {
        n = List.size_list ss;
        uss = map (uncurry_term a sm) ss;
        uts = map (uncurry_term a sm) ts;
        aa = aarity sm f n;
        m = Orderings.min (List.size_list ts) aa;
        fm = get_symbol sm f n m;
      } in apply_args a (Term.Fun fm (uss ++ List.take m uts))
             (List.drop m uts);
  });

generate_f_xs :: forall a. a -> Arith.Nat -> Term.Term a [Str.Char];
generate_f_xs f n =
  Term.Fun f
    (map (\ i -> Term.Var (generate_var i)) (List.upt Arith.zero_nat n));

}
