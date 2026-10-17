{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  CSR_Guarded_List_Measure(Csr_guard_sort(..), equal_csr_guard_sort,
                            Csr_guard_form, csr_guard_weak_pair,
                            csr_guard_strict_pair, csr_guard_symbolic_rank,
                            csr_guard_form_requirements,
                            csr_guard_normal_rule_backward_eq)
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

data Csr_guard_sort = Guard_Nat | Guard_List | Guard_IList;

equal_csr_guard_sort :: Csr_guard_sort -> Csr_guard_sort -> Bool;
equal_csr_guard_sort Guard_List Guard_IList = False;
equal_csr_guard_sort Guard_IList Guard_List = False;
equal_csr_guard_sort Guard_Nat Guard_IList = False;
equal_csr_guard_sort Guard_IList Guard_Nat = False;
equal_csr_guard_sort Guard_Nat Guard_List = False;
equal_csr_guard_sort Guard_List Guard_Nat = False;
equal_csr_guard_sort Guard_IList Guard_IList = True;
equal_csr_guard_sort Guard_List Guard_List = True;
equal_csr_guard_sort Guard_Nat Guard_Nat = True;

instance Eq Csr_guard_sort where {
  a == b = equal_csr_guard_sort a b;
};

data Csr_guard_form a =
  Guard_Form [(a, Csr_guard_sort)] [(a, Csr_guard_sort)] Arith.Nat;

csr_guard_erase_and ::
  forall a b. (Eq a) => a -> Term_Rewriting.Term a b -> Term_Rewriting.Term a b;
csr_guard_erase_and a (Term_Rewriting.Var x) = Term_Rewriting.Var x;
csr_guard_erase_and a (Term_Rewriting.Fun f ts) =
  (if f == a &&
        Arith.equal_nat (Arith.size_list ts)
          (Arith.nat_of_integer (2 :: Integer))
    then csr_guard_erase_and a (Arith.nth ts Arith.one_nat)
    else Term_Rewriting.Fun f (map (csr_guard_erase_and a) ts));

csr_guard_erase_admin ::
  forall a b.
    (Eq a) => a -> a -> a -> a -> a -> a ->
 a -> a -> Term_Rewriting.Term a b -> Term_Rewriting.Term a b;
csr_guard_erase_admin u11 u21 u31 su len ni co ta (Term_Rewriting.Var x) =
  Term_Rewriting.Var x;
csr_guard_erase_admin u11 u21 u31 su len ni co ta (Term_Rewriting.Fun f ts) =
  (if f == u11 &&
        Arith.equal_nat (Arith.size_list ts)
          (Arith.nat_of_integer (2 :: Integer))
    then Term_Rewriting.Fun su
           [Term_Rewriting.Fun len
              [csr_guard_erase_admin u11 u21 u31 su len ni co ta
                 (Arith.nth ts Arith.one_nat)]]
    else (if f == u21 && Arith.equal_nat (Arith.size_list ts) Arith.one_nat
           then Term_Rewriting.Fun ni []
           else (if f == u31 &&
                      Arith.equal_nat (Arith.size_list ts)
                        (Arith.nat_of_integer (4 :: Integer))
                  then Term_Rewriting.Fun co
                         [csr_guard_erase_admin u11 u21 u31 su len ni co ta
                            (Arith.nth ts
                              (Arith.nat_of_integer (3 :: Integer))),
                           Term_Rewriting.Fun ta
                             [csr_guard_erase_admin u11 u21 u31 su len ni co ta
                                (Arith.nth ts
                                  (Arith.nat_of_integer (2 :: Integer))),
                               csr_guard_erase_admin u11 u21 u31 su len ni co ta
                                 (Arith.nth ts Arith.one_nat)]]
                  else Term_Rewriting.Fun f
                         (map (csr_guard_erase_admin u11 u21 u31 su len ni co
                                ta)
                           ts))));

csr_guard_normalize ::
  forall a b.
    (Eq a) => a -> a -> a -> a -> a -> a ->
 a -> a -> a -> Term_Rewriting.Term a b -> Term_Rewriting.Term a b;
csr_guard_normalize a u11 u21 u31 su len ni co ta t =
  csr_guard_erase_and a (csr_guard_erase_admin u11 u21 u31 su len ni co ta t);

csr_guard_weak_pair ::
  forall a b c.
    a -> a -> b -> c -> (Term_Rewriting.Term a c, Term_Rewriting.Term b c);
csr_guard_weak_pair u11s tt lens l =
  (Term_Rewriting.Fun u11s [Term_Rewriting.Fun tt [], Term_Rewriting.Var l],
    Term_Rewriting.Fun lens [Term_Rewriting.Var l]);

csr_guard_strict_pair ::
  forall a b c.
    a -> a -> b -> b -> b -> b -> c -> c ->
 (Term_Rewriting.Term a c, Term_Rewriting.Term b c);
csr_guard_strict_pair lens co u11s a listp natp n l =
  (Term_Rewriting.Fun lens
     [Term_Rewriting.Fun co [Term_Rewriting.Var n, Term_Rewriting.Var l]],
    Term_Rewriting.Fun u11s
      [Term_Rewriting.Fun a
         [Term_Rewriting.Fun listp [Term_Rewriting.Var l],
           Term_Rewriting.Fun natp [Term_Rewriting.Var n]],
        Term_Rewriting.Var l]);

csr_guard_symbolic_rank ::
  forall a b.
    (Eq a) => a -> a -> a -> a -> a -> a ->
 a -> Csr_guard_sort -> Term_Rewriting.Term a b -> Maybe (Csr_guard_form b);
csr_guard_symbolic_rank z su len ni co ta zs a (Term_Rewriting.Var x) =
  Just (Guard_Form [(x, a)] [(x, a)] Arith.zero_nat);
csr_guard_symbolic_rank z su len ni co ta zs Guard_Nat (Term_Rewriting.Fun f ts)
  = (if f == z && null ts then Just (Guard_Form [] [] Arith.zero_nat)
      else (if f == su && Arith.equal_nat (Arith.size_list ts) Arith.one_nat
             then (case csr_guard_symbolic_rank z su len ni co ta zs Guard_Nat
                          (Arith.nth ts Arith.zero_nat)
                    of {
                    Nothing -> Nothing;
                    Just (Guard_Form req cs c) ->
                      Just (Guard_Form req cs (Arith.suc c));
                  })
             else (if f == len &&
                        Arith.equal_nat (Arith.size_list ts) Arith.one_nat
                    then csr_guard_symbolic_rank z su len ni co ta zs Guard_List
                           (Arith.nth ts Arith.zero_nat)
                    else Nothing)));
csr_guard_symbolic_rank z su len ni co ta zs Guard_List
  (Term_Rewriting.Fun f ts) =
  (if f == ni && null ts then Just (Guard_Form [] [] Arith.zero_nat)
    else (if f == co &&
               Arith.equal_nat (Arith.size_list ts)
                 (Arith.nat_of_integer (2 :: Integer))
           then (case csr_guard_symbolic_rank z su len ni co ta zs Guard_List
                        (Arith.nth ts Arith.one_nat)
                  of {
                  Nothing -> Nothing;
                  Just (Guard_Form reql coeffl cl) ->
                    Just (Guard_Form reql coeffl (Arith.suc cl));
                })
           else (if f == ta &&
                      Arith.equal_nat (Arith.size_list ts)
                        (Arith.nat_of_integer (2 :: Integer))
                  then (case (csr_guard_symbolic_rank z su len ni co ta zs
                                Guard_Nat (Arith.nth ts Arith.zero_nat),
                               csr_guard_symbolic_rank z su len ni co ta zs
                                 Guard_IList (Arith.nth ts Arith.one_nat))
                         of {
                         (Nothing, _) -> Nothing;
                         (Just (Guard_Form _ _ _), Nothing) -> Nothing;
                         (Just (Guard_Form reqn coeffn cn),
                           Just (Guard_Form reqi _ _))
                           -> Just (Guard_Form (reqn ++ reqi) coeffn cn);
                       })
                  else Nothing)));
csr_guard_symbolic_rank z su len ni co ta zs Guard_IList
  (Term_Rewriting.Fun f ts) =
  (if f == zs && null ts then Just (Guard_Form [] [] Arith.zero_nat)
    else (if f == co &&
               Arith.equal_nat (Arith.size_list ts)
                 (Arith.nat_of_integer (2 :: Integer))
           then (case csr_guard_symbolic_rank z su len ni co ta zs Guard_IList
                        (Arith.nth ts Arith.one_nat)
                  of {
                  Nothing -> Nothing;
                  Just (Guard_Form reqi _ _) ->
                    Just (Guard_Form reqi [] Arith.zero_nat);
                })
           else (if f == ni && null ts
                  then Just (Guard_Form [] [] Arith.zero_nat)
                  else (if f == ta &&
                             Arith.equal_nat (Arith.size_list ts)
                               (Arith.nat_of_integer (2 :: Integer))
                         then (case (csr_guard_symbolic_rank z su len ni co ta
                                       zs Guard_Nat
                                       (Arith.nth ts Arith.zero_nat),
                                      csr_guard_symbolic_rank z su len ni co ta
zs Guard_IList (Arith.nth ts Arith.one_nat))
                                of {
                                (Nothing, _) -> Nothing;
                                (Just (Guard_Form _ _ _), Nothing) -> Nothing;
                                (Just (Guard_Form reqn _ _),
                                  Just (Guard_Form reqi _ _))
                                  -> Just (Guard_Form (reqn ++ reqi) []
    Arith.zero_nat);
                              })
                         else Nothing))));

csr_guard_coefficients_le :: forall a. (Eq a) => [a] -> [a] -> Bool;
csr_guard_coefficients_le [] ys = True;
csr_guard_coefficients_le (x : xs) ys =
  Arith.membera ys x && csr_guard_coefficients_le xs (Arith.remove1 x ys);

csr_guard_form_backward_eq ::
  forall a. (Eq a) => Csr_guard_form a -> Csr_guard_form a -> Bool;
csr_guard_form_backward_eq (Guard_Form req_l cs_l c_l)
  (Guard_Form req_r cs_r c_r) =
  Arith.superset req_r req_l &&
    csr_guard_coefficients_le cs_l cs_r &&
      csr_guard_coefficients_le cs_r cs_l && Arith.equal_nat c_l c_r;

csr_guard_form_requirements ::
  forall a. Csr_guard_form a -> [(a, Csr_guard_sort)];
csr_guard_form_requirements (Guard_Form req cs c) = req;

csr_guard_normal_symbolic_rank ::
  forall a b.
    (Eq a) => a -> a -> a -> a -> a -> a ->
 a -> a -> a -> a -> a -> Csr_guard_sort ->
                            Term_Rewriting.Term a b -> Maybe (Csr_guard_form b);
csr_guard_normal_symbolic_rank aa u11 u21 u31 z su len ni co ta zs a t =
  csr_guard_symbolic_rank z su len ni co ta zs a
    (csr_guard_normalize aa u11 u21 u31 su len ni co ta t);

csr_guard_normal_rule_backward_eq ::
  forall a b.
    (Eq a,
      Eq b) => a -> a -> a -> a -> a -> a ->
  a -> a -> a -> a -> a -> Csr_guard_sort ->
                             Term_Rewriting.Term a b ->
                               Term_Rewriting.Term a b -> Bool;
csr_guard_normal_rule_backward_eq aa u11 u21 u31 z su len ni co ta zs a l r =
  (case csr_guard_normal_symbolic_rank aa u11 u21 u31 z su len ni co ta zs a r
    of {
    Nothing -> True;
    Just g ->
      (case csr_guard_normal_symbolic_rank aa u11 u21 u31 z su len ni co ta zs a
              l
        of {
        Nothing -> False;
        Just f -> csr_guard_form_backward_eq f g;
      });
  });

}
