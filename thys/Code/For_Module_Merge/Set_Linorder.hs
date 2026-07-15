{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Set_Linorder(exhaustive_fusion, compl_set_less_aux, set_less_aux_Compl,
                compl_set_less_eq_aux, set_less_eq_aux_Compl,
                proper_interval_set_aux, compl_set_less_aux_fusion,
                set_less_aux_Compl_fusion, compl_set_less_eq_aux_fusion,
                set_less_eq_aux_Compl_fusion, proper_interval_nat,
                proper_interval_Compl_set_aux, proper_interval_set_Compl_aux,
                proper_interval_set_aux_fusion,
                proper_interval_Compl_set_aux_fusion,
                proper_interval_set_Compl_aux_fusion)
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
import qualified Finite_Set;
import qualified Set;
import qualified Collection_Order;
import qualified Cardinality;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified HOL;
import qualified List_Fusion;
import qualified Product_Type;
import qualified List;
import qualified Arith;

length_last :: forall a. [a] -> (Arith.Nat, a);
length_last [] = (Arith.zero_nat, error "undefined");
length_last (x : xs) =
  List.fold (\ xa (n, _) -> (Arith.plus_nat n Arith.one_nat, xa)) xs
    (Arith.one_nat, x);

length_last_fusion ::
  forall a b. List_Fusion.Generator a b -> b -> (Arith.Nat, a);
length_last_fusion g s =
  (if List_Fusion.has_next g s
    then (case List_Fusion.next g s of {
           (x, sa) ->
             List_Fusion.fold_fusion g
               (\ xa (n, _) -> (Arith.plus_nat n Arith.one_nat, xa)) sa
               (Arith.one_nat, x);
         })
    else (Arith.zero_nat, error "undefined"));

exhaustive_above :: forall a. (Maybe a -> Maybe a -> Bool) -> a -> [a] -> Bool;
exhaustive_above proper_interval x [] = not (proper_interval (Just x) Nothing);
exhaustive_above proper_interval x (y : ys) =
  not (proper_interval (Just x) (Just y)) &&
    exhaustive_above proper_interval y ys;

exhaustive_above_fusion ::
  forall a b.
    (Maybe a -> Maybe a -> Bool) -> List_Fusion.Generator a b -> a -> b -> Bool;
exhaustive_above_fusion proper_interval g y s =
  (if List_Fusion.has_next g s
    then (case List_Fusion.next g s of {
           (x, sa) ->
             not (proper_interval (Just y) (Just x)) &&
               exhaustive_above_fusion proper_interval g x sa;
         })
    else not (proper_interval (Just y) Nothing));

exhaustive_fusion ::
  forall a b.
    (Maybe a -> Maybe a -> Bool) -> List_Fusion.Generator a b -> b -> Bool;
exhaustive_fusion proper_interval g s =
  List_Fusion.has_next g s &&
    (case List_Fusion.next g s of {
      (x, sa) ->
        not (proper_interval Nothing (Just x)) &&
          exhaustive_above_fusion proper_interval g x sa;
    });

compl_set_less_aux ::
  forall a.
    (a -> a -> Bool) ->
      (Maybe a -> Maybe a -> Bool) -> Maybe a -> [a] -> [a] -> Bool;
compl_set_less_aux less proper_interval ao [] ys = False;
compl_set_less_aux less proper_interval ao xs [] = False;
compl_set_less_aux less proper_interval ao (x : xs) (y : ys) =
  (if less x y
    then not (proper_interval ao (Just x)) &&
           compl_set_less_aux less proper_interval (Just x) xs (y : ys)
    else (if less y x
           then not (proper_interval ao (Just y)) &&
                  compl_set_less_aux less proper_interval (Just y) (x : xs) ys
           else not (proper_interval ao (Just y))));

set_less_aux_Compl ::
  forall a.
    (a -> a -> Bool) ->
      (Maybe a -> Maybe a -> Bool) -> Maybe a -> [a] -> [a] -> Bool;
set_less_aux_Compl less proper_interval ao [] [] = proper_interval ao Nothing;
set_less_aux_Compl less proper_interval ao [] (y : ys) =
  proper_interval ao (Just y) ||
    set_less_aux_Compl less proper_interval (Just y) [] ys;
set_less_aux_Compl less proper_interval ao (x : xs) [] =
  proper_interval ao (Just x) ||
    set_less_aux_Compl less proper_interval (Just x) xs [];
set_less_aux_Compl less proper_interval ao (x : xs) (y : ys) =
  (if less x y
    then proper_interval ao (Just x) ||
           set_less_aux_Compl less proper_interval (Just x) xs (y : ys)
    else (if less y x
           then proper_interval ao (Just y) ||
                  set_less_aux_Compl less proper_interval (Just y) (x : xs) ys
           else proper_interval ao (Just y)));

compl_set_less_eq_aux ::
  forall a.
    (a -> a -> Bool) ->
      (Maybe a -> Maybe a -> Bool) -> Maybe a -> [a] -> [a] -> Bool;
compl_set_less_eq_aux less proper_interval ao [] [] =
  not (proper_interval ao Nothing);
compl_set_less_eq_aux less proper_interval ao [] (y : ys) =
  not (proper_interval ao (Just y)) &&
    compl_set_less_eq_aux less proper_interval (Just y) [] ys;
compl_set_less_eq_aux less proper_interval ao (x : xs) [] =
  not (proper_interval ao (Just x)) &&
    compl_set_less_eq_aux less proper_interval (Just x) xs [];
compl_set_less_eq_aux less proper_interval ao (x : xs) (y : ys) =
  (if less x y
    then not (proper_interval ao (Just x)) &&
           compl_set_less_eq_aux less proper_interval (Just x) xs (y : ys)
    else (if less y x
           then not (proper_interval ao (Just y)) &&
                  compl_set_less_eq_aux less proper_interval (Just y) (x : xs)
                    ys
           else not (proper_interval ao (Just y))));

set_less_eq_aux_Compl ::
  forall a.
    (a -> a -> Bool) ->
      (Maybe a -> Maybe a -> Bool) -> Maybe a -> [a] -> [a] -> Bool;
set_less_eq_aux_Compl less proper_interval ao [] ys = True;
set_less_eq_aux_Compl less proper_interval ao xs [] = True;
set_less_eq_aux_Compl less proper_interval ao (x : xs) (y : ys) =
  (if less x y
    then proper_interval ao (Just x) ||
           set_less_eq_aux_Compl less proper_interval (Just x) xs (y : ys)
    else (if less y x
           then proper_interval ao (Just y) ||
                  set_less_eq_aux_Compl less proper_interval (Just y) (x : xs)
                    ys
           else proper_interval ao (Just y)));

proper_interval_set_aux ::
  forall a.
    (a -> a -> Bool) -> (Maybe a -> Maybe a -> Bool) -> [a] -> [a] -> Bool;
proper_interval_set_aux less proper_interval xs [] = False;
proper_interval_set_aux less proper_interval [] (y : ys) =
  not (null ys) || proper_interval (Just y) Nothing;
proper_interval_set_aux less proper_interval (x : xs) (y : ys) =
  (if less x y then False
    else (if less y x
           then proper_interval (Just y) (Just x) ||
                  (not (null ys) || not (exhaustive_above proper_interval x xs))
           else proper_interval_set_aux less proper_interval xs ys));

compl_set_less_aux_fusion ::
  forall a b c.
    (a -> a -> Bool) ->
      (Maybe a -> Maybe a -> Bool) ->
        List_Fusion.Generator a b ->
          List_Fusion.Generator a c -> Maybe a -> b -> c -> Bool;
compl_set_less_aux_fusion less proper_interval g1 g2 ao s1 s2 =
  List_Fusion.has_next g1 s1 &&
    List_Fusion.has_next g2 s2 &&
      (case List_Fusion.next g1 s1 of {
        (x, s1a) ->
          (case List_Fusion.next g2 s2 of {
            (y, s2a) ->
              (if less x y
                then not (proper_interval ao (Just x)) &&
                       compl_set_less_aux_fusion less proper_interval g1 g2
                         (Just x) s1a s2
                else (if less y x
                       then not (proper_interval ao (Just y)) &&
                              compl_set_less_aux_fusion less proper_interval g1
                                g2 (Just y) s1 s2a
                       else not (proper_interval ao (Just y))));
          });
      });

set_less_aux_Compl_fusion ::
  forall a b c.
    (a -> a -> Bool) ->
      (Maybe a -> Maybe a -> Bool) ->
        List_Fusion.Generator a b ->
          List_Fusion.Generator a c -> Maybe a -> b -> c -> Bool;
set_less_aux_Compl_fusion less proper_interval g1 g2 ao s1 s2 =
  (if List_Fusion.has_next g1 s1
    then (case List_Fusion.next g1 s1 of {
           (x, s1a) ->
             (if List_Fusion.has_next g2 s2
               then (case List_Fusion.next g2 s2 of {
                      (y, s2a) ->
                        (if less x y
                          then proper_interval ao (Just x) ||
                                 set_less_aux_Compl_fusion less proper_interval
                                   g1 g2 (Just x) s1a s2
                          else (if less y x
                                 then proper_interval ao (Just y) ||
set_less_aux_Compl_fusion less proper_interval g1 g2 (Just y) s1 s2a
                                 else proper_interval ao (Just y)));
                    })
               else proper_interval ao (Just x) ||
                      set_less_aux_Compl_fusion less proper_interval g1 g2
                        (Just x) s1a s2);
         })
    else (if List_Fusion.has_next g2 s2
           then (case List_Fusion.next g2 s2 of {
                  (y, s2a) ->
                    proper_interval ao (Just y) ||
                      set_less_aux_Compl_fusion less proper_interval g1 g2
                        (Just y) s1 s2a;
                })
           else proper_interval ao Nothing));

compl_set_less_eq_aux_fusion ::
  forall a b c.
    (a -> a -> Bool) ->
      (Maybe a -> Maybe a -> Bool) ->
        List_Fusion.Generator a b ->
          List_Fusion.Generator a c -> Maybe a -> b -> c -> Bool;
compl_set_less_eq_aux_fusion less proper_interval g1 g2 ao s1 s2 =
  (if List_Fusion.has_next g1 s1
    then (case List_Fusion.next g1 s1 of {
           (x, s1a) ->
             (if List_Fusion.has_next g2 s2
               then (case List_Fusion.next g2 s2 of {
                      (y, s2a) ->
                        (if less x y
                          then not (proper_interval ao (Just x)) &&
                                 compl_set_less_eq_aux_fusion less
                                   proper_interval g1 g2 (Just x) s1a s2
                          else (if less y x
                                 then not (proper_interval ao (Just y)) &&
compl_set_less_eq_aux_fusion less proper_interval g1 g2 (Just y) s1 s2a
                                 else not (proper_interval ao (Just y))));
                    })
               else not (proper_interval ao (Just x)) &&
                      compl_set_less_eq_aux_fusion less proper_interval g1 g2
                        (Just x) s1a s2);
         })
    else (if List_Fusion.has_next g2 s2
           then (case List_Fusion.next g2 s2 of {
                  (y, s2a) ->
                    not (proper_interval ao (Just y)) &&
                      compl_set_less_eq_aux_fusion less proper_interval g1 g2
                        (Just y) s1 s2a;
                })
           else not (proper_interval ao Nothing)));

set_less_eq_aux_Compl_fusion ::
  forall a b c.
    (a -> a -> Bool) ->
      (Maybe a -> Maybe a -> Bool) ->
        List_Fusion.Generator a b ->
          List_Fusion.Generator a c -> Maybe a -> b -> c -> Bool;
set_less_eq_aux_Compl_fusion less proper_interval g1 g2 ao s1 s2 =
  (if List_Fusion.has_next g1 s1
    then (if List_Fusion.has_next g2 s2
           then (case List_Fusion.next g1 s1 of {
                  (x, s1a) ->
                    (case List_Fusion.next g2 s2 of {
                      (y, s2a) ->
                        (if less x y
                          then proper_interval ao (Just x) ||
                                 set_less_eq_aux_Compl_fusion less
                                   proper_interval g1 g2 (Just x) s1a s2
                          else (if less y x
                                 then proper_interval ao (Just y) ||
set_less_eq_aux_Compl_fusion less proper_interval g1 g2 (Just y) s1 s2a
                                 else proper_interval ao (Just y)));
                    });
                })
           else True)
    else True);

proper_interval_nat :: Maybe Arith.Nat -> Maybe Arith.Nat -> Bool;
proper_interval_nat no Nothing = True;
proper_interval_nat Nothing (Just x) = Arith.less_nat Arith.zero_nat x;
proper_interval_nat (Just x) (Just y) =
  Arith.less_nat Arith.one_nat (Arith.minus_nat y x);

proper_interval_Compl_set_aux ::
  forall a.
    (a -> a -> Bool) ->
      (Maybe a -> Maybe a -> Bool) -> Maybe a -> [a] -> [a] -> Bool;
proper_interval_Compl_set_aux less proper_interval ao (x : xs) (y : ys) =
  (if less x y
    then not (proper_interval ao (Just x)) &&
           proper_interval_Compl_set_aux less proper_interval (Just x) xs
             (y : ys)
    else (if less y x
           then not (proper_interval ao (Just y)) &&
                  proper_interval_Compl_set_aux less proper_interval (Just y)
                    (x : xs) ys
           else not (proper_interval ao (Just x)) &&
                  (if null ys then not (null xs) else True)));
proper_interval_Compl_set_aux less proper_interval ao [] uv = False;
proper_interval_Compl_set_aux less proper_interval ao uu [] = False;

proper_interval_set_Compl_aux ::
  forall a.
    (Cardinality.Card_UNIV a, Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Set_Impl.Set_impl a) => (a -> a -> Bool) ->
                                (Maybe a -> Maybe a -> Bool) ->
                                  Maybe a -> Arith.Nat -> [a] -> [a] -> Bool;
proper_interval_set_Compl_aux less proper_interval ao n [] [] =
  Arith.less_nat (Arith.plus_nat n Arith.one_nat)
    ((Finite_Set.card :: Set.Set a -> Arith.Nat) (Set.top_set :: Set.Set a));
proper_interval_set_Compl_aux less proper_interval ao n [] (y : ys) =
  let {
    m = Arith.minus_nat
          ((Finite_Set.card :: Set.Set a -> Arith.Nat)
            (Set.top_set :: Set.Set a))
          n;
  } in (case length_last (y : ys) of {
         (len_y, ya) ->
           not (Arith.equal_nat m len_y) &&
             (if Arith.equal_nat m (Arith.plus_nat len_y Arith.one_nat)
               then not (proper_interval (Just ya) Nothing) else True);
       });
proper_interval_set_Compl_aux less proper_interval ao n (x : xs) [] =
  let {
    m = Arith.minus_nat
          ((Finite_Set.card :: Set.Set a -> Arith.Nat)
            (Set.top_set :: Set.Set a))
          n;
  } in (case length_last (x : xs) of {
         (len_x, xa) ->
           not (Arith.equal_nat m len_x) &&
             (if Arith.equal_nat m (Arith.plus_nat len_x Arith.one_nat)
               then not (proper_interval (Just xa) Nothing) else True);
       });
proper_interval_set_Compl_aux less proper_interval ao n (x : xs) (y : ys) =
  (if less x y
    then proper_interval ao (Just x) ||
           proper_interval_set_Compl_aux less proper_interval (Just x)
             (Arith.plus_nat n Arith.one_nat) xs (y : ys)
    else (if less y x
           then proper_interval ao (Just y) ||
                  proper_interval_set_Compl_aux less proper_interval (Just y)
                    (Arith.plus_nat n Arith.one_nat) (x : xs) ys
           else proper_interval ao (Just x) &&
                  let {
                    m = Arith.minus_nat
                          ((Finite_Set.card :: Set.Set a -> Arith.Nat)
                            (Set.top_set :: Set.Set a))
                          n;
                  } in not (Arith.equal_nat
                             (Arith.minus_nat m (List.size_list ys))
                             (Arith.nat_of_integer (2 :: Integer))) ||
                         not (Arith.equal_nat
                               (Arith.minus_nat m (List.size_list xs))
                               (Arith.nat_of_integer (2 :: Integer)))));

proper_interval_set_aux_fusion ::
  forall a b c.
    (a -> a -> Bool) ->
      (Maybe a -> Maybe a -> Bool) ->
        List_Fusion.Generator a b ->
          List_Fusion.Generator a c -> b -> c -> Bool;
proper_interval_set_aux_fusion less proper_interval g1 g2 s1 s2 =
  List_Fusion.has_next g2 s2 &&
    (case List_Fusion.next g2 s2 of {
      (y, s2a) ->
        (if List_Fusion.has_next g1 s1
          then (case List_Fusion.next g1 s1 of {
                 (x, s1a) ->
                   (if less x y then False
                     else (if less y x
                            then proper_interval (Just y) (Just x) ||
                                   (List_Fusion.has_next g2 s2a ||
                                     not (exhaustive_above_fusion
   proper_interval g1 x s1a))
                            else proper_interval_set_aux_fusion less
                                   proper_interval g1 g2 s1a s2a));
               })
          else List_Fusion.has_next g2 s2a || proper_interval (Just y) Nothing);
    });

proper_interval_Compl_set_aux_fusion ::
  forall a b c.
    (a -> a -> Bool) ->
      (Maybe a -> Maybe a -> Bool) ->
        List_Fusion.Generator a b ->
          List_Fusion.Generator a c -> Maybe a -> b -> c -> Bool;
proper_interval_Compl_set_aux_fusion less proper_interval g1 g2 ao s1 s2 =
  List_Fusion.has_next g1 s1 &&
    List_Fusion.has_next g2 s2 &&
      (case List_Fusion.next g1 s1 of {
        (x, s1a) ->
          (case List_Fusion.next g2 s2 of {
            (y, s2a) ->
              (if less x y
                then not (proper_interval ao (Just x)) &&
                       proper_interval_Compl_set_aux_fusion less proper_interval
                         g1 g2 (Just x) s1a s2
                else (if less y x
                       then not (proper_interval ao (Just y)) &&
                              proper_interval_Compl_set_aux_fusion less
                                proper_interval g1 g2 (Just y) s1 s2a
                       else not (proper_interval ao (Just x)) &&
                              (List_Fusion.has_next g2 s2a ||
                                List_Fusion.has_next g1 s1a)));
          });
      });

proper_interval_set_Compl_aux_fusion ::
  forall a b c.
    (Cardinality.Card_UNIV a, Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Set_Impl.Set_impl a) => (a -> a -> Bool) ->
                                (Maybe a -> Maybe a -> Bool) ->
                                  List_Fusion.Generator a b ->
                                    List_Fusion.Generator a c ->
                                      Maybe a -> Arith.Nat -> b -> c -> Bool;
proper_interval_set_Compl_aux_fusion less proper_interval g1 g2 ao n s1 s2 =
  (if List_Fusion.has_next g1 s1
    then (case List_Fusion.next g1 s1 of {
           (x, s1a) ->
             (if List_Fusion.has_next g2 s2
               then (case List_Fusion.next g2 s2 of {
                      (y, s2a) ->
                        (if less x y
                          then proper_interval ao (Just x) ||
                                 proper_interval_set_Compl_aux_fusion less
                                   proper_interval g1 g2 (Just x)
                                   (Arith.plus_nat n Arith.one_nat) s1a s2
                          else (if less y x
                                 then proper_interval ao (Just y) ||
proper_interval_set_Compl_aux_fusion less proper_interval g1 g2 (Just y)
  (Arith.plus_nat n Arith.one_nat) s1 s2a
                                 else proper_interval ao (Just x) &&
let {
  m = Arith.minus_nat
        ((Finite_Set.card :: Set.Set a -> Arith.Nat) (Set.top_set :: Set.Set a))
        n;
} in not (Arith.equal_nat (Arith.minus_nat m (List_Fusion.length_fusion g2 s2a))
           (Arith.nat_of_integer (2 :: Integer))) ||
       not (Arith.equal_nat
             (Arith.minus_nat m (List_Fusion.length_fusion g1 s1a))
             (Arith.nat_of_integer (2 :: Integer)))));
                    })
               else let {
                      m = Arith.minus_nat
                            ((Finite_Set.card :: Set.Set a -> Arith.Nat)
                              (Set.top_set :: Set.Set a))
                            n;
                    } in (case length_last_fusion g1 s1 of {
                           (len_x, xa) ->
                             not (Arith.equal_nat m len_x) &&
                               (if Arith.equal_nat m
                                     (Arith.plus_nat len_x Arith.one_nat)
                                 then not (proper_interval (Just xa) Nothing)
                                 else True);
                         }));
         })
    else (if List_Fusion.has_next g2 s2
           then (case List_Fusion.next g2 s2 of {
                  (_, _) ->
                    let {
                      m = Arith.minus_nat
                            ((Finite_Set.card :: Set.Set a -> Arith.Nat)
                              (Set.top_set :: Set.Set a))
                            n;
                    } in (case length_last_fusion g2 s2 of {
                           (len_y, y) ->
                             not (Arith.equal_nat m len_y) &&
                               (if Arith.equal_nat m
                                     (Arith.plus_nat len_y Arith.one_nat)
                                 then not (proper_interval (Just y) Nothing)
                                 else True);
                         });
                })
           else Arith.less_nat (Arith.plus_nat n Arith.one_nat)
                  ((Finite_Set.card :: Set.Set a -> Arith.Nat)
                    (Set.top_set :: Set.Set a))));

}
