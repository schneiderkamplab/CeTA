{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Collection_Enum(Cenum(..)) where {

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
import qualified Option;
import qualified List;
import qualified Set;
import qualified Collection_Order;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Arith;

cEnum_int ::
  Maybe ([Arith.Int],
          ((Arith.Int -> Bool) -> Bool, (Arith.Int -> Bool) -> Bool));
cEnum_int = Nothing;

class Cenum a where {
  cEnum :: Maybe ([a], ((a -> Bool) -> Bool, (a -> Bool) -> Bool));
};

instance Cenum Arith.Int where {
  cEnum = cEnum_int;
};

cEnum_nat ::
  Maybe ([Arith.Nat],
          ((Arith.Nat -> Bool) -> Bool, (Arith.Nat -> Bool) -> Bool));
cEnum_nat = Nothing;

instance Cenum Arith.Nat where {
  cEnum = cEnum_nat;
};

cEnum_set ::
  forall a.
    (Cenum a, Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Set_Impl.Set_impl a) => Maybe ([Set.Set a],
                                      ((Set.Set a -> Bool) -> Bool,
(Set.Set a -> Bool) -> Bool));
cEnum_set =
  (case cEnum of {
    Nothing -> Nothing;
    Just (enum_a, (_, _)) ->
      Just (map List.set (List.subseqs enum_a),
             ((\ p -> all p (map List.set (List.subseqs enum_a))),
               (\ p -> any p (map List.set (List.subseqs enum_a)))));
  });

instance (Cenum a, Collection_Eq.Ceq a, Collection_Order.Ccompare a,
           Set_Impl.Set_impl a) => Cenum (Set.Set a) where {
  cEnum = cEnum_set;
};

cEnum_list ::
  forall a. Maybe ([[a]], (([a] -> Bool) -> Bool, ([a] -> Bool) -> Bool));
cEnum_list = Nothing;

instance Cenum [a] where {
  cEnum = cEnum_list;
};

cEnum_option ::
  forall a.
    (Cenum a) => Maybe ([Maybe a],
                         ((Maybe a -> Bool) -> Bool,
                           (Maybe a -> Bool) -> Bool));
cEnum_option =
  (case cEnum of {
    Nothing -> Nothing;
    Just (enum_a, (enum_all_a, enum_ex_a)) ->
      Just (Nothing : map Just enum_a,
             ((\ p -> p Nothing && enum_all_a (\ x -> p (Just x))),
               (\ p -> p Nothing || enum_ex_a (\ x -> p (Just x)))));
  });

instance (Cenum a) => Cenum (Maybe a) where {
  cEnum = cEnum_option;
};

cEnum_prod ::
  forall a b.
    (Cenum a,
      Cenum b) => Maybe ([(a, b)],
                          (((a, b) -> Bool) -> Bool, ((a, b) -> Bool) -> Bool));
cEnum_prod =
  (case cEnum of {
    Nothing -> Nothing;
    Just (enum_a, (enum_all_a, enum_ex_a)) ->
      (case cEnum of {
        Nothing -> Nothing;
        Just (enum_b, (enum_all_b, enum_ex_b)) ->
          Just (List.product enum_a enum_b,
                 ((\ p -> enum_all_a (\ x -> enum_all_b (\ y -> p (x, y)))),
                   (\ p -> enum_ex_a (\ x -> enum_ex_b (\ y -> p (x, y))))));
      });
  });

instance (Cenum a, Cenum b) => Cenum (a, b) where {
  cEnum = cEnum_prod;
};

cEnum_integer ::
  Maybe ([Integer], ((Integer -> Bool) -> Bool, (Integer -> Bool) -> Bool));
cEnum_integer = Nothing;

instance Cenum Integer where {
  cEnum = cEnum_integer;
};

}
