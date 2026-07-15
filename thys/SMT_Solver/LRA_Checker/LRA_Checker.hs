{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  LRA_Checker(Num, Char, Term, La_solver_type, Hints, Ty, Sig, Sum, Formula,
               Lin_rel, Lin_constraint, lra_validity_checker,
               example_la_formula)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Uint32;
import qualified Uint64;
import qualified Data_Bits;

newtype Int = Int_of_integer Integer;

integer_of_int :: Int -> Integer;
integer_of_int (Int_of_integer k) = k;

equal_int :: Int -> Int -> Bool;
equal_int k l = integer_of_int k == integer_of_int l;

instance Eq Int where {
  a == b = equal_int a b;
};

newtype Nat = Nat Integer;

integer_of_nat :: Nat -> Integer;
integer_of_nat (Nat x) = x;

equal_nat :: Nat -> Nat -> Bool;
equal_nat m n = integer_of_nat m == integer_of_nat n;

instance Eq Nat where {
  a == b = equal_nat a b;
};

less_eq_nat :: Nat -> Nat -> Bool;
less_eq_nat m n = integer_of_nat m <= integer_of_nat n;

class Ord a where {
  less_eq :: a -> a -> Bool;
  less :: a -> a -> Bool;
};

less_nat :: Nat -> Nat -> Bool;
less_nat m n = integer_of_nat m < integer_of_nat n;

instance Ord Nat where {
  less_eq = less_eq_nat;
  less = less_nat;
};

class (Ord a) => Quasi_order a where {
};

class (Quasi_order a) => Weak_order a where {
};

class (Ord a) => Preorder a where {
};

class (Preorder a, Weak_order a) => Order a where {
};

instance Quasi_order Nat where {
};

instance Weak_order Nat where {
};

instance Preorder Nat where {
};

instance Order Nat where {
};

ceq_nat :: Maybe (Nat -> Nat -> Bool);
ceq_nat = Just equal_nat;

class Ceq a where {
  ceq :: Maybe (a -> a -> Bool);
};

instance Ceq Nat where {
  ceq = ceq_nat;
};

newtype Phantom a b = Phantom b;

data Set_impla = Set_Choose | Set_Collect | Set_DList | Set_RBT | Set_Monada;

set_impl_nat :: Phantom Nat Set_impla;
set_impl_nat = Phantom Set_RBT;

class Set_impl a where {
  set_impl :: Phantom a Set_impla;
};

instance Set_impl Nat where {
  set_impl = set_impl_nat;
};

class (Order a) => Linorder a where {
};

instance Linorder Nat where {
};

data Ordera = Eqa | Lt | Gt;

comparator_of :: forall a. (Eq a, Linorder a) => a -> a -> Ordera;
comparator_of x y = (if less x y then Lt else (if x == y then Eqa else Gt));

compare_nat :: Nat -> Nat -> Ordera;
compare_nat = comparator_of;

ccompare_nat :: Maybe (Nat -> Nat -> Ordera);
ccompare_nat = Just compare_nat;

class Ccompare a where {
  ccompare :: Maybe (a -> a -> Ordera);
};

instance Ccompare Nat where {
  ccompare = ccompare_nat;
};

data Mapping_impla = Mapping_Choose | Mapping_Assoc_List | Mapping_RBT
  | Mapping_Mapping;

mapping_impl_nat :: Phantom Nat Mapping_impla;
mapping_impl_nat = Phantom Mapping_RBT;

class Mapping_impl a where {
  mapping_impl :: Phantom a Mapping_impla;
};

instance Mapping_impl Nat where {
  mapping_impl = mapping_impl_nat;
};

newtype Rat = Frct (Int, Int);

quotient_of :: Rat -> (Int, Int);
quotient_of (Frct x) = x;

equal_rat :: Rat -> Rat -> Bool;
equal_rat a b = quotient_of a == quotient_of b;

instance Eq Rat where {
  a == b = equal_rat a b;
};

times_int :: Int -> Int -> Int;
times_int k l = Int_of_integer (integer_of_int k * integer_of_int l);

apsnd :: forall a b c. (a -> b) -> (c, a) -> (c, b);
apsnd f (x, y) = (x, f y);

data Num = One | Bit0 Num | Bit1 Num;

divmod_integer :: Integer -> Integer -> (Integer, Integer);
divmod_integer k l =
  (if k == (0 :: Integer) then ((0 :: Integer), (0 :: Integer))
    else (if (0 :: Integer) < l
           then (if (0 :: Integer) < k then divMod ( k ) ( l )
                  else (case divMod ( (negate k) ) ( l ) of {
                         (r, s) ->
                           (if s == (0 :: Integer)
                             then (negate r, (0 :: Integer))
                             else (negate r - (1 :: Integer), l - s));
                       }))
           else (if l == (0 :: Integer) then ((0 :: Integer), k)
                  else apsnd negate
                         (if k < (0 :: Integer)
                           then divMod ( (negate k) ) ( (negate l) )
                           else (case divMod ( k ) ( (negate l) ) of {
                                  (r, s) ->
                                    (if s == (0 :: Integer)
                                      then (negate r, (0 :: Integer))
                                      else (negate r - (1 :: Integer),
     negate l - s));
                                })))));

divide_integer :: Integer -> Integer -> Integer;
divide_integer k l = fst (divmod_integer k l);

divide_int :: Int -> Int -> Int;
divide_int k l =
  Int_of_integer (divide_integer (integer_of_int k) (integer_of_int l));

uminus_int :: Int -> Int;
uminus_int k = Int_of_integer (negate (integer_of_int k));

zero_int :: Int;
zero_int = Int_of_integer (0 :: Integer);

less_int :: Int -> Int -> Bool;
less_int k l = integer_of_int k < integer_of_int l;

one_int :: Int;
one_int = Int_of_integer (1 :: Integer);

gcd_int :: Int -> Int -> Int;
gcd_int (Int_of_integer x) (Int_of_integer y) =
  Int_of_integer (Prelude.gcd x y);

normalize :: (Int, Int) -> (Int, Int);
normalize p =
  (if less_int zero_int (snd p)
    then let {
           a = gcd_int (fst p) (snd p);
         } in (divide_int (fst p) a, divide_int (snd p) a)
    else (if equal_int (snd p) zero_int then (zero_int, one_int)
           else let {
                  a = uminus_int (gcd_int (fst p) (snd p));
                } in (divide_int (fst p) a, divide_int (snd p) a)));

times_rat :: Rat -> Rat -> Rat;
times_rat p q =
  Frct (case quotient_of p of {
         (a, c) -> (case quotient_of q of {
                     (b, d) -> normalize (times_int a b, times_int c d);
                   });
       });

class Times a where {
  times :: a -> a -> a;
};

class (Times a) => Dvd a where {
};

instance Times Rat where {
  times = times_rat;
};

instance Dvd Rat where {
};

one_rat :: Rat;
one_rat = Frct (one_int, one_int);

class One a where {
  one :: a;
};

instance One Rat where {
  one = one_rat;
};

uminus_rat :: Rat -> Rat;
uminus_rat p = Frct (case quotient_of p of {
                      (a, b) -> (uminus_int a, b);
                    });

minus_int :: Int -> Int -> Int;
minus_int k l = Int_of_integer (integer_of_int k - integer_of_int l);

minus_rat :: Rat -> Rat -> Rat;
minus_rat p q =
  Frct (case quotient_of p of {
         (a, c) ->
           (case quotient_of q of {
             (b, d) ->
               normalize
                 (minus_int (times_int a d) (times_int b c), times_int c d);
           });
       });

zero_rat :: Rat;
zero_rat = Frct (zero_int, one_int);

plus_int :: Int -> Int -> Int;
plus_int k l = Int_of_integer (integer_of_int k + integer_of_int l);

plus_rat :: Rat -> Rat -> Rat;
plus_rat p q =
  Frct (case quotient_of p of {
         (a, c) ->
           (case quotient_of q of {
             (b, d) ->
               normalize
                 (plus_int (times_int a d) (times_int b c), times_int c d);
           });
       });

class Uminus a where {
  uminus :: a -> a;
};

class Minus a where {
  minus :: a -> a -> a;
};

class Zero a where {
  zeroa :: a;
};

class Plus a where {
  plus :: a -> a -> a;
};

class (Plus a) => Semigroup_add a where {
};

class (Semigroup_add a) => Cancel_semigroup_add a where {
};

class (Semigroup_add a) => Ab_semigroup_add a where {
};

class (Ab_semigroup_add a, Cancel_semigroup_add a,
        Minus a) => Cancel_ab_semigroup_add a where {
};

class (Semigroup_add a, Zero a) => Monoid_add a where {
};

class (Ab_semigroup_add a, Monoid_add a) => Comm_monoid_add a where {
};

class (Cancel_ab_semigroup_add a,
        Comm_monoid_add a) => Cancel_comm_monoid_add a where {
};

class (Times a, Zero a) => Mult_zero a where {
};

class (Times a) => Semigroup_mult a where {
};

class (Ab_semigroup_add a, Semigroup_mult a) => Semiring a where {
};

class (Comm_monoid_add a, Mult_zero a, Semiring a) => Semiring_0 a where {
};

class (Cancel_comm_monoid_add a, Semiring_0 a) => Semiring_0_cancel a where {
};

class (Semigroup_mult a) => Ab_semigroup_mult a where {
};

class (Ab_semigroup_mult a, Semiring a) => Comm_semiring a where {
};

class (Comm_semiring a, Semiring_0 a) => Comm_semiring_0 a where {
};

class (Comm_semiring_0 a,
        Semiring_0_cancel a) => Comm_semiring_0_cancel a where {
};

class (One a, Times a) => Power a where {
};

class (Semigroup_mult a, Power a) => Monoid_mult a where {
};

class (One a, Semigroup_add a) => Numeral a where {
};

class (Monoid_mult a, Numeral a, Semiring a) => Semiring_numeral a where {
};

class (One a, Zero a) => Zero_neq_one a where {
};

class (Semiring_numeral a, Semiring_0 a, Zero_neq_one a) => Semiring_1 a where {
};

class (Semiring_0_cancel a, Semiring_1 a) => Semiring_1_cancel a where {
};

class (Ab_semigroup_mult a, Monoid_mult a, Dvd a) => Comm_monoid_mult a where {
};

class (Comm_monoid_mult a, Comm_semiring_0 a,
        Semiring_1 a) => Comm_semiring_1 a where {
};

class (Comm_semiring_0_cancel a, Comm_semiring_1 a,
        Semiring_1_cancel a) => Comm_semiring_1_cancel a where {
};

class (Comm_semiring_1_cancel a) => Comm_semiring_1_cancel_crossproduct a where {
};

class (Semiring_0 a) => Semiring_no_zero_divisors a where {
};

class (Semiring_1 a,
        Semiring_no_zero_divisors a) => Semiring_1_no_zero_divisors a where {
};

class (Semiring_no_zero_divisors a) => Semiring_no_zero_divisors_cancel a where {
};

class (Cancel_semigroup_add a, Minus a, Monoid_add a,
        Uminus a) => Group_add a where {
};

class (Cancel_comm_monoid_add a, Group_add a) => Ab_group_add a where {
};

class (Ab_group_add a, Semiring_0_cancel a) => Ring a where {
};

class (Ring a,
        Semiring_no_zero_divisors_cancel a) => Ring_no_zero_divisors a where {
};

class (Group_add a, Numeral a) => Neg_numeral a where {
};

class (Neg_numeral a, Ring a, Semiring_1_cancel a) => Ring_1 a where {
};

class (Ring_1 a, Ring_no_zero_divisors a,
        Semiring_1_no_zero_divisors a) => Ring_1_no_zero_divisors a where {
};

class (Comm_semiring_0_cancel a, Ring a) => Comm_ring a where {
};

class (Comm_ring a, Comm_semiring_1_cancel a, Ring_1 a) => Comm_ring_1 a where {
};

class (Comm_semiring_1_cancel a,
        Semiring_1_no_zero_divisors a) => Semidom a where {
};

class (Comm_ring_1 a, Ring_1_no_zero_divisors a, Semidom a,
        Comm_semiring_1_cancel_crossproduct a) => Idom a where {
};

instance Plus Rat where {
  plus = plus_rat;
};

instance Semigroup_add Rat where {
};

instance Cancel_semigroup_add Rat where {
};

instance Ab_semigroup_add Rat where {
};

instance Minus Rat where {
  minus = minus_rat;
};

instance Cancel_ab_semigroup_add Rat where {
};

instance Zero Rat where {
  zeroa = zero_rat;
};

instance Monoid_add Rat where {
};

instance Comm_monoid_add Rat where {
};

instance Cancel_comm_monoid_add Rat where {
};

instance Mult_zero Rat where {
};

instance Semigroup_mult Rat where {
};

instance Semiring Rat where {
};

instance Semiring_0 Rat where {
};

instance Semiring_0_cancel Rat where {
};

instance Ab_semigroup_mult Rat where {
};

instance Comm_semiring Rat where {
};

instance Comm_semiring_0 Rat where {
};

instance Comm_semiring_0_cancel Rat where {
};

instance Power Rat where {
};

instance Monoid_mult Rat where {
};

instance Numeral Rat where {
};

instance Semiring_numeral Rat where {
};

instance Zero_neq_one Rat where {
};

instance Semiring_1 Rat where {
};

instance Semiring_1_cancel Rat where {
};

instance Comm_monoid_mult Rat where {
};

instance Comm_semiring_1 Rat where {
};

instance Comm_semiring_1_cancel Rat where {
};

instance Comm_semiring_1_cancel_crossproduct Rat where {
};

instance Semiring_no_zero_divisors Rat where {
};

instance Semiring_1_no_zero_divisors Rat where {
};

instance Semiring_no_zero_divisors_cancel Rat where {
};

instance Uminus Rat where {
  uminus = uminus_rat;
};

instance Group_add Rat where {
};

instance Ab_group_add Rat where {
};

instance Ring Rat where {
};

instance Ring_no_zero_divisors Rat where {
};

instance Neg_numeral Rat where {
};

instance Ring_1 Rat where {
};

instance Ring_1_no_zero_divisors Rat where {
};

instance Comm_ring Rat where {
};

instance Comm_ring_1 Rat where {
};

instance Semidom Rat where {
};

instance Idom Rat where {
};

sgn_int :: Int -> Int;
sgn_int i =
  (if equal_int i zero_int then zero_int
    else (if less_int zero_int i then one_int else uminus_int one_int));

abs_int :: Int -> Int;
abs_int i = (if less_int i zero_int then uminus_int i else i);

inverse_rat :: Rat -> Rat;
inverse_rat p =
  Frct (case quotient_of p of {
         (a, b) ->
           (if equal_int a zero_int then (zero_int, one_int)
             else (times_int (sgn_int a) b, abs_int a));
       });

divide_rat :: Rat -> Rat -> Rat;
divide_rat p q =
  Frct (case quotient_of p of {
         (a, c) -> (case quotient_of q of {
                     (b, d) -> normalize (times_int a d, times_int c b);
                   });
       });

class Divide a where {
  divide :: a -> a -> a;
};

class (Divide a) => Inverse a where {
  inverse :: a -> a;
};

class (Idom a) => Ufd a where {
};

class (Inverse a, Ring_1_no_zero_divisors a) => Division_ring a where {
};

class (Divide a, Semidom a,
        Semiring_no_zero_divisors_cancel a) => Semidom_divide a where {
};

class (Idom a, Semidom_divide a) => Idom_divide a where {
};

class (Division_ring a, Idom_divide a, Ufd a) => Field a where {
};

instance Ufd Rat where {
};

instance Divide Rat where {
  divide = divide_rat;
};

instance Inverse Rat where {
  inverse = inverse_rat;
};

instance Division_ring Rat where {
};

instance Semidom_divide Rat where {
};

instance Idom_divide Rat where {
};

instance Field Rat where {
};

less_eq_int :: Int -> Int -> Bool;
less_eq_int k l = integer_of_int k <= integer_of_int l;

less_eq_rat :: Rat -> Rat -> Bool;
less_eq_rat p q =
  (case quotient_of p of {
    (a, c) -> (case quotient_of q of {
                (b, d) -> less_eq_int (times_int a d) (times_int c b);
              });
  });

less_rat :: Rat -> Rat -> Bool;
less_rat p q =
  (case quotient_of p of {
    (a, c) -> (case quotient_of q of {
                (b, d) -> less_int (times_int a d) (times_int c b);
              });
  });

instance Ord Rat where {
  less_eq = less_eq_rat;
  less = less_rat;
};

class (Semiring_1 a) => Semiring_char_0 a where {
};

class (Semiring_char_0 a, Ring_1 a) => Ring_char_0 a where {
};

instance Semiring_char_0 Rat where {
};

instance Ring_char_0 Rat where {
};

instance Quasi_order Rat where {
};

instance Weak_order Rat where {
};

instance Preorder Rat where {
};

instance Order Rat where {
};

ceq_rat :: Maybe (Rat -> Rat -> Bool);
ceq_rat = Just equal_rat;

instance Ceq Rat where {
  ceq = ceq_rat;
};

set_impl_rat :: Phantom Rat Set_impla;
set_impl_rat = Phantom Set_RBT;

instance Set_impl Rat where {
  set_impl = set_impl_rat;
};

instance Linorder Rat where {
};

class (Field a, Ring_char_0 a) => Field_char_0 a where {
};

instance Field_char_0 Rat where {
};

modulo_integer :: Integer -> Integer -> Integer;
modulo_integer k l = snd (divmod_integer k l);

modulo_nat :: Nat -> Nat -> Nat;
modulo_nat m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));

divide_nat :: Nat -> Nat -> Nat;
divide_nat m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));

max :: forall a. (Ord a) => a -> a -> a;
max a b = (if less_eq a b then b else a);

instance Ord Integer where {
  less_eq = (\ a b -> a <= b);
  less = (\ a b -> a < b);
};

nat_of_integer :: Integer -> Nat;
nat_of_integer k = Nat (max (0 :: Integer) k);

newtype Char = Chr Integer;

char_of_integer :: Integer -> Char;
char_of_integer k =
  Chr (if (0 :: Integer) <= k && k < (256 :: Integer) then k
        else modulo_integer k (256 :: Integer));

integer_of_char :: Char -> Integer;
integer_of_char (Chr x) = x;

implode :: [Char] -> String;
implode cs =
  map (let chr k | (0 <= k && k < 128) = Prelude.toEnum k :: Prelude.Char in chr . Prelude.fromInteger)
    (map integer_of_char cs);

lit_of_digit :: Nat -> String;
lit_of_digit n = implode [char_of_integer ((48 :: Integer) + integer_of_nat n)];

showsl_lit :: String -> String -> String;
showsl_lit = (\ a b -> a ++ b);

showsl_nat :: Nat -> String -> String;
showsl_nat n =
  (if less_nat n (nat_of_integer (10 :: Integer))
    then showsl_lit (lit_of_digit n)
    else showsl_nat (divide_nat n (nat_of_integer (10 :: Integer))) .
           showsl_lit
             (lit_of_digit (modulo_nat n (nat_of_integer (10 :: Integer)))));

nat :: Int -> Nat;
nat k = Nat (max (0 :: Integer) (integer_of_int k));

showsl_int :: Int -> String -> String;
showsl_int i =
  (if less_int i zero_int then showsl_lit "-" . showsl_nat (nat (uminus_int i))
    else showsl_nat (nat i));

showsl_rat :: Rat -> String -> String;
showsl_rat x =
  (case quotient_of x of {
    (d, n) ->
      (if equal_int n one_int then showsl_int d
        else (showsl_int d . showsl_lit "/") . showsl_int n);
  });

showsl_sep ::
  forall a.
    (a -> String -> String) -> (String -> String) -> [a] -> String -> String;
showsl_sep s sep [] = showsl_lit "";
showsl_sep s sep [x] = s x;
showsl_sep s sep (x : v : va) = (s x . sep) . showsl_sep s sep (v : va);

showsl_list_gen ::
  forall a.
    (a -> String -> String) ->
      String -> String -> String -> String -> [a] -> String -> String;
showsl_list_gen showslx e l s r xs =
  (if null xs then showsl_lit e
    else (showsl_lit l . showsl_sep showslx (showsl_lit s) xs) . showsl_lit r);

default_showsl_list ::
  forall a. (a -> String -> String) -> [a] -> String -> String;
default_showsl_list sl = showsl_list_gen sl "[]" "[" ", " "]";

showsl_list_rat :: [Rat] -> String -> String;
showsl_list_rat xs = default_showsl_list showsl_rat xs;

class Showl a where {
  showsl :: a -> String -> String;
  showsl_list :: [a] -> String -> String;
};

instance Showl Rat where {
  showsl = showsl_rat;
  showsl_list = showsl_list_rat;
};

compare_rat :: Rat -> Rat -> Ordera;
compare_rat = comparator_of;

ccompare_rat :: Maybe (Rat -> Rat -> Ordera);
ccompare_rat = Just compare_rat;

instance Ccompare Rat where {
  ccompare = ccompare_rat;
};

less_eq_list :: forall a. (Eq a, Order a) => [a] -> [a] -> Bool;
less_eq_list (x : xs) (y : ys) = less x y || x == y && less_eq_list xs ys;
less_eq_list [] xs = True;
less_eq_list (x : xs) [] = False;

less_list :: forall a. (Eq a, Order a) => [a] -> [a] -> Bool;
less_list (x : xs) (y : ys) = less x y || x == y && less_list xs ys;
less_list [] (x : xs) = True;
less_list xs [] = False;

instance (Eq a, Order a) => Ord [a] where {
  less_eq = less_eq_list;
  less = less_list;
};

instance (Eq a, Order a) => Quasi_order [a] where {
};

instance (Eq a, Order a) => Weak_order [a] where {
};

instance (Eq a, Order a) => Preorder [a] where {
};

instance (Eq a, Order a) => Order [a] where {
};

instance (Eq a, Linorder a) => Linorder [a] where {
};

showsl_lista :: forall a. (Showl a) => [a] -> String -> String;
showsl_lista xs = showsl_list xs;

showsl_list_list :: forall a. (Showl a) => [[a]] -> String -> String;
showsl_list_list xs = default_showsl_list showsl_lista xs;

instance (Showl a) => Showl [a] where {
  showsl = showsl_lista;
  showsl_list = showsl_list_list;
};

comparator_list :: forall a. (a -> a -> Ordera) -> [a] -> [a] -> Ordera;
comparator_list comp_a (x : xa) (y : ya) =
  (case comp_a x y of {
    Eqa -> comparator_list comp_a xa ya;
    Lt -> Lt;
    Gt -> Gt;
  });
comparator_list comp_a (x : xa) [] = Gt;
comparator_list comp_a [] (y : ya) = Lt;
comparator_list comp_a [] [] = Eqa;

ccompare_list :: forall a. (Ccompare a) => Maybe ([a] -> [a] -> Ordera);
ccompare_list = (case ccompare of {
                  Nothing -> Nothing;
                  Just comp_a -> Just (comparator_list comp_a);
                });

instance (Ccompare a) => Ccompare [a] where {
  ccompare = ccompare_list;
};

mapping_impl_list :: forall a. Phantom [a] Mapping_impla;
mapping_impl_list = Phantom Mapping_Choose;

instance Mapping_impl [a] where {
  mapping_impl = mapping_impl_list;
};

data Term a b = Var b | Fun a [Term a b];

instance (Eq a, Eq b) => Eq (Term a b) where {
  a == b = equal_term a b;
};

equal_term :: forall a b. (Eq a, Eq b) => Term a b -> Term a b -> Bool;
equal_term (Var x1) (Fun x21 x22) = False;
equal_term (Fun x21 x22) (Var x1) = False;
equal_term (Fun x21 x22) (Fun y21 y22) = x21 == y21 && x22 == y22;
equal_term (Var x1) (Var y1) = x1 == y1;

equal_char :: Char -> Char -> Bool;
equal_char c d = integer_of_char c == integer_of_char d;

instance Eq Char where {
  a == b = equal_char a b;
};

less_eq_char :: Char -> Char -> Bool;
less_eq_char c d = integer_of_char c <= integer_of_char d;

less_char :: Char -> Char -> Bool;
less_char c d = integer_of_char c < integer_of_char d;

instance Ord Char where {
  less_eq = less_eq_char;
  less = less_char;
};

instance Quasi_order Char where {
};

instance Weak_order Char where {
};

instance Preorder Char where {
};

instance Order Char where {
};

instance Linorder Char where {
};

showsl_list_char :: [Char] -> String -> String;
showsl_list_char cs s = showsl_lit (implode cs) s;

showsl_char :: Char -> String -> String;
showsl_char c = showsl_lit (implode [c]);

instance Showl Char where {
  showsl = showsl_char;
  showsl_list = showsl_list_char;
};

compare_char :: Char -> Char -> Ordera;
compare_char = comparator_of;

ccompare_char :: Maybe (Char -> Char -> Ordera);
ccompare_char = Just compare_char;

instance Ccompare Char where {
  ccompare = ccompare_char;
};

data Atom a = Leq Nat a | Geq Nat a;

equal_atom :: forall a. (Eq a) => Atom a -> Atom a -> Bool;
equal_atom (Leq x11 x12) (Geq x21 x22) = False;
equal_atom (Geq x21 x22) (Leq x11 x12) = False;
equal_atom (Geq x21 x22) (Geq y21 y22) = equal_nat x21 y21 && x22 == y22;
equal_atom (Leq x11 x12) (Leq y11 y12) = equal_nat x11 y11 && x12 == y12;

ceq_atom :: forall a. (Eq a) => Maybe (Atom a -> Atom a -> Bool);
ceq_atom = Just equal_atom;

instance (Eq a) => Ceq (Atom a) where {
  ceq = ceq_atom;
};

set_impl_atom :: forall a. Phantom (Atom a) Set_impla;
set_impl_atom = Phantom Set_RBT;

instance Set_impl (Atom a) where {
  set_impl = set_impl_atom;
};

comparator_atom :: forall a. (a -> a -> Ordera) -> Atom a -> Atom a -> Ordera;
comparator_atom comp_a (Geq x xa) (Geq yb yc) = (case comparator_of x yb of {
          Eqa -> comp_a xa yc;
          Lt -> Lt;
          Gt -> Gt;
        });
comparator_atom comp_a (Geq x xa) (Leq y ya) = Gt;
comparator_atom comp_a (Leq x xa) (Geq yb yc) = Lt;
comparator_atom comp_a (Leq x xa) (Leq y ya) = (case comparator_of x y of {
         Eqa -> comp_a xa ya;
         Lt -> Lt;
         Gt -> Gt;
       });

class Compare a where {
  compare :: a -> a -> Ordera;
};

compare_atom :: forall a. (Compare a) => Atom a -> Atom a -> Ordera;
compare_atom = comparator_atom compare;

ccompare_atom :: forall a. (Compare a) => Maybe (Atom a -> Atom a -> Ordera);
ccompare_atom = Just compare_atom;

instance (Compare a) => Ccompare (Atom a) where {
  ccompare = ccompare_atom;
};

data QDelta = QDelta Rat Rat;

equal_QDelta :: QDelta -> QDelta -> Bool;
equal_QDelta (QDelta x1 x2) (QDelta y1 y2) = equal_rat x1 y1 && equal_rat x2 y2;

instance Eq QDelta where {
  a == b = equal_QDelta a b;
};

one_QDelta :: QDelta;
one_QDelta = QDelta one_rat zero_rat;

instance One QDelta where {
  one = one_QDelta;
};

qdsnd :: QDelta -> Rat;
qdsnd (QDelta a b) = b;

qdfst :: QDelta -> Rat;
qdfst (QDelta a b) = a;

plus_QDelta :: QDelta -> QDelta -> QDelta;
plus_QDelta qd1 qd2 =
  QDelta (plus_rat (qdfst qd1) (qdfst qd2)) (plus_rat (qdsnd qd1) (qdsnd qd2));

instance Plus QDelta where {
  plus = plus_QDelta;
};

zero_QDelta :: QDelta;
zero_QDelta = QDelta zero_rat zero_rat;

instance Zero QDelta where {
  zeroa = zero_QDelta;
};

minus_QDelta :: QDelta -> QDelta -> QDelta;
minus_QDelta qd1 qd2 =
  QDelta (minus_rat (qdfst qd1) (qdfst qd2))
    (minus_rat (qdsnd qd1) (qdsnd qd2));

instance Minus QDelta where {
  minus = minus_QDelta;
};

uminus_QDelta :: QDelta -> QDelta;
uminus_QDelta qd = QDelta (uminus_rat (qdfst qd)) (uminus_rat (qdsnd qd));

instance Uminus QDelta where {
  uminus = uminus_QDelta;
};

less_eq_QDelta :: QDelta -> QDelta -> Bool;
less_eq_QDelta qd1 qd2 =
  less_rat (qdfst qd1) (qdfst qd2) ||
    equal_rat (qdfst qd1) (qdfst qd2) && less_eq_rat (qdsnd qd1) (qdsnd qd2);

less_QDelta :: QDelta -> QDelta -> Bool;
less_QDelta qd1 qd2 =
  less_rat (qdfst qd1) (qdfst qd2) ||
    equal_rat (qdfst qd1) (qdfst qd2) && less_rat (qdsnd qd1) (qdsnd qd2);

instance Ord QDelta where {
  less_eq = less_eq_QDelta;
  less = less_QDelta;
};

instance Quasi_order QDelta where {
};

instance Weak_order QDelta where {
};

instance Preorder QDelta where {
};

instance Order QDelta where {
};

instance Linorder QDelta where {
};

compare_QDelta :: QDelta -> QDelta -> Ordera;
compare_QDelta = comparator_of;

instance Compare QDelta where {
  compare = compare_QDelta;
};

instance Semigroup_add QDelta where {
};

instance Cancel_semigroup_add QDelta where {
};

instance Monoid_add QDelta where {
};

instance Group_add QDelta where {
};

instance Ab_semigroup_add QDelta where {
};

instance Cancel_ab_semigroup_add QDelta where {
};

instance Comm_monoid_add QDelta where {
};

instance Cancel_comm_monoid_add QDelta where {
};

instance Ab_group_add QDelta where {
};

scaleRat_QDelta :: Rat -> QDelta -> QDelta;
scaleRat_QDelta r qd = QDelta (times_rat r (qdfst qd)) (times_rat r (qdsnd qd));

class ScaleRat a where {
  scaleRat :: Rat -> a -> a;
};

class (Ab_group_add a, ScaleRat a) => Rational_vector a where {
};

class (Order a, Rational_vector a) => Ordered_rational_vector a where {
};

class (Ab_semigroup_add a, Order a) => Ordered_ab_semigroup_add a where {
};

class (Ordered_ab_semigroup_add a, Linorder a,
        Ordered_rational_vector a) => Linordered_rational_vector a where {
};

class (One a, Linordered_rational_vector a) => Lrv a where {
};

instance ScaleRat QDelta where {
  scaleRat = scaleRat_QDelta;
};

instance Rational_vector QDelta where {
};

instance Ordered_rational_vector QDelta where {
};

instance Ordered_ab_semigroup_add QDelta where {
};

instance Linordered_rational_vector QDelta where {
};

instance Lrv QDelta where {
};

data La_solver_type = Simplex_Solver;

newtype Hints = LA_Solver La_solver_type;

default_hints :: Hints;
default_hints = LA_Solver Simplex_Solver;

class Default a where {
  defaulta :: a;
};

instance Default Hints where {
  defaulta = default_hints;
};

showsl_hints :: Hints -> String -> String;
showsl_hints (LA_Solver Simplex_Solver) = showsl_lit "Simplex";

showsl_list_hints :: [Hints] -> String -> String;
showsl_list_hints xs = default_showsl_list showsl_hints xs;

instance Showl Hints where {
  showsl = showsl_hints;
  showsl_list = showsl_list_hints;
};

newtype Monom a = Abs_monom [(a, Nat)];

rep_monom :: forall a. (Linorder a) => Monom a -> [(a, Nat)];
rep_monom (Abs_monom x) = x;

equal_monom :: forall a. (Eq a, Linorder a) => Monom a -> Monom a -> Bool;
equal_monom xa xc = rep_monom xa == rep_monom xc;

instance (Eq a, Linorder a) => Eq (Monom a) where {
  a == b = equal_monom a b;
};

equality_prod ::
  forall a b. (a -> a -> Bool) -> (b -> b -> Bool) -> (a, b) -> (a, b) -> Bool;
equality_prod eq_a eq_b (x, xa) (y, ya) = eq_a x y && eq_b xa ya;

ceq_prod :: forall a b. (Ceq a, Ceq b) => Maybe ((a, b) -> (a, b) -> Bool);
ceq_prod = (case ceq of {
             Nothing -> Nothing;
             Just eq_a -> (case ceq of {
                            Nothing -> Nothing;
                            Just eq_b -> Just (equality_prod eq_a eq_b);
                          });
           });

instance (Ceq a, Ceq b) => Ceq (a, b) where {
  ceq = ceq_prod;
};

of_phantom :: forall a b. Phantom a b -> b;
of_phantom (Phantom x) = x;

set_impl_choose2 :: Set_impla -> Set_impla -> Set_impla;
set_impl_choose2 Set_Monada Set_Monada = Set_Monada;
set_impl_choose2 Set_RBT Set_RBT = Set_RBT;
set_impl_choose2 Set_DList Set_DList = Set_DList;
set_impl_choose2 Set_Collect Set_Collect = Set_Collect;
set_impl_choose2 x y = Set_Choose;

set_impl_prod ::
  forall a b. (Set_impl a, Set_impl b) => Phantom (a, b) Set_impla;
set_impl_prod =
  Phantom
    (set_impl_choose2 (of_phantom (set_impl :: Phantom a Set_impla))
      (of_phantom (set_impl :: Phantom b Set_impla)));

instance (Set_impl a, Set_impl b) => Set_impl (a, b) where {
  set_impl = set_impl_prod;
};

comparator_prod ::
  forall a b.
    (a -> a -> Ordera) -> (b -> b -> Ordera) -> (a, b) -> (a, b) -> Ordera;
comparator_prod comp_a comp_b (x, xa) (y, ya) = (case comp_a x y of {
          Eqa -> comp_b xa ya;
          Lt -> Lt;
          Gt -> Gt;
        });

ccompare_prod ::
  forall a b. (Ccompare a, Ccompare b) => Maybe ((a, b) -> (a, b) -> Ordera);
ccompare_prod =
  (case ccompare of {
    Nothing -> Nothing;
    Just comp_a -> (case ccompare of {
                     Nothing -> Nothing;
                     Just comp_b -> Just (comparator_prod comp_a comp_b);
                   });
  });

instance (Ccompare a, Ccompare b) => Ccompare (a, b) where {
  ccompare = ccompare_prod;
};

rel_option :: forall a b. (a -> b -> Bool) -> Maybe a -> Maybe b -> Bool;
rel_option r Nothing (Just y2) = False;
rel_option r (Just y2) Nothing = False;
rel_option r Nothing Nothing = True;
rel_option r (Just x2) (Just y2) = r x2 y2;

newtype Fmap a b = Fmap_of_list [(a, b)];

map_of :: forall a b. (Eq a) => [(a, b)] -> a -> Maybe b;
map_of ((l, v) : ps) k = (if l == k then Just v else map_of ps k);
map_of [] k = Nothing;

fmlookup :: forall a b. (Eq a) => Fmap a b -> a -> Maybe b;
fmlookup (Fmap_of_list m) = map_of m;

data Color = R | B;

data Rbt a b = Empty | Branch Color (Rbt a b) a b (Rbt a b);

newtype Mapping_rbt b a = Mapping_RBTa (Rbt b a);

newtype Set_dlist a = Abs_dlist [a];

data Set a = Collect_set (a -> Bool) | DList_set (Set_dlist a)
  | RBT_set (Mapping_rbt a ()) | Set_Monad [a] | Complement (Set a);

newtype Fset a = Abs_fset (Set a);

emptyc :: forall a b. (Ccompare a) => Mapping_rbt a b;
emptyc = Mapping_RBTa Empty;

emptyb :: forall a. (Ceq a) => Set_dlist a;
emptyb = Abs_dlist [];

set_empty_choose :: forall a. (Ceq a, Ccompare a) => Set a;
set_empty_choose = (case (ccompare :: Maybe (a -> a -> Ordera)) of {
                     Nothing -> (case (ceq :: Maybe (a -> a -> Bool)) of {
                                  Nothing -> Set_Monad [];
                                  Just _ -> DList_set emptyb;
                                });
                     Just _ -> RBT_set emptyc;
                   });

set_empty :: forall a. (Ceq a, Ccompare a) => Set_impla -> Set a;
set_empty Set_Choose = set_empty_choose;
set_empty Set_Monada = Set_Monad [];
set_empty Set_RBT = RBT_set emptyc;
set_empty Set_DList = DList_set emptyb;
set_empty Set_Collect = Collect_set (\ _ -> False);

fun_upda :: forall a b. (a -> a -> Bool) -> (a -> b) -> a -> b -> a -> b;
fun_upda equal f aa b a = (if equal aa a then b else f a);

balance :: forall a b. Rbt a b -> a -> b -> Rbt a b -> Rbt a b;
balance (Branch R a w x b) s t (Branch R c y z d) =
  Branch R (Branch B a w x b) s t (Branch B c y z d);
balance (Branch R (Branch R a w x b) s t c) y z Empty =
  Branch R (Branch B a w x b) s t (Branch B c y z Empty);
balance (Branch R (Branch R a w x b) s t c) y z (Branch B va vb vc vd) =
  Branch R (Branch B a w x b) s t (Branch B c y z (Branch B va vb vc vd));
balance (Branch R Empty w x (Branch R b s t c)) y z Empty =
  Branch R (Branch B Empty w x b) s t (Branch B c y z Empty);
balance (Branch R (Branch B va vb vc vd) w x (Branch R b s t c)) y z Empty =
  Branch R (Branch B (Branch B va vb vc vd) w x b) s t (Branch B c y z Empty);
balance (Branch R Empty w x (Branch R b s t c)) y z (Branch B va vb vc vd) =
  Branch R (Branch B Empty w x b) s t (Branch B c y z (Branch B va vb vc vd));
balance (Branch R (Branch B ve vf vg vh) w x (Branch R b s t c)) y z
  (Branch B va vb vc vd) =
  Branch R (Branch B (Branch B ve vf vg vh) w x b) s t
    (Branch B c y z (Branch B va vb vc vd));
balance Empty w x (Branch R b s t (Branch R c y z d)) =
  Branch R (Branch B Empty w x b) s t (Branch B c y z d);
balance (Branch B va vb vc vd) w x (Branch R b s t (Branch R c y z d)) =
  Branch R (Branch B (Branch B va vb vc vd) w x b) s t (Branch B c y z d);
balance Empty w x (Branch R (Branch R b s t c) y z Empty) =
  Branch R (Branch B Empty w x b) s t (Branch B c y z Empty);
balance Empty w x (Branch R (Branch R b s t c) y z (Branch B va vb vc vd)) =
  Branch R (Branch B Empty w x b) s t (Branch B c y z (Branch B va vb vc vd));
balance (Branch B va vb vc vd) w x (Branch R (Branch R b s t c) y z Empty) =
  Branch R (Branch B (Branch B va vb vc vd) w x b) s t (Branch B c y z Empty);
balance (Branch B va vb vc vd) w x
  (Branch R (Branch R b s t c) y z (Branch B ve vf vg vh)) =
  Branch R (Branch B (Branch B va vb vc vd) w x b) s t
    (Branch B c y z (Branch B ve vf vg vh));
balance Empty s t Empty = Branch B Empty s t Empty;
balance Empty s t (Branch B va vb vc vd) =
  Branch B Empty s t (Branch B va vb vc vd);
balance Empty s t (Branch v Empty vb vc Empty) =
  Branch B Empty s t (Branch v Empty vb vc Empty);
balance Empty s t (Branch v (Branch B ve vf vg vh) vb vc Empty) =
  Branch B Empty s t (Branch v (Branch B ve vf vg vh) vb vc Empty);
balance Empty s t (Branch v Empty vb vc (Branch B vf vg vh vi)) =
  Branch B Empty s t (Branch v Empty vb vc (Branch B vf vg vh vi));
balance Empty s t (Branch v (Branch B ve vj vk vl) vb vc (Branch B vf vg vh vi))
  = Branch B Empty s t
      (Branch v (Branch B ve vj vk vl) vb vc (Branch B vf vg vh vi));
balance (Branch B va vb vc vd) s t Empty =
  Branch B (Branch B va vb vc vd) s t Empty;
balance (Branch B va vb vc vd) s t (Branch B ve vf vg vh) =
  Branch B (Branch B va vb vc vd) s t (Branch B ve vf vg vh);
balance (Branch B va vb vc vd) s t (Branch v Empty vf vg Empty) =
  Branch B (Branch B va vb vc vd) s t (Branch v Empty vf vg Empty);
balance (Branch B va vb vc vd) s t (Branch v (Branch B vi vj vk vl) vf vg Empty)
  = Branch B (Branch B va vb vc vd) s t
      (Branch v (Branch B vi vj vk vl) vf vg Empty);
balance (Branch B va vb vc vd) s t (Branch v Empty vf vg (Branch B vj vk vl vm))
  = Branch B (Branch B va vb vc vd) s t
      (Branch v Empty vf vg (Branch B vj vk vl vm));
balance (Branch B va vb vc vd) s t
  (Branch v (Branch B vi vn vo vp) vf vg (Branch B vj vk vl vm)) =
  Branch B (Branch B va vb vc vd) s t
    (Branch v (Branch B vi vn vo vp) vf vg (Branch B vj vk vl vm));
balance (Branch v Empty vb vc Empty) s t Empty =
  Branch B (Branch v Empty vb vc Empty) s t Empty;
balance (Branch v Empty vb vc (Branch B ve vf vg vh)) s t Empty =
  Branch B (Branch v Empty vb vc (Branch B ve vf vg vh)) s t Empty;
balance (Branch v (Branch B vf vg vh vi) vb vc Empty) s t Empty =
  Branch B (Branch v (Branch B vf vg vh vi) vb vc Empty) s t Empty;
balance (Branch v (Branch B vf vg vh vi) vb vc (Branch B ve vj vk vl)) s t Empty
  = Branch B (Branch v (Branch B vf vg vh vi) vb vc (Branch B ve vj vk vl)) s t
      Empty;
balance (Branch v Empty vf vg Empty) s t (Branch B va vb vc vd) =
  Branch B (Branch v Empty vf vg Empty) s t (Branch B va vb vc vd);
balance (Branch v Empty vf vg (Branch B vi vj vk vl)) s t (Branch B va vb vc vd)
  = Branch B (Branch v Empty vf vg (Branch B vi vj vk vl)) s t
      (Branch B va vb vc vd);
balance (Branch v (Branch B vj vk vl vm) vf vg Empty) s t (Branch B va vb vc vd)
  = Branch B (Branch v (Branch B vj vk vl vm) vf vg Empty) s t
      (Branch B va vb vc vd);
balance (Branch v (Branch B vj vk vl vm) vf vg (Branch B vi vn vo vp)) s t
  (Branch B va vb vc vd) =
  Branch B (Branch v (Branch B vj vk vl vm) vf vg (Branch B vi vn vo vp)) s t
    (Branch B va vb vc vd);

rbt_comp_ins ::
  forall a b.
    (a -> a -> Ordera) -> (a -> b -> b -> b) -> a -> b -> Rbt a b -> Rbt a b;
rbt_comp_ins c f k v Empty = Branch R Empty k v Empty;
rbt_comp_ins c f k v (Branch B l x y r) =
  (case c k x of {
    Eqa -> Branch B l x (f k y v) r;
    Lt -> balance (rbt_comp_ins c f k v l) x y r;
    Gt -> balance l x y (rbt_comp_ins c f k v r);
  });
rbt_comp_ins c f k v (Branch R l x y r) =
  (case c k x of {
    Eqa -> Branch R l x (f k y v) r;
    Lt -> Branch R (rbt_comp_ins c f k v l) x y r;
    Gt -> Branch R l x y (rbt_comp_ins c f k v r);
  });

paint :: forall a b. Color -> Rbt a b -> Rbt a b;
paint c Empty = Empty;
paint c (Branch uu l k v r) = Branch c l k v r;

rbt_comp_insert_with_key ::
  forall a b.
    (a -> a -> Ordera) -> (a -> b -> b -> b) -> a -> b -> Rbt a b -> Rbt a b;
rbt_comp_insert_with_key c f k v t = paint B (rbt_comp_ins c f k v t);

rbt_comp_insert ::
  forall a b. (a -> a -> Ordera) -> a -> b -> Rbt a b -> Rbt a b;
rbt_comp_insert c = rbt_comp_insert_with_key c (\ _ _ nv -> nv);

impl_ofa :: forall b a. (Ccompare b) => Mapping_rbt b a -> Rbt b a;
impl_ofa (Mapping_RBTa x) = x;

the :: forall a. Maybe a -> a;
the (Just x2) = x2;

insertb ::
  forall a b. (Ccompare a) => a -> b -> Mapping_rbt a b -> Mapping_rbt a b;
insertb xc xd xe =
  Mapping_RBTa (rbt_comp_insert (the ccompare) xc xd (impl_ofa xe));

list_of_dlist :: forall a. (Ceq a) => Set_dlist a -> [a];
list_of_dlist (Abs_dlist x) = x;

list_member :: forall a. (a -> a -> Bool) -> [a] -> a -> Bool;
list_member equal (x : xs) y = equal x y || list_member equal xs y;
list_member equal [] y = False;

list_insert :: forall a. (a -> a -> Bool) -> a -> [a] -> [a];
list_insert equal x xs = (if list_member equal xs x then xs else x : xs);

inserta :: forall a. (Ceq a) => a -> Set_dlist a -> Set_dlist a;
inserta xb xc = Abs_dlist (list_insert (the ceq) xb (list_of_dlist xc));

balance_right :: forall a b. Rbt a b -> a -> b -> Rbt a b -> Rbt a b;
balance_right a k x (Branch R b s y c) = Branch R a k x (Branch B b s y c);
balance_right (Branch B a k x b) s y Empty =
  balance (Branch R a k x b) s y Empty;
balance_right (Branch B a k x b) s y (Branch B va vb vc vd) =
  balance (Branch R a k x b) s y (Branch B va vb vc vd);
balance_right (Branch R a k x (Branch B b s y c)) t z Empty =
  Branch R (balance (paint R a) k x b) s y (Branch B c t z Empty);
balance_right (Branch R a k x (Branch B b s y c)) t z (Branch B va vb vc vd) =
  Branch R (balance (paint R a) k x b) s y
    (Branch B c t z (Branch B va vb vc vd));
balance_right Empty k x Empty = Empty;
balance_right (Branch R va vb vc Empty) k x Empty = Empty;
balance_right (Branch R va vb vc (Branch R ve vf vg vh)) k x Empty = Empty;
balance_right Empty k x (Branch B va vb vc vd) = Empty;
balance_right (Branch R ve vf vg Empty) k x (Branch B va vb vc vd) = Empty;
balance_right (Branch R ve vf vg (Branch R vi vj vk vl)) k x
  (Branch B va vb vc vd) = Empty;

balance_left :: forall a b. Rbt a b -> a -> b -> Rbt a b -> Rbt a b;
balance_left (Branch R a k x b) s y c = Branch R (Branch B a k x b) s y c;
balance_left Empty k x (Branch B a s y b) =
  balance Empty k x (Branch R a s y b);
balance_left (Branch B va vb vc vd) k x (Branch B a s y b) =
  balance (Branch B va vb vc vd) k x (Branch R a s y b);
balance_left Empty k x (Branch R (Branch B a s y b) t z c) =
  Branch R (Branch B Empty k x a) s y (balance b t z (paint R c));
balance_left (Branch B va vb vc vd) k x (Branch R (Branch B a s y b) t z c) =
  Branch R (Branch B (Branch B va vb vc vd) k x a) s y
    (balance b t z (paint R c));
balance_left Empty k x Empty = Empty;
balance_left Empty k x (Branch R Empty vb vc vd) = Empty;
balance_left Empty k x (Branch R (Branch R ve vf vg vh) vb vc vd) = Empty;
balance_left (Branch B va vb vc vd) k x Empty = Empty;
balance_left (Branch B va vb vc vd) k x (Branch R Empty vf vg vh) = Empty;
balance_left (Branch B va vb vc vd) k x
  (Branch R (Branch R vi vj vk vl) vf vg vh) = Empty;

combine :: forall a b. Rbt a b -> Rbt a b -> Rbt a b;
combine Empty x = x;
combine (Branch v va vb vc vd) Empty = Branch v va vb vc vd;
combine (Branch R a k x b) (Branch R c s y d) =
  (case combine b c of {
    Empty -> Branch R a k x (Branch R Empty s y d);
    Branch R b2 t z c2 -> Branch R (Branch R a k x b2) t z (Branch R c2 s y d);
    Branch B b2 t z c2 -> Branch R a k x (Branch R (Branch B b2 t z c2) s y d);
  });
combine (Branch B a k x b) (Branch B c s y d) =
  (case combine b c of {
    Empty -> balance_left a k x (Branch B Empty s y d);
    Branch R b2 t z c2 -> Branch R (Branch B a k x b2) t z (Branch B c2 s y d);
    Branch B b2 t z c2 ->
      balance_left a k x (Branch B (Branch B b2 t z c2) s y d);
  });
combine (Branch B va vb vc vd) (Branch R b k x c) =
  Branch R (combine (Branch B va vb vc vd) b) k x c;
combine (Branch R a k x b) (Branch B va vb vc vd) =
  Branch R a k x (combine b (Branch B va vb vc vd));

rbt_comp_del :: forall a b. (a -> a -> Ordera) -> a -> Rbt a b -> Rbt a b;
rbt_comp_del c x Empty = Empty;
rbt_comp_del c x (Branch uu a y s b) =
  (case c x y of {
    Eqa -> combine a b;
    Lt -> rbt_comp_del_from_left c x a y s b;
    Gt -> rbt_comp_del_from_right c x a y s b;
  });

rbt_comp_del_from_left ::
  forall a b.
    (a -> a -> Ordera) -> a -> Rbt a b -> a -> b -> Rbt a b -> Rbt a b;
rbt_comp_del_from_left c x (Branch B lt z v rt) y s b =
  balance_left (rbt_comp_del c x (Branch B lt z v rt)) y s b;
rbt_comp_del_from_left c x Empty y s b =
  Branch R (rbt_comp_del c x Empty) y s b;
rbt_comp_del_from_left c x (Branch R va vb vc vd) y s b =
  Branch R (rbt_comp_del c x (Branch R va vb vc vd)) y s b;

rbt_comp_del_from_right ::
  forall a b.
    (a -> a -> Ordera) -> a -> Rbt a b -> a -> b -> Rbt a b -> Rbt a b;
rbt_comp_del_from_right c x a y s (Branch B lt z v rt) =
  balance_right a y s (rbt_comp_del c x (Branch B lt z v rt));
rbt_comp_del_from_right c x a y s Empty =
  Branch R a y s (rbt_comp_del c x Empty);
rbt_comp_del_from_right c x a y s (Branch R va vb vc vd) =
  Branch R a y s (rbt_comp_del c x (Branch R va vb vc vd));

rbt_comp_delete :: forall a b. (a -> a -> Ordera) -> a -> Rbt a b -> Rbt a b;
rbt_comp_delete c k t = paint B (rbt_comp_del c k t);

delete :: forall a b. (Ccompare a) => a -> Mapping_rbt a b -> Mapping_rbt a b;
delete xb xc = Mapping_RBTa (rbt_comp_delete (the ccompare) xb (impl_ofa xc));

list_remove1 :: forall a. (a -> a -> Bool) -> a -> [a] -> [a];
list_remove1 equal x (y : xs) =
  (if equal x y then xs else y : list_remove1 equal x xs);
list_remove1 equal x [] = [];

removea :: forall a. (Ceq a) => a -> Set_dlist a -> Set_dlist a;
removea xb xc = Abs_dlist (list_remove1 (the ceq) xb (list_of_dlist xc));

insert :: forall a. (Ceq a, Ccompare a) => a -> Set a -> Set a;
insert xa (Complement x) = Complement (remove xa x);
insert x (RBT_set rbt) =
  (case (ccompare :: Maybe (a -> a -> Ordera)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "insert RBT_set: ccompare = None" (\ _ -> insert x (RBT_set rbt));
    Just _ -> RBT_set (insertb x () rbt);
  });
insert x (DList_set dxs) =
  (case (ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "insert DList_set: ceq = None" (\ _ -> insert x (DList_set dxs));
    Just _ -> DList_set (inserta x dxs);
  });
insert x (Set_Monad xs) = Set_Monad (x : xs);
insert x (Collect_set a) =
  (case ceq of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "insert Collect_set: ceq = None" (\ _ -> insert x (Collect_set a));
    Just eq -> Collect_set (fun_upda eq a x True);
  });

remove :: forall a. (Ceq a, Ccompare a) => a -> Set a -> Set a;
remove x (Complement a) = Complement (insert x a);
remove x (RBT_set rbt) =
  (case (ccompare :: Maybe (a -> a -> Ordera)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "remove RBT_set: ccompare = None" (\ _ -> remove x (RBT_set rbt));
    Just _ -> RBT_set (delete x rbt);
  });
remove x (DList_set dxs) =
  (case (ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "remove DList_set: ceq = None" (\ _ -> remove x (DList_set dxs));
    Just _ -> DList_set (removea x dxs);
  });
remove x (Collect_set a) =
  (case ceq of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a) "remove Collect: ceq = None"
        (\ _ -> remove x (Collect_set a));
    Just eq -> Collect_set (fun_upda eq a x False);
  });

foldl :: forall a b. (a -> b -> a) -> a -> [b] -> a;
foldl f a [] = a;
foldl f a (x : xs) = foldl f (f a x) xs;

set_aux :: forall a. (Ceq a, Ccompare a) => Set_impla -> [a] -> Set a;
set_aux Set_Monada = Set_Monad;
set_aux Set_Choose =
  (case (ccompare :: Maybe (a -> a -> Ordera)) of {
    Nothing -> (case (ceq :: Maybe (a -> a -> Bool)) of {
                 Nothing -> Set_Monad;
                 Just _ -> foldl (\ s x -> insert x s) (DList_set emptyb);
               });
    Just _ -> foldl (\ s x -> insert x s) (RBT_set emptyc);
  });
set_aux impl = foldl (\ s x -> insert x s) (set_empty impl);

set :: forall a. (Ceq a, Ccompare a, Set_impl a) => [a] -> Set a;
set xs = set_aux (of_phantom (set_impl :: Phantom a Set_impla)) xs;

fset_of_list :: forall a. (Ceq a, Ccompare a, Set_impl a) => [a] -> Fset a;
fset_of_list xa = Abs_fset (set xa);

fset :: forall a. Fset a -> Set a;
fset (Abs_fset x) = x;

bot_set :: forall a. (Ceq a, Ccompare a, Set_impl a) => Set a;
bot_set = set_empty (of_phantom (set_impl :: Phantom a Set_impla));

fold :: forall a b. (a -> b -> b) -> [a] -> b -> b;
fold f (x : xs) s = fold f xs (f x s);
fold f [] s = s;

foldc :: forall a b. (Ceq a) => (a -> b -> b) -> Set_dlist a -> b -> b;
foldc x xc = fold x (list_of_dlist xc);

folda :: forall a b c. (a -> b -> c -> c) -> Rbt a b -> c -> c;
folda f (Branch c lt k v rt) x = folda f rt (f k v (folda f lt x));
folda f Empty x = x;

foldb ::
  forall a b. (Ccompare a) => (a -> b -> b) -> Mapping_rbt a () -> b -> b;
foldb x xc = folda (\ a _ -> x a) (impl_ofa xc);

image ::
  forall a b.
    (Ceq a, Ccompare a, Ceq b, Ccompare b,
      Set_impl b) => (a -> b) -> Set a -> Set b;
image h (RBT_set rbt) =
  (case (ccompare :: Maybe (a -> a -> Ordera)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "image RBT_set: ccompare = None" (\ _ -> image h (RBT_set rbt));
    Just _ -> foldb (insert . h) rbt bot_set;
  });
image g (DList_set dxs) =
  (case (ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "image DList_set: ceq = None" (\ _ -> image g (DList_set dxs));
    Just _ -> foldc (insert . g) dxs bot_set;
  });
image f (Complement (Complement b)) = image f b;
image f (Collect_set a) =
  (error :: forall a. String -> (() -> a) -> a) "image Collect_set"
    (\ _ -> image f (Collect_set a));
image f (Set_Monad xs) = Set_Monad (map f xs);

fimage ::
  forall b a.
    (Ceq b, Ccompare b, Ceq a, Ccompare a,
      Set_impl a) => (b -> a) -> Fset b -> Fset a;
fimage xb xc = Abs_fset (image xb (fset xc));

fmdom ::
  forall a b.
    (Ceq a, Ccompare a, Set_impl a, Ceq b, Ccompare b,
      Set_impl b) => Fmap a b -> Fset a;
fmdom (Fmap_of_list m) = fimage fst (fset_of_list m);

dlist_all :: forall a. (Ceq a) => (a -> Bool) -> Set_dlist a -> Bool;
dlist_all x xc = all x (list_of_dlist xc);

rBT_Impl_rbt_all :: forall a b. (a -> b -> Bool) -> Rbt a b -> Bool;
rBT_Impl_rbt_all p (Branch c l k v r) =
  p k v && rBT_Impl_rbt_all p l && rBT_Impl_rbt_all p r;
rBT_Impl_rbt_all p Empty = True;

alla :: forall a b. (Ccompare a) => (a -> b -> Bool) -> Mapping_rbt a b -> Bool;
alla xb xc = rBT_Impl_rbt_all xb (impl_ofa xc);

ball :: forall a. (Ceq a, Ccompare a) => Set a -> (a -> Bool) -> Bool;
ball (RBT_set rbt) p =
  (case (ccompare :: Maybe (a -> a -> Ordera)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "Ball RBT_set: ccompare = None" (\ _ -> ball (RBT_set rbt) p);
    Just _ -> alla (\ k _ -> p k) rbt;
  });
ball (DList_set dxs) p =
  (case (ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a) "Ball DList_set: ceq = None"
        (\ _ -> ball (DList_set dxs) p);
    Just _ -> dlist_all p dxs;
  });
ball (Set_Monad xs) p = all p xs;

fBall :: forall a. (Ceq a, Ccompare a) => Fset a -> (a -> Bool) -> Bool;
fBall xa = ball (fset xa);

fmrel ::
  forall a b c.
    (Ceq a, Ccompare a, Set_impl a, Ceq b, Ccompare b, Set_impl b, Ceq c,
      Ccompare c, Eq c,
      Set_impl c) => (a -> b -> Bool) -> Fmap c a -> Fmap c b -> Bool;
fmrel r m n =
  fBall (fmdom m) (\ x -> rel_option r (fmlookup m x) (fmlookup n x)) &&
    fBall (fmdom n) (\ x -> rel_option r (fmlookup m x) (fmlookup n x));

equal_fmap ::
  forall a b.
    (Ceq a, Ccompare a, Eq a, Set_impl a, Ceq b, Ccompare b, Eq b,
      Set_impl b) => Fmap a b -> Fmap a b -> Bool;
equal_fmap = fmrel (\ a b -> a == b);

newtype Linear_poly = LinearPoly (Fmap Nat Rat);

linear_poly_map :: Linear_poly -> Fmap Nat Rat;
linear_poly_map (LinearPoly x) = x;

equal_linear_poly :: Linear_poly -> Linear_poly -> Bool;
equal_linear_poly x y = equal_fmap (linear_poly_map x) (linear_poly_map y);

instance Eq Linear_poly where {
  a == b = equal_linear_poly a b;
};

data Ty = BoolT | RatT;

equal_ty :: Ty -> Ty -> Bool;
equal_ty BoolT RatT = False;
equal_ty RatT BoolT = False;
equal_ty RatT RatT = True;
equal_ty BoolT BoolT = True;

instance Eq Ty where {
  a == b = equal_ty a b;
};

data Sig = LessF | LeF | SumF Nat | ConstF Rat | ProdF Nat | EqF;

equal_sig :: Sig -> Sig -> Bool;
equal_sig (ProdF x5) EqF = False;
equal_sig EqF (ProdF x5) = False;
equal_sig (ConstF x4) EqF = False;
equal_sig EqF (ConstF x4) = False;
equal_sig (ConstF x4) (ProdF x5) = False;
equal_sig (ProdF x5) (ConstF x4) = False;
equal_sig (SumF x3) EqF = False;
equal_sig EqF (SumF x3) = False;
equal_sig (SumF x3) (ProdF x5) = False;
equal_sig (ProdF x5) (SumF x3) = False;
equal_sig (SumF x3) (ConstF x4) = False;
equal_sig (ConstF x4) (SumF x3) = False;
equal_sig LeF EqF = False;
equal_sig EqF LeF = False;
equal_sig LeF (ProdF x5) = False;
equal_sig (ProdF x5) LeF = False;
equal_sig LeF (ConstF x4) = False;
equal_sig (ConstF x4) LeF = False;
equal_sig LeF (SumF x3) = False;
equal_sig (SumF x3) LeF = False;
equal_sig LessF EqF = False;
equal_sig EqF LessF = False;
equal_sig LessF (ProdF x5) = False;
equal_sig (ProdF x5) LessF = False;
equal_sig LessF (ConstF x4) = False;
equal_sig (ConstF x4) LessF = False;
equal_sig LessF (SumF x3) = False;
equal_sig (SumF x3) LessF = False;
equal_sig LessF LeF = False;
equal_sig LeF LessF = False;
equal_sig (ProdF x5) (ProdF y5) = equal_nat x5 y5;
equal_sig (ConstF x4) (ConstF y4) = equal_rat x4 y4;
equal_sig (SumF x3) (SumF y3) = equal_nat x3 y3;
equal_sig EqF EqF = True;
equal_sig LeF LeF = True;
equal_sig LessF LessF = True;

instance Eq Sig where {
  a == b = equal_sig a b;
};

newtype Alist b a = Alist [(b, a)];

data Sum a b = Inl a | Inr b;

data Mapping a b = Assoc_List_Mapping (Alist a b)
  | RBT_Mapping (Mapping_rbt a b) | Mapping (a -> Maybe b);

data State a b =
  State [(Nat, Linear_poly)] (Mapping Nat (a, b)) (Mapping Nat (a, b))
    (Mapping Nat b) Bool (Maybe [a]);

data Istate a =
  IState Nat [(Nat, Linear_poly)] [(a, Atom QDelta)] (Linear_poly -> Maybe Nat)
    [a];

data Formula a = Atom a | NegAtom a | Conjunction [Formula a]
  | Disjunction [Formula a];

data Tpoly a b = PVar a | PNum b | PSum [Tpoly a b] | PMult [Tpoly a b];

data Direction a b =
  Direction (b -> b -> Bool) (State a b -> Mapping Nat (a, b))
    (State a b -> Mapping Nat (a, b)) (State a b -> Nat -> Maybe b)
    (State a b -> Nat -> Maybe b) (State a b -> Nat -> a)
    (State a b -> Nat -> a)
    ((Mapping Nat (a, b) -> Mapping Nat (a, b)) -> State a b -> State a b)
    (Nat -> b -> Atom b) (Nat -> b -> Atom b) (Rat -> Rat -> Bool);

data Constraint = LT Linear_poly Rat | GT Linear_poly Rat | LEQ Linear_poly Rat
  | GEQ Linear_poly Rat | EQ Linear_poly Rat | LTPP Linear_poly Linear_poly
  | GTPP Linear_poly Linear_poly | LEQPP Linear_poly Linear_poly
  | GEQPP Linear_poly Linear_poly | EQPP Linear_poly Linear_poly;

data Linearity a = Non_Linear | Onea | Variable a;

data Ns_constraint a = LEQ_ns Linear_poly a | GEQ_ns Linear_poly a;

data Lin_rel = Less | Less_Equal | Equal;

data Lin_constraint a = Lin_Constraint [(Integer, a)] Lin_rel Integer;

data Poly_constraint a = Poly_Ge [(Monom a, Rat)] | Poly_Gt [(Monom a, Rat)]
  | Poly_Eq [(Monom a, Rat)];

plus_nat :: Nat -> Nat -> Nat;
plus_nat m n = Nat (integer_of_nat m + integer_of_nat n);

one_nat :: Nat;
one_nat = Nat (1 :: Integer);

suc :: Nat -> Nat;
suc n = plus_nat n one_nat;

minus_nat :: Nat -> Nat -> Nat;
minus_nat m n = Nat (max (0 :: Integer) (integer_of_nat m - integer_of_nat n));

zero_nat :: Nat;
zero_nat = Nat (0 :: Integer);

nth :: forall a. [a] -> Nat -> a;
nth (x : xs) n =
  (if equal_nat n zero_nat then x else nth xs (minus_nat n one_nat));

upt :: Nat -> Nat -> [Nat];
upt i j = (if less_nat i j then i : upt (suc i) j else []);

find :: forall a. (a -> Bool) -> [a] -> Maybe a;
find uu [] = Nothing;
find p (x : xs) = (if p x then Just x else find p xs);

fract :: Int -> Int -> Rat;
fract a b = Frct (normalize (a, b));

foldr :: forall a b. (a -> b -> b) -> [a] -> b -> b;
foldr f [] = id;
foldr f (x : xs) = f x . foldr f xs;

val :: QDelta -> Rat -> Rat;
val qd delta = plus_rat (qdfst qd) (times_rat delta (qdsnd qd));

memberc :: forall a. (Ceq a) => Set_dlist a -> a -> Bool;
memberc xa = list_member (the ceq) (list_of_dlist xa);

rbt_comp_lookup :: forall a b. (a -> a -> Ordera) -> Rbt a b -> a -> Maybe b;
rbt_comp_lookup c Empty k = Nothing;
rbt_comp_lookup c (Branch uu l x y r) k = (case c k x of {
    Eqa -> Just y;
    Lt -> rbt_comp_lookup c l k;
    Gt -> rbt_comp_lookup c r k;
  });

lookupb :: forall a b. (Ccompare a) => Mapping_rbt a b -> a -> Maybe b;
lookupb xa = rbt_comp_lookup (the ccompare) (impl_ofa xa);

memberb :: forall a. (Ccompare a) => Mapping_rbt a () -> a -> Bool;
memberb t x = lookupb t x == Just ();

member :: forall a. (Ceq a, Ccompare a) => a -> Set a -> Bool;
member x (Set_Monad xs) =
  (case ceq of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "member Set_Monad: ceq = None" (\ _ -> member x (Set_Monad xs));
    Just eq -> list_member eq xs x;
  });
member xa (Complement x) = not (member xa x);
member x (RBT_set rbt) = memberb rbt x;
member x (DList_set dxs) = memberc dxs x;
member x (Collect_set a) = a x;

update :: forall a b. (Eq a) => a -> b -> [(a, b)] -> [(a, b)];
update k v [] = [(k, v)];
update k v (p : ps) = (if fst p == k then (k, v) : ps else p : update k v ps);

merge :: forall a b. (Eq a) => [(a, b)] -> [(a, b)] -> [(a, b)];
merge qs ps = foldr (\ (a, b) -> update a b) ps qs;

fun_upd :: forall a b. (Eq a) => (a -> b) -> a -> b -> a -> b;
fun_upd f a b = (\ x -> (if x == a then b else f x));

membera :: forall a. (Eq a) => [a] -> a -> Bool;
membera [] y = False;
membera (x : xs) y = x == y || membera xs y;

bind :: forall a b. Maybe a -> (a -> Maybe b) -> Maybe b;
bind Nothing f = Nothing;
bind (Just x) f = f x;

lhs :: (Nat, Linear_poly) -> Nat;
lhs (l, r) = l;

rhs :: (Nat, Linear_poly) -> Linear_poly;
rhs (l, r) = r;

empty :: forall a b. Alist a b;
empty = Alist [];

extract :: forall a. (a -> Bool) -> [a] -> Maybe ([a], (a, [a]));
extract p (x : xs) =
  (if p x then Just ([], (x, xs))
    else (case extract p xs of {
           Nothing -> Nothing;
           Just (ys, (y, zs)) -> Just (x : ys, (y, zs));
         }));
extract p [] = Nothing;

hd :: forall a. [a] -> a;
hd (x21 : x22) = x21;

tl :: forall a. [a] -> [a];
tl [] = [];
tl (x21 : x22) = x22;

remdups :: forall a. (Eq a) => [a] -> [a];
remdups [] = [];
remdups (x : xs) = (if membera xs x then remdups xs else x : remdups xs);

gelb :: forall a. (Eq a) => (a -> a -> Bool) -> a -> Maybe a -> Bool;
gelb lt c b = (case b of {
                Nothing -> True;
                Just ba -> lt ba c || ba == c;
              });

geub :: forall a. (Eq a) => (a -> a -> Bool) -> a -> Maybe a -> Bool;
geub lt c b = (case b of {
                Nothing -> False;
                Just ba -> lt ba c || ba == c;
              });

gtlb :: forall a b. (a -> b -> Bool) -> b -> Maybe a -> Bool;
gtlb lt c b = (case b of {
                Nothing -> True;
                Just ba -> lt ba c;
              });

leub :: forall a. (Eq a) => (a -> a -> Bool) -> a -> Maybe a -> Bool;
leub lt c b = (case b of {
                Nothing -> True;
                Just ba -> lt c ba || c == ba;
              });

ltlb :: forall a b. (a -> b -> Bool) -> a -> Maybe b -> Bool;
ltlb lt c b = (case b of {
                Nothing -> False;
                Just a -> lt c a;
              });

ltub :: forall a b. (a -> b -> Bool) -> a -> Maybe b -> Bool;
ltub lt c b = (case b of {
                Nothing -> True;
                Just a -> lt c a;
              });

poly :: forall a. Ns_constraint a -> Linear_poly;
poly (LEQ_ns p a) = p;
poly (GEQ_ns p a) = p;

impl_of :: forall b a. Alist b a -> [(b, a)];
impl_of (Alist x) = x;

lookup :: forall a b. (Eq a) => Alist a b -> a -> Maybe b;
lookup xa = map_of (impl_of xa);

updatea :: forall a b. (Eq a) => a -> b -> Alist a b -> Alist a b;
updatea xc xd xe = Alist (update xc xd (impl_of xe));

mapping_empty_choose :: forall a b. (Ccompare a) => Mapping a b;
mapping_empty_choose = (case (ccompare :: Maybe (a -> a -> Ordera)) of {
                         Nothing -> Assoc_List_Mapping empty;
                         Just _ -> RBT_Mapping emptyc;
                       });

mapping_empty :: forall a b. (Ccompare a) => Mapping_impla -> Mapping a b;
mapping_empty Mapping_RBT = RBT_Mapping emptyc;
mapping_empty Mapping_Assoc_List = Assoc_List_Mapping empty;
mapping_empty Mapping_Mapping = Mapping (\ _ -> Nothing);
mapping_empty Mapping_Choose = mapping_empty_choose;

emptya :: forall a b. (Ccompare a, Mapping_impl a) => Mapping a b;
emptya = mapping_empty (of_phantom (mapping_impl :: Phantom a Mapping_impla));

gen_keys :: forall a b. [(a, Rbt a b)] -> Rbt a b -> [a];
gen_keys kts (Branch c l k v r) = gen_keys ((k, r) : kts) l;
gen_keys ((k, t) : kts) Empty = k : gen_keys kts t;
gen_keys [] Empty = [];

keys :: forall a b. Rbt a b -> [a];
keys = gen_keys [];

keysa :: forall a. (Ccompare a) => Mapping_rbt a () -> [a];
keysa xa = keys (impl_ofa xa);

lvars :: [(Nat, Linear_poly)] -> Set Nat;
lvars t = set (map lhs t);

fmmap :: forall a b c. (a -> b) -> Fmap c a -> Fmap c b;
fmmap f (Fmap_of_list m) = Fmap_of_list (map (apsnd f) m);

fmempty :: forall a b. Fmap a b;
fmempty = Fmap_of_list [];

scale :: Rat -> Fmap Nat Rat -> Fmap Nat Rat;
scale r lp = (if equal_rat r zero_rat then fmempty else fmmap (times_rat r) lp);

scaleRat_linear_poly :: Rat -> Linear_poly -> Linear_poly;
scaleRat_linear_poly r p = LinearPoly (scale r (linear_poly_map p));

uminus_linear_poly :: Linear_poly -> Linear_poly;
uminus_linear_poly lp = scaleRat_linear_poly (uminus_rat one_rat) lp;

get_var_coeff :: Fmap Nat Rat -> Nat -> Rat;
get_var_coeff lp v = (case fmlookup lp v of {
                       Nothing -> zero_rat;
                       Just c -> c;
                     });

gen_length :: forall a. Nat -> [a] -> Nat;
gen_length n (x : xs) = gen_length (suc n) xs;
gen_length n [] = n;

size_list :: forall a. [a] -> Nat;
size_list = gen_length zero_nat;

part :: forall a b. (Linorder b) => (a -> b) -> b -> [a] -> ([a], ([a], [a]));
part f pivot (x : xs) =
  (case part f pivot xs of {
    (lts, (eqs, gts)) ->
      let {
        xa = f x;
      } in (if less xa pivot then (x : lts, (eqs, gts))
             else (if less pivot xa then (lts, (eqs, x : gts))
                    else (lts, (x : eqs, gts))));
  });
part f pivot [] = ([], ([], []));

sort_key :: forall a b. (Linorder b) => (a -> b) -> [a] -> [a];
sort_key f xs =
  (case xs of {
    [] -> [];
    [_] -> xs;
    [x, y] -> (if less_eq (f x) (f y) then xs else [y, x]);
    _ : _ : _ : _ ->
      (case part f
              (f (nth xs
                   (divide_nat (size_list xs) (nat_of_integer (2 :: Integer)))))
              xs
        of {
        (lts, (eqs, gts)) -> sort_key f lts ++ eqs ++ sort_key f gts;
      });
  });

sorted_list_of_set ::
  forall a. (Ceq a, Ccompare a, Eq a, Linorder a) => Set a -> [a];
sorted_list_of_set (RBT_set rbt) =
  (case (ccompare :: Maybe (a -> a -> Ordera)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "sorted_list_of_set RBT_set: ccompare = None"
        (\ _ -> sorted_list_of_set (RBT_set rbt));
    Just _ -> sort_key (\ x -> x) (keysa rbt);
  });
sorted_list_of_set (DList_set dxs) =
  (case (ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "sorted_list_of_set DList_set: ceq = None"
        (\ _ -> sorted_list_of_set (DList_set dxs));
    Just _ -> sort_key (\ x -> x) (list_of_dlist dxs);
  });
sorted_list_of_set (Set_Monad xs) = sort_key (\ x -> x) (remdups xs);

ordered_keys ::
  forall a b.
    (Ceq a, Ccompare a, Eq a, Linorder a, Set_impl a, Ceq b, Ccompare b,
      Set_impl b) => Fmap a b -> [a];
ordered_keys m = sorted_list_of_set (fset (fmdom m));

fmfilter :: forall a b. (a -> Bool) -> Fmap a b -> Fmap a b;
fmfilter p (Fmap_of_list m) = Fmap_of_list (filter (\ (k, _) -> p k) m);

fmdrop :: forall a b. (Eq a) => a -> Fmap a b -> Fmap a b;
fmdrop a = fmfilter (\ aa -> not (aa == a));

fmadd :: forall a b. (Eq a) => Fmap a b -> Fmap a b -> Fmap a b;
fmadd (Fmap_of_list m) (Fmap_of_list n) = Fmap_of_list (merge m n);

fmupd :: forall a b. (Eq a) => a -> b -> Fmap a b -> Fmap a b;
fmupd k v m = fmadd m (Fmap_of_list [(k, v)]);

set_var_coeff :: Nat -> Rat -> Fmap Nat Rat -> Fmap Nat Rat;
set_var_coeff v c lp =
  (if equal_rat c zero_rat then fmdrop v lp else fmupd v c lp);

add_monom :: Rat -> Nat -> Fmap Nat Rat -> Fmap Nat Rat;
add_monom c v lp = set_var_coeff v (plus_rat c (get_var_coeff lp v)) lp;

add :: Fmap Nat Rat -> Fmap Nat Rat -> Fmap Nat Rat;
add lp1 lp2 =
  foldl (\ lp v -> add_monom (get_var_coeff lp1 v) v lp) lp2 (ordered_keys lp1);

plus_linear_poly :: Linear_poly -> Linear_poly -> Linear_poly;
plus_linear_poly p1 p2 =
  LinearPoly (add (linear_poly_map p1) (linear_poly_map p2));

minus_linear_poly :: Linear_poly -> Linear_poly -> Linear_poly;
minus_linear_poly lp1 lp2 = plus_linear_poly lp1 (uminus_linear_poly lp2);

constraint_to_qdelta_constraint :: Constraint -> [Ns_constraint QDelta];
constraint_to_qdelta_constraint (LT l r) =
  [LEQ_ns l (QDelta r (uminus_rat one_rat))];
constraint_to_qdelta_constraint (GT l r) = [GEQ_ns l (QDelta r one_rat)];
constraint_to_qdelta_constraint (LEQ l r) = [LEQ_ns l (QDelta r zero_rat)];
constraint_to_qdelta_constraint (GEQ l r) = [GEQ_ns l (QDelta r zero_rat)];
constraint_to_qdelta_constraint (EQ l r) =
  [LEQ_ns l (QDelta r zero_rat), GEQ_ns l (QDelta r zero_rat)];
constraint_to_qdelta_constraint (LTPP l1 l2) =
  [LEQ_ns (minus_linear_poly l1 l2) (QDelta zero_rat (uminus_rat one_rat))];
constraint_to_qdelta_constraint (GTPP l1 l2) =
  [GEQ_ns (minus_linear_poly l1 l2) (QDelta zero_rat one_rat)];
constraint_to_qdelta_constraint (LEQPP l1 l2) =
  [LEQ_ns (minus_linear_poly l1 l2) zero_QDelta];
constraint_to_qdelta_constraint (GEQPP l1 l2) =
  [GEQ_ns (minus_linear_poly l1 l2) zero_QDelta];
constraint_to_qdelta_constraint (EQPP l1 l2) =
  [LEQ_ns (minus_linear_poly l1 l2) zero_QDelta,
    GEQ_ns (minus_linear_poly l1 l2) zero_QDelta];

i_constraint_to_qdelta_constraint ::
  forall a. (a, Constraint) -> [(a, Ns_constraint QDelta)];
i_constraint_to_qdelta_constraint (i, c) =
  map (\ a -> (i, a)) (constraint_to_qdelta_constraint c);

to_ns :: forall a. [(a, Constraint)] -> [(a, Ns_constraint QDelta)];
to_ns l = concatMap i_constraint_to_qdelta_constraint l;

partition :: forall a. (a -> Bool) -> [a] -> ([a], [a]);
partition p [] = ([], []);
partition p (x : xs) =
  (case partition p xs of {
    (yes, no) -> (if p x then (x : yes, no) else (yes, x : no));
  });

lookupa :: forall a b. (Ccompare a, Eq a) => Mapping a b -> a -> Maybe b;
lookupa (RBT_Mapping t) = lookupb t;
lookupa (Assoc_List_Mapping al) = lookup al;

updateb ::
  forall a b. (Ccompare a, Eq a) => a -> b -> Mapping a b -> Mapping a b;
updateb k v (RBT_Mapping t) =
  (case (ccompare :: Maybe (a -> a -> Ordera)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "update RBT_Mapping: ccompare = None"
        (\ _ -> updateb k v (RBT_Mapping t));
    Just _ -> RBT_Mapping (insertb k v t);
  });
updateb k v (Assoc_List_Mapping al) = Assoc_List_Mapping (updatea k v al);
updateb k v (Mapping m) = Mapping (fun_upd m k (Just v));

b_i_l :: forall a b. State a b -> Mapping Nat (a, b);
b_i_l (State x1 x2 x3 x4 x5 x6) = x2;

indexl :: forall a b. State a b -> Nat -> a;
indexl s = (fst . the) . lookupa (b_i_l s);

b_i_u :: forall a b. State a b -> Mapping Nat (a, b);
b_i_u (State x1 x2 x3 x4 x5 x6) = x3;

indexu :: forall a b. State a b -> Nat -> a;
indexu s = (fst . the) . lookupa (b_i_u s);

form_or :: forall a. Formula a -> Formula a -> Formula a;
form_or (Disjunction []) psi = psi;
form_or (Atom v) (Disjunction []) = Atom v;
form_or (NegAtom v) (Disjunction []) = NegAtom v;
form_or (Conjunction v) (Disjunction []) = Conjunction v;
form_or (Disjunction (va : vb)) (Disjunction []) = Disjunction (va : vb);
form_or (Disjunction (v : va)) (Disjunction (vb : vc)) =
  Disjunction ((v : va) ++ vb : vc);
form_or (Disjunction (v : va)) (Atom vb) = Disjunction ((v : va) ++ [Atom vb]);
form_or (Disjunction (v : va)) (NegAtom vb) =
  Disjunction ((v : va) ++ [NegAtom vb]);
form_or (Disjunction (v : va)) (Conjunction vb) =
  Disjunction ((v : va) ++ [Conjunction vb]);
form_or (Atom v) (Disjunction (va : vb)) = Disjunction (Atom v : va : vb);
form_or (NegAtom v) (Disjunction (va : vb)) = Disjunction (NegAtom v : va : vb);
form_or (Conjunction v) (Disjunction (va : vb)) =
  Disjunction (Conjunction v : va : vb);
form_or (Atom v) (Atom va) = Disjunction [Atom v, Atom va];
form_or (Atom v) (NegAtom va) = Disjunction [Atom v, NegAtom va];
form_or (Atom v) (Conjunction va) = Disjunction [Atom v, Conjunction va];
form_or (NegAtom v) (Atom va) = Disjunction [NegAtom v, Atom va];
form_or (NegAtom v) (NegAtom va) = Disjunction [NegAtom v, NegAtom va];
form_or (NegAtom v) (Conjunction va) = Disjunction [NegAtom v, Conjunction va];
form_or (Conjunction v) (Atom va) = Disjunction [Conjunction v, Atom va];
form_or (Conjunction v) (NegAtom va) = Disjunction [Conjunction v, NegAtom va];
form_or (Conjunction v) (Conjunction va) =
  Disjunction [Conjunction v, Conjunction va];

cnf_form_or :: forall a. Formula a -> Formula a -> Formula a;
cnf_form_or (Conjunction phi_s) (Conjunction psi_s) =
  Conjunction (concatMap (\ phi -> map (form_or phi) psi_s) phi_s);
cnf_form_or (Atom v) psi = form_or (Atom v) psi;
cnf_form_or (NegAtom v) psi = form_or (NegAtom v) psi;
cnf_form_or (Disjunction v) psi = form_or (Disjunction v) psi;
cnf_form_or phi (Atom v) = form_or phi (Atom v);
cnf_form_or phi (NegAtom v) = form_or phi (NegAtom v);
cnf_form_or phi (Disjunction v) = form_or phi (Disjunction v);

form_cnf_ex :: forall a. [Formula a] -> Formula a;
form_cnf_ex [] = Conjunction [Disjunction []];
form_cnf_ex (phi : phi_s) = cnf_form_or phi (form_cnf_ex phi_s);

form_and :: forall a. Formula a -> Formula a -> Formula a;
form_and (Conjunction []) psi = psi;
form_and (Atom v) (Conjunction []) = Atom v;
form_and (NegAtom v) (Conjunction []) = NegAtom v;
form_and (Conjunction (va : vb)) (Conjunction []) = Conjunction (va : vb);
form_and (Disjunction v) (Conjunction []) = Disjunction v;
form_and (Conjunction (v : va)) (Conjunction (vb : vc)) =
  Conjunction ((v : va) ++ vb : vc);
form_and (Conjunction (v : va)) (Atom vb) = Conjunction ((v : va) ++ [Atom vb]);
form_and (Conjunction (v : va)) (NegAtom vb) =
  Conjunction ((v : va) ++ [NegAtom vb]);
form_and (Conjunction (v : va)) (Disjunction vb) =
  Conjunction ((v : va) ++ [Disjunction vb]);
form_and (Atom v) (Conjunction (va : vb)) = Conjunction (Atom v : va : vb);
form_and (NegAtom v) (Conjunction (va : vb)) =
  Conjunction (NegAtom v : va : vb);
form_and (Disjunction v) (Conjunction (va : vb)) =
  Conjunction (Disjunction v : va : vb);
form_and (Atom v) (Atom va) = Conjunction [Atom v, Atom va];
form_and (Atom v) (NegAtom va) = Conjunction [Atom v, NegAtom va];
form_and (Atom v) (Disjunction va) = Conjunction [Atom v, Disjunction va];
form_and (NegAtom v) (Atom va) = Conjunction [NegAtom v, Atom va];
form_and (NegAtom v) (NegAtom va) = Conjunction [NegAtom v, NegAtom va];
form_and (NegAtom v) (Disjunction va) = Conjunction [NegAtom v, Disjunction va];
form_and (Disjunction v) (Atom va) = Conjunction [Disjunction v, Atom va];
form_and (Disjunction v) (NegAtom va) = Conjunction [Disjunction v, NegAtom va];
form_and (Disjunction v) (Disjunction va) =
  Conjunction [Disjunction v, Disjunction va];

form_all :: forall a. [Formula a] -> Formula a;
form_all [] = Conjunction [];
form_all (phi : phi_s) = form_and phi (form_all phi_s);

flatten :: forall a. Formula a -> Formula a;
flatten (Conjunction phi_s) = form_all (map flatten phi_s);
flatten (Disjunction phi_s) = form_cnf_ex (map flatten phi_s);
flatten (Atom v) = Conjunction [Disjunction [Atom v]];
flatten (NegAtom v) = Conjunction [Disjunction [NegAtom v]];

is_Atom :: forall a. Formula a -> Bool;
is_Atom (Atom uu) = True;
is_Atom (NegAtom v) = False;
is_Atom (Conjunction v) = False;
is_Atom (Disjunction v) = False;

map_option :: forall a b. (a -> b) -> Maybe a -> Maybe b;
map_option f Nothing = Nothing;
map_option f (Just x2) = Just (f x2);

boundsl :: forall a b. State a b -> Nat -> Maybe b;
boundsl s = map_option snd . lookupa (b_i_l s);

boundsu :: forall a b. State a b -> Nat -> Maybe b;
boundsu s = map_option snd . lookupa (b_i_u s);

vars_list :: Linear_poly -> [Nat];
vars_list lp = ordered_keys (linear_poly_map lp);

min :: forall a. (Ord a) => a -> a -> a;
min a b = (if less_eq a b then a else b);

sum_list :: forall a. (Monoid_add a) => [a] -> a;
sum_list xs = foldr plus xs zeroa;

valuate :: forall a. (Rational_vector a) => Linear_poly -> (Nat -> a) -> a;
valuate lp val =
  let {
    lpm = linear_poly_map lp;
  } in sum_list
         (map (\ x -> scaleRat (the (fmlookup lpm x)) (val x)) (vars_list lp));

delta_0 :: QDelta -> QDelta -> Rat;
delta_0 qd1 qd2 =
  let {
    c1 = qdfst qd1;
    c2 = qdfst qd2;
    k1 = qdsnd qd1;
    k2 = qdsnd qd2;
  } in (if less_rat c1 c2 && less_rat k2 k1
         then divide_rat (minus_rat c2 c1) (minus_rat k1 k2) else one_rat);

delta_0_val :: Ns_constraint QDelta -> (Nat -> QDelta) -> Rat;
delta_0_val (LEQ_ns lll rrr) vl = delta_0 (valuate lll vl) rrr;
delta_0_val (GEQ_ns lll rrr) vl = delta_0 rrr (valuate lll vl);

delta_0_val_min :: [Ns_constraint QDelta] -> (Nat -> QDelta) -> Rat;
delta_0_val_min [] vl = one_rat;
delta_0_val_min (h : t) vl = min (delta_0_val_min t vl) (delta_0_val h vl);

tabulate ::
  forall a b.
    (Ccompare a, Eq a, Mapping_impl a) => [a] -> (a -> b) -> Mapping a b;
tabulate xs f = fold (\ k -> updateb k (f k)) xs emptya;

map2fun :: forall a. (Zero a) => Mapping Nat a -> Nat -> a;
map2fun v = (\ x -> (case lookupa v x of {
                      Nothing -> zeroa;
                      Just y -> y;
                    }));

from_ns :: Mapping Nat QDelta -> [Ns_constraint QDelta] -> Mapping Nat Rat;
from_ns vl cs =
  let {
    delta = delta_0_val_min cs (map2fun vl);
  } in tabulate (remdups (concatMap vars_list (map poly cs)))
         (\ var -> val (map2fun vl var) delta);

uBI_upd ::
  forall a b.
    (Linorder b) => Direction a b ->
                      (Mapping Nat (a, b) -> Mapping Nat (a, b)) ->
                        State a b -> State a b;
uBI_upd (Direction x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) = x8;

update_B_I ::
  forall a b c d e.
    (Ccompare a,
      Eq a) => ((Mapping a (b, c) -> Mapping a (b, c)) -> d -> e) ->
                 b -> a -> c -> d -> e;
update_B_I field_update i x c s = field_update (updateb x (i, c)) s;

lt :: forall a b. (Linorder b) => Direction a b -> b -> b -> Bool;
lt (Direction x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) = x1;

ub :: forall a b. (Linorder b) => Direction a b -> State a b -> Nat -> Maybe b;
ub (Direction x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) = x5;

li :: forall a b. (Linorder b) => Direction a b -> State a b -> Nat -> a;
li (Direction x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) = x6;

lb :: forall a b. (Linorder b) => Direction a b -> State a b -> Nat -> Maybe b;
lb (Direction x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) = x4;

v_update :: forall a b. Mapping Nat a -> State b a -> State b a;
v_update v (State t bil biu v_old u uc) = State t bil biu v u uc;

v :: forall a b. State a b -> Mapping Nat b;
v (State x1 x2 x3 x4 x5 x6) = x4;

t :: forall a b. State a b -> [(Nat, Linear_poly)];
t (State x1 x2 x3 x4 x5 x6) = x1;

coeff :: Linear_poly -> Nat -> Rat;
coeff lp = get_var_coeff (linear_poly_map lp);

rhs_eq_val ::
  forall a.
    (Minus a, Plus a, Zero a,
      ScaleRat a) => Mapping Nat a -> Nat -> a -> (Nat, Linear_poly) -> a;
rhs_eq_val v x_i c e =
  let {
    x_j = lhs e;
    a_i_j = coeff (rhs e) x_i;
  } in plus (map2fun v x_j) (scaleRat a_i_j (minus c (map2fun v x_i)));

update_code :: forall a b. (Lrv a) => Nat -> a -> State b a -> State b a;
update_code x c s =
  v_update
    (updateb x c
      (foldl (\ va e -> updateb (lhs e) (rhs_eq_val (v s) x c e) va) (v s)
        (t s)))
    s;

set_unsat :: forall a b. (Eq a) => [a] -> State a b -> State a b;
set_unsat i (State t bil biu v u uc) =
  State t bil biu v True (Just (remdups i));

assert_bound_codea ::
  forall a b.
    (Eq a, Eq b,
      Lrv b) => Direction a b -> a -> Nat -> b -> State a b -> State a b;
assert_bound_codea dir i x c s =
  (if geub (lt dir) c (ub dir s x) then s
    else let {
           sa = update_B_I (uBI_upd dir) i x c s;
         } in (if ltlb (lt dir) c (lb dir s x) then set_unsat [i, li dir s x] sa
                else (if not (member x (lvars (t sa))) &&
                           lt dir c (map2fun (v s) x)
                       then update_code x c sa else sa)));

b_i_u_update ::
  forall a b.
    (Mapping Nat (a, b) -> Mapping Nat (a, b)) -> State a b -> State a b;
b_i_u_update up (State t bil biu v u uc) = State t bil (up biu) v u uc;

positive :: forall a b. (Linorder b) => Direction a b;
positive =
  Direction less b_i_l b_i_u boundsl boundsu indexl indexu b_i_u_update Leq Geq
    less_eq_rat;

b_i_l_update ::
  forall a b.
    (Mapping Nat (a, b) -> Mapping Nat (a, b)) -> State a b -> State a b;
b_i_l_update up (State t bil biu v u uc) = State t (up bil) biu v u uc;

negative :: forall a b. (Linorder b) => Direction a b;
negative =
  Direction (\ x y -> less y x) b_i_u b_i_l boundsu boundsl indexu indexl
    b_i_l_update Geq Leq (\ x y -> less_eq_rat y x);

assert_bound_code ::
  forall a b. (Eq a, Eq b, Lrv b) => (a, Atom b) -> State a b -> State a b;
assert_bound_code (i, Leq x c) s = assert_bound_codea positive i x c s;
assert_bound_code (i, Geq x c) s = assert_bound_codea negative i x c s;

u :: forall a b. State a b -> Bool;
u (State x1 x2 x3 x4 x5 x6) = x5;

assert_bound_loop_code ::
  forall a b. (Eq a, Eq b, Lrv b) => [(a, Atom b)] -> State a b -> State a b;
assert_bound_loop_code ats s =
  foldl (\ sa a -> (if u sa then sa else assert_bound_code a sa)) s ats;

init_state :: forall a b. (Zero b) => [(Nat, Linear_poly)] -> State a b;
init_state t =
  State t (mapping_empty (of_phantom mapping_impl_nat))
    (mapping_empty (of_phantom mapping_impl_nat))
    (tabulate (remdups (map lhs t ++ concatMap (vars_list . rhs) t))
      (\ _ -> zeroa))
    False Nothing;

min_satisfying :: forall a. (Linorder a) => (a -> Bool) -> [a] -> Maybe a;
min_satisfying p l =
  let {
    xs = filter p l;
  } in (if null xs then Nothing else Just (foldl min (hd xs) (tl xs)));

le_ubound :: forall a. (Eq a, Linorder a) => a -> Maybe a -> Bool;
le_ubound c b = leub less c b;

ge_lbound :: forall a. (Eq a, Linorder a) => a -> Maybe a -> Bool;
ge_lbound c b = gelb less c b;

in_bounds ::
  forall a b.
    (Eq b, Linorder b) => a -> (a -> b) -> (a -> Maybe b, a -> Maybe b) -> Bool;
in_bounds x v (lb, ub) = ge_lbound (v x) (lb x) && le_ubound (v x) (ub x);

min_lvar_not_in_bounds ::
  forall a b. (Zero b, Eq b, Linorder b) => State a b -> Maybe Nat;
min_lvar_not_in_bounds s =
  min_satisfying
    (\ x -> not (in_bounds x (map2fun (v s)) (boundsl s, boundsu s)))
    (map lhs (t s));

var :: Nat -> Linear_poly;
var x = LinearPoly (set_var_coeff x one_rat fmempty);

subst_var :: Nat -> Linear_poly -> Linear_poly -> Linear_poly;
subst_var v lpa lp =
  minus_linear_poly
    (plus_linear_poly lp (scaleRat_linear_poly (coeff lp v) lpa))
    (scaleRat_linear_poly (coeff lp v) (var v));

subst_var_eq_code ::
  Nat -> Linear_poly -> (Nat, Linear_poly) -> (Nat, Linear_poly);
subst_var_eq_code v lp eq = (lhs eq, subst_var v lp (rhs eq));

eq_idx_for_lvar_aux :: [(Nat, Linear_poly)] -> Nat -> Nat -> Nat;
eq_idx_for_lvar_aux [] x i = i;
eq_idx_for_lvar_aux (eq : t) x i =
  (if equal_nat (lhs eq) x then i
    else eq_idx_for_lvar_aux t x (plus_nat i one_nat));

eq_idx_for_lvar :: [(Nat, Linear_poly)] -> Nat -> Nat;
eq_idx_for_lvar t x = eq_idx_for_lvar_aux t x zero_nat;

eq_for_lvar_code :: [(Nat, Linear_poly)] -> Nat -> (Nat, Linear_poly);
eq_for_lvar_code t v = nth t (eq_idx_for_lvar t v);

pivot_eq :: (Nat, Linear_poly) -> Nat -> (Nat, Linear_poly);
pivot_eq e y =
  let {
    cy = coeff (rhs e) y;
  } in (y, plus_linear_poly
             (scaleRat_linear_poly (divide_rat (uminus_rat one_rat) cy)
               (minus_linear_poly (rhs e) (scaleRat_linear_poly cy (var y))))
             (scaleRat_linear_poly (divide_rat one_rat cy) (var (lhs e))));

pivot_tableau_code ::
  Nat -> Nat -> [(Nat, Linear_poly)] -> [(Nat, Linear_poly)];
pivot_tableau_code x_i x_j t =
  let {
    eq = eq_for_lvar_code t x_i;
    eqa = pivot_eq eq x_j;
  } in map (\ e ->
             (if equal_nat (lhs e) (lhs eq) then eqa
               else subst_var_eq_code x_j (rhs eqa) e))
         t;

t_update :: forall a b. [(Nat, Linear_poly)] -> State a b -> State a b;
t_update t (State t_old bil biu v u uc) = State t bil biu v u uc;

pivot_code :: forall a b. (Lrv b) => Nat -> Nat -> State a b -> State a b;
pivot_code x_i x_j s = t_update (pivot_tableau_code x_i x_j (t s)) s;

pivot_and_update_code ::
  forall a b. (Lrv a) => Nat -> Nat -> a -> State b a -> State b a;
pivot_and_update_code x_i x_j c s = update_code x_i c (pivot_code x_i x_j s);

ui :: forall a b. (Linorder b) => Direction a b -> State a b -> Nat -> a;
ui (Direction x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) = x7;

unsat_indices ::
  forall a b.
    (Eq a,
      Linorder b) => Direction a b ->
                       State a b -> [Nat] -> (Nat, Linear_poly) -> [a];
unsat_indices dir s vs eq =
  let {
    r = rhs eq;
    lia = li dir s;
    uia = ui dir s;
  } in remdups
         (lia (lhs eq) :
           map (\ x -> (if less_rat (coeff r x) zero_rat then lia x else uia x))
             vs);

min_rvar_incdec_eq ::
  forall a b.
    (Eq a,
      Lrv b) => Direction a b -> State a b -> (Nat, Linear_poly) -> Sum [a] Nat;
min_rvar_incdec_eq dir s eq =
  let {
    rvars = vars_list (rhs eq);
  } in (case min_satisfying
               (\ x ->
                 less_rat zero_rat (coeff (rhs eq) x) &&
                   ltub (lt dir) (map2fun (v s) x) (ub dir s x) ||
                   less_rat (coeff (rhs eq) x) zero_rat &&
                     gtlb (lt dir) (map2fun (v s) x) (lb dir s x))
               rvars
         of {
         Nothing -> Inl (unsat_indices dir s rvars eq);
         Just a -> Inr a;
       });

check_codea ::
  forall a b. (Eq a, Lrv b) => Direction a b -> Nat -> State a b -> State a b;
check_codea dir x_i s =
  let {
    l_i = the (lb dir s x_i);
  } in (case min_rvar_incdec_eq dir s (eq_for_lvar_code (t s) x_i) of {
         Inl i -> set_unsat i s;
         Inr x_j -> pivot_and_update_code x_i x_j l_i s;
       });

lt_lbound :: forall a. (Linorder a) => a -> Maybe a -> Bool;
lt_lbound c b = ltlb less c b;

check_code :: forall a b. (Eq a, Eq b, Lrv b) => State a b -> State a b;
check_code s =
  (if u s then s
    else (case min_lvar_not_in_bounds s of {
           Nothing -> s;
           Just x_i ->
             let {
               dir = (if lt_lbound (map2fun (v s) x_i) (boundsl s x_i)
                       then positive else negative);
             } in check_code (check_codea dir x_i s);
         }));

assert_all_state_code ::
  forall a b.
    (Eq a, Eq b, Lrv b) => [(Nat, Linear_poly)] -> [(a, Atom b)] -> State a b;
assert_all_state_code t ats =
  check_code (assert_bound_loop_code ats (init_state t));

u_c :: forall a b. State a b -> Maybe [a];
u_c (State x1 x2 x3 x4 x5 x6) = x6;

assert_all_code ::
  forall a b.
    (Eq a, Eq b,
      Lrv b) => [(Nat, Linear_poly)] ->
                  [(a, Atom b)] -> Sum [a] (Mapping Nat b);
assert_all_code t asa = let {
                          s = assert_all_state_code t asa;
                        } in (if u s then Inl (the (u_c s)) else Inr (v s));

max_var :: Linear_poly -> Nat;
max_var lp = let {
               vl = vars_list lp;
             } in (if null vl then zero_nat else foldl max (hd vl) (tl vl));

normalize_ns_constraint ::
  forall a. (Lrv a) => Ns_constraint a -> Ns_constraint a;
normalize_ns_constraint (LEQ_ns l r) =
  let {
    v = max_var l;
    c = coeff l v;
  } in (if equal_rat c zero_rat then LEQ_ns l r
         else let {
                ic = inverse_rat c;
              } in (if less_rat c zero_rat
                     then GEQ_ns (scaleRat_linear_poly ic l) (scaleRat ic r)
                     else LEQ_ns (scaleRat_linear_poly ic l) (scaleRat ic r)));
normalize_ns_constraint (GEQ_ns l r) =
  let {
    v = max_var l;
    c = coeff l v;
  } in (if equal_rat c zero_rat then GEQ_ns l r
         else let {
                ic = inverse_rat c;
              } in (if less_rat c zero_rat
                     then LEQ_ns (scaleRat_linear_poly ic l) (scaleRat ic r)
                     else GEQ_ns (scaleRat_linear_poly ic l) (scaleRat ic r)));

pivot_tableau_eq ::
  [(Nat, Linear_poly)] ->
    (Nat, Linear_poly) ->
      [(Nat, Linear_poly)] ->
        Nat ->
          ([(Nat, Linear_poly)], ((Nat, Linear_poly), [(Nat, Linear_poly)]));
pivot_tableau_eq t1 eq t2 x = let {
                                eqa = pivot_eq eq x;
                                m = map (subst_var_eq_code x (rhs eqa));
                              } in (m t1, (eqa, m t2));

preprocess_opt ::
  forall a.
    (Lrv a) => Set Nat ->
                 [(Nat, Linear_poly)] ->
                   [(Nat, Linear_poly)] ->
                     ([(Nat, Linear_poly)], Mapping Nat a -> Mapping Nat a);
preprocess_opt x t1 [] = (t1, id);
preprocess_opt xa t1 ((x, p) : t2) =
  (if not (member x xa)
    then (case preprocess_opt xa t1 t2 of {
           (t, tv) -> (t, (\ v -> updateb x (valuate p (map2fun v)) v) . tv);
         })
    else (case find (\ xb -> not (member xb xa)) (vars_list p) of {
           Nothing -> preprocess_opt xa ((x, p) : t1) t2;
           Just y ->
             (case pivot_tableau_eq t1 (x, p) t2 y of {
               (tt1, ((z, q), tt2)) ->
                 (case preprocess_opt xa tt1 tt2 of {
                   (t, tv) ->
                     (t, (\ v -> updateb z (valuate q (map2fun v)) v) . tv);
                 });
             });
         }));

atom_var :: forall a. Atom a -> Nat;
atom_var (Leq var a) = var;
atom_var (Geq var a) = var;

preprocess_part_2 ::
  forall a b c.
    (Ceq a, Ccompare a, Set_impl a, Compare b, Eq b,
      Lrv c) => [(a, Atom b)] ->
                  [(Nat, Linear_poly)] ->
                    ([(Nat, Linear_poly)], Mapping Nat c -> Mapping Nat c);
preprocess_part_2 asa t =
  preprocess_opt (image atom_var (image snd (set asa))) [] t;

start_fresh_variable :: forall a. [(a, Ns_constraint QDelta)] -> Nat;
start_fresh_variable [] = zero_nat;
start_fresh_variable ((i, h) : t) =
  max (plus_nat (max_var (poly h)) one_nat) (start_fresh_variable t);

unsatIndices :: forall a. Istate a -> [a];
unsatIndices (IState x1 x2 x3 x4 x5) = x5;

tableau :: forall a. Istate a -> [(Nat, Linear_poly)];
tableau (IState x1 x2 x3 x4 x5) = x2;

atoms :: forall a. Istate a -> [(a, Atom QDelta)];
atoms (IState x1 x2 x3 x4 x5) = x3;

zero :: Fmap Nat Rat;
zero = fmempty;

zero_linear_poly :: Linear_poly;
zero_linear_poly = LinearPoly zero;

qdelta_constraint_to_atom :: Ns_constraint QDelta -> Nat -> Atom QDelta;
qdelta_constraint_to_atom (LEQ_ns l r) v = Leq v r;
qdelta_constraint_to_atom (GEQ_ns l r) v = Geq v r;

firstFreshVariable :: forall a. Istate a -> Nat;
firstFreshVariable (IState x1 x2 x3 x4 x5) = x1;

is_monom :: Linear_poly -> Bool;
is_monom l = equal_nat (size_list (vars_list l)) one_nat;

poly_Mapping :: forall a. Istate a -> Linear_poly -> Maybe Nat;
poly_Mapping (IState x1 x2 x3 x4 x5) = x4;

linear_poly_to_eq :: Linear_poly -> Nat -> (Nat, Linear_poly);
linear_poly_to_eq p v = (v, p);

zero_satisfies :: forall a. (Lrv a) => Ns_constraint a -> Bool;
zero_satisfies (LEQ_ns l r) = less_eq zeroa r;
zero_satisfies (GEQ_ns l r) = less_eq r zeroa;

monom_var :: Linear_poly -> Nat;
monom_var l = max_var l;

monom_coeff :: Linear_poly -> Rat;
monom_coeff l = coeff l (monom_var l);

monom_to_atom :: Ns_constraint QDelta -> Atom QDelta;
monom_to_atom (LEQ_ns l r) =
  (if less_rat (monom_coeff l) zero_rat
    then Geq (monom_var l) (scaleRat_QDelta (inverse_rat (monom_coeff l)) r)
    else Leq (monom_var l) (scaleRat_QDelta (inverse_rat (monom_coeff l)) r));
monom_to_atom (GEQ_ns l r) =
  (if less_rat (monom_coeff l) zero_rat
    then Leq (monom_var l) (scaleRat_QDelta (inverse_rat (monom_coeff l)) r)
    else Geq (monom_var l) (scaleRat_QDelta (inverse_rat (monom_coeff l)) r));

preprocessa :: forall a. [(a, Ns_constraint QDelta)] -> Nat -> Istate a;
preprocessa ((i, h) : t) v =
  let {
    s = preprocessa t v;
    p = poly h;
    is_monom_h = is_monom p;
    va = firstFreshVariable s;
    ta = tableau s;
    a = atoms s;
    m = poly_Mapping s;
    u = unsatIndices s;
  } in (if is_monom_h then IState va ta ((i, monom_to_atom h) : a) m u
         else (if equal_linear_poly p zero_linear_poly
                then (if zero_satisfies h then s else IState va ta a m (i : u))
                else (case m p of {
                       Nothing ->
                         IState (plus_nat va one_nat)
                           (linear_poly_to_eq p va : ta)
                           ((i, qdelta_constraint_to_atom h va) : a)
                           (fun_upd m p (Just va)) u;
                       Just vaa ->
                         IState va ta ((i, qdelta_constraint_to_atom h vaa) : a)
                           m u;
                     })));
preprocessa [] v = IState v [] [] (\ _ -> Nothing) [];

preprocess_part_1 ::
  forall a.
    [(a, Ns_constraint QDelta)] ->
      ([(Nat, Linear_poly)], ([(a, Atom QDelta)], [a]));
preprocess_part_1 l = let {
                        start = start_fresh_variable l;
                        is = preprocessa l start;
                      } in (tableau is, (atoms is, unsatIndices is));

map_prod :: forall a b c d. (a -> b) -> (c -> d) -> (a, c) -> (b, d);
map_prod f g (a, b) = (f a, g b);

preprocess ::
  forall a.
    (Ceq a, Ccompare a,
      Set_impl a) => [(a, Ns_constraint QDelta)] ->
                       ([(Nat, Linear_poly)],
                         ([(a, Atom QDelta)],
                           (Mapping Nat QDelta -> Mapping Nat QDelta, [a])));
preprocess l =
  (case preprocess_part_1 (map (map_prod id normalize_ns_constraint) l) of {
    (t, (asa, ui)) -> (case preprocess_part_2 asa t of {
                        (ta, tv) -> (ta, (asa, (tv, ui)));
                      });
  });

solve_exec_ns_code ::
  forall a.
    (Ceq a, Ccompare a, Eq a,
      Set_impl a) => [(a, Ns_constraint QDelta)] ->
                       Sum [a] (Mapping Nat QDelta);
solve_exec_ns_code s =
  (case preprocess s of {
    (t, (asa, (trans_v, []))) -> (case assert_all_code t asa of {
                                   Inl a -> Inl a;
                                   Inr v -> Inr (trans_v v);
                                 });
    (_, (_, (_, i : _))) -> Inl [i];
  });

solve_exec_code ::
  forall a.
    (Ceq a, Ccompare a, Eq a,
      Set_impl a) => [(a, Constraint)] -> Sum [a] (Mapping Nat Rat);
solve_exec_code cs = let {
                       csa = to_ns cs;
                     } in (case solve_exec_ns_code csa of {
                            Inl a -> Inl a;
                            Inr v -> Inr (from_ns v (map snd csa));
                          });

simplex_index ::
  forall a.
    (Ceq a, Ccompare a, Eq a,
      Set_impl a) => [(a, Constraint)] -> Sum [a] (Mapping Nat Rat);
simplex_index = solve_exec_code;

simplex :: [Constraint] -> Sum [Nat] (Mapping Nat Rat);
simplex cs = simplex_index (zip (upt zero_nat (size_list cs)) cs);

binda :: forall a b c. Sum a b -> (b -> Sum a c) -> Sum a c;
binda m f = (case m of {
              Inl a -> Inl a;
              Inr a -> f a;
            });

form_not :: forall a. Formula a -> Formula a;
form_not (Atom a) = NegAtom a;
form_not (NegAtom a) = Atom a;
form_not (Conjunction phi_s) = Disjunction (map form_not phi_s);
form_not (Disjunction phi_s) = Conjunction (map form_not phi_s);

get_Atom :: forall a. Formula a -> a;
get_Atom (Atom a) = a;
get_Atom (NegAtom a) = a;

of_alist ::
  forall a b. (Ccompare a, Eq a, Mapping_impl a) => [(a, b)] -> Mapping a b;
of_alist xs = foldr (\ (a, b) -> updateb a b) xs emptya;

check :: forall a. Bool -> a -> Sum a ();
check b e = (if b then Inr () else Inl e);

to_rat :: Integer -> Rat;
to_rat x = fract (Int_of_integer x) one_int;

catch_error :: forall a b c. Sum a b -> (a -> Sum c b) -> Sum c b;
catch_error m f = (case m of {
                    Inl a -> f a;
                    Inr a -> Inr a;
                  });

forallM :: forall a b. (a -> Sum b ()) -> [a] -> Sum (a, b) ();
forallM f [] = Inr ();
forallM f (x : xs) =
  binda (catch_error (f x) (\ xa -> Inl (x, xa))) (\ _ -> forallM f xs);

one_monom :: forall a. (Linorder a) => Monom a;
one_monom = Abs_monom [];

zero_poly :: forall a b. [(Monom a, b)];
zero_poly = [];

var_monom :: forall a. (Linorder a) => a -> Monom a;
var_monom xa = Abs_monom [(xa, one_nat)];

monom_mult_list ::
  forall a. (Eq a, Linorder a) => [(a, Nat)] -> [(a, Nat)] -> [(a, Nat)];
monom_mult_list [] n = n;
monom_mult_list ((x, p) : m) n =
  (case n of {
    [] -> (x, p) : m;
    (y, q) : na ->
      (if x == y then (x, plus_nat p q) : monom_mult_list m na
        else (if less x y then (x, p) : monom_mult_list m n
               else (y, q) : monom_mult_list ((x, p) : m) na));
  });

times_monom :: forall a. (Eq a, Linorder a) => Monom a -> Monom a -> Monom a;
times_monom xb xc = Abs_monom (monom_mult_list (rep_monom xb) (rep_monom xc));

monom_mult_poly ::
  forall a b.
    (Eq a, Linorder a, Eq b,
      Semiring_0 b) => (Monom a, b) -> [(Monom a, b)] -> [(Monom a, b)];
monom_mult_poly uu [] = [];
monom_mult_poly (ma, c) ((m, d) : p) =
  (if times c d == zeroa then monom_mult_poly (ma, c) p
    else (times_monom ma m, times c d) : monom_mult_poly (ma, c) p);

poly_add ::
  forall a b.
    (Eq a, Linorder a, Eq b,
      Semiring_0 b) => [(Monom a, b)] -> [(Monom a, b)] -> [(Monom a, b)];
poly_add [] q = q;
poly_add ((m, c) : p) q =
  (case extract (\ mc -> fst mc == m) q of {
    Nothing -> (m, c) : poly_add p q;
    Just (q1, ((_, d), q2)) ->
      (if plus c d == zeroa then poly_add p (q1 ++ q2)
        else (m, plus c d) : poly_add p (q1 ++ q2));
  });

poly_mult ::
  forall a b.
    (Eq a, Linorder a, Eq b,
      Semiring_0 b) => [(Monom a, b)] -> [(Monom a, b)] -> [(Monom a, b)];
poly_mult [] q = [];
poly_mult (mc : p) q = poly_add (monom_mult_poly mc q) (poly_mult p q);

one_poly :: forall a b. (Linorder a, Semiring_1 b) => [(Monom a, b)];
one_poly = [(one_monom, one)];

poly_of ::
  forall a b.
    (Eq a, Linorder a, Eq b, Comm_semiring_1 b) => Tpoly a b -> [(Monom a, b)];
poly_of (PNum i) = (if i == zeroa then [] else [(one_monom, i)]);
poly_of (PVar x) = [(var_monom x, one)];
poly_of (PSum []) = zero_poly;
poly_of (PSum (p : ps)) = poly_add (poly_of p) (poly_of (PSum ps));
poly_of (PMult []) = one_poly;
poly_of (PMult (p : ps)) = poly_mult (poly_of p) (poly_of (PMult ps));

la_solver :: La_solver_type -> [Constraint] -> Maybe (Nat -> Rat);
la_solver Simplex_Solver cs = (case simplex cs of {
                                Inl _ -> Nothing;
                                Inr v -> Just (map2fun v);
                              });

divmod_nat :: Nat -> Nat -> (Nat, Nat);
divmod_nat m n =
  let {
    k = integer_of_nat m;
    l = integer_of_nat n;
  } in map_prod nat_of_integer nat_of_integer
         (if k == (0 :: Integer) then ((0 :: Integer), (0 :: Integer))
           else (if l == (0 :: Integer) then ((0 :: Integer), k)
                  else divMod ( k ) ( l )));

binary_power :: forall a. (Monoid_mult a) => a -> Nat -> a;
binary_power x n =
  (if equal_nat n zero_nat then one
    else (case divmod_nat n (nat_of_integer (2 :: Integer)) of {
           (d, r) -> let {
                       rec = binary_power (times x x) d;
                     } in (if equal_nat r zero_nat then rec else times rec x);
         }));

eval_monom_list ::
  forall a b. (Linorder a, Comm_semiring_1 b) => (a -> b) -> [(a, Nat)] -> b;
eval_monom_list alpha [] = one;
eval_monom_list alpha ((x, p) : m) =
  times (eval_monom_list alpha m) (binary_power (alpha x) p);

eval_monom ::
  forall a b. (Linorder a, Comm_semiring_1 b) => (a -> b) -> Monom a -> b;
eval_monom x xc = eval_monom_list x (rep_monom xc);

eval_poly ::
  forall a b.
    (Linorder a, Comm_semiring_1 b) => (a -> b) -> [(Monom a, b)] -> b;
eval_poly alpha [] = zeroa;
eval_poly alpha (mc : p) =
  plus (times (eval_monom alpha (fst mc)) (snd mc)) (eval_poly alpha p);

poly_minus ::
  forall a b.
    (Eq a, Linorder a, Eq b,
      Ring_1 b) => [(Monom a, b)] -> [(Monom a, b)] -> [(Monom a, b)];
poly_minus f g = poly_add f (monom_mult_poly (one_monom, uminus one) g);

explode :: String -> [Char];
explode s =
  map char_of_integer
    (map (let ord k | (k < 128) = Prelude.toInteger k in ord . (Prelude.fromEnum :: Prelude.Char -> Prelude.Int))
      s);

trivial_checker :: forall a. (Eq a) => [Formula a] -> Bool;
trivial_checker lits = (case partition is_Atom lits of {
                         (asa, nas) -> let {
 pos = map get_Atom asa;
 neg = map get_Atom nas;
                                       } in any (membera neg) pos;
                       });

modulo_int :: Int -> Int -> Int;
modulo_int k l =
  Int_of_integer (modulo_integer (integer_of_int k) (integer_of_int l));

numeral :: forall a. (Numeral a) => Num -> a;
numeral (Bit1 n) = let {
                     m = numeral n;
                   } in plus (plus m m) one;
numeral (Bit0 n) = let {
                     m = numeral n;
                   } in plus m m;
numeral One = one;

of_int :: forall a. (Ring_1 a) => Int -> a;
of_int k =
  (if equal_int k zero_int then zeroa
    else (if less_int k zero_int then uminus (of_int (uminus_int k))
           else let {
                  l = times (numeral (Bit0 One))
                        (of_int (divide_int k (Int_of_integer (2 :: Integer))));
                  j = modulo_int k (Int_of_integer (2 :: Integer));
                } in (if equal_int j zero_int then l else plus l one)));

convert_lin_rel :: Lin_rel -> Sig;
convert_lin_rel Less = LessF;
convert_lin_rel Less_Equal = LeF;
convert_lin_rel Equal = EqF;

monom_vars_list :: forall a. (Linorder a) => Monom a -> [a];
monom_vars_list xa = map fst (rep_monom xa);

poly_vars_list :: forall a b. (Eq a, Linorder a) => [(Monom a, b)] -> [a];
poly_vars_list p = remdups (concatMap (monom_vars_list . fst) p);

monom_list_linearity :: forall a. [(a, Nat)] -> Linearity a;
monom_list_linearity [] = Onea;
monom_list_linearity [(x, n)] =
  (if equal_nat n one_nat then Variable x else Non_Linear);
monom_list_linearity (v : vb : vc) = Non_Linear;

monom_linearity :: forall a. (Linorder a) => Monom a -> Linearity a;
monom_linearity xa = monom_list_linearity (rep_monom xa);

map_formula :: forall a b. (a -> b) -> Formula a -> Formula b;
map_formula f (Atom x1) = Atom (f x1);
map_formula f (NegAtom x2) = NegAtom (f x2);
map_formula f (Conjunction x3) = Conjunction (map (map_formula f) x3);
map_formula f (Disjunction x4) = Disjunction (map (map_formula f) x4);

convert_lin_poly :: [(Integer, String)] -> Term Sig ([Char], Ty);
convert_lin_poly cxs =
  Fun (SumF (size_list cxs))
    (map (\ (r, x) ->
           Fun (ProdF (nat_of_integer (2 :: Integer)))
             [Fun (ConstF (to_rat r)) [], Var (explode x, RatT)])
      cxs);

negatea :: forall a. Term Sig (a, Ty) -> Formula (Term Sig (a, Ty));
negatea (Fun LessF [a, b]) = Atom (Fun LeF [b, a]);
negatea (Fun LeF [a, b]) = Atom (Fun LessF [b, a]);
negatea (Fun EqF [a, b]) =
  Disjunction [Atom (Fun LessF [a, b]), Atom (Fun LessF [b, a])];
negatea (Var v) = Conjunction [];
negatea (Fun LeF []) = Conjunction [];
negatea (Fun LeF [v]) = Conjunction [];
negatea (Fun LeF (v : vc : ve : vf)) = Conjunction [];
negatea (Fun (SumF vb) va) = Conjunction [];
negatea (Fun (ConstF vb) va) = Conjunction [];
negatea (Fun (ProdF vb) va) = Conjunction [];
negatea (Fun EqF []) = Conjunction [];
negatea (Fun EqF [v]) = Conjunction [];
negatea (Fun EqF (v : vc : ve : vf)) = Conjunction [];
negatea (Fun v []) = Conjunction [];
negatea (Fun v [vb]) = Conjunction [];
negatea (Fun v (vb : vd : vf : vg)) = Conjunction [];

lp_monom :: Rat -> Nat -> Linear_poly;
lp_monom c x =
  LinearPoly (if equal_rat c zero_rat then fmempty else fmupd x c fmempty);

of_rat :: forall a. (Field_char_0 a) => Rat -> a;
of_rat p = (case quotient_of p of {
             (a, b) -> divide (of_int a) (of_int b);
           });

trivial_clause_checker :: forall a. (Eq a) => Formula a -> Bool;
trivial_clause_checker f = (case f of {
                             Disjunction a -> trivial_checker a;
                           });

showsl_literal :: String -> String -> String;
showsl_literal s = showsl_lit s;

showsl_formula ::
  forall a. (a -> String -> String) -> Formula a -> String -> String;
showsl_formula showsl_atom (Disjunction fs) =
  let {
    a = map (showsl_formula showsl_atom) fs;
  } in showsl_list_gen id "False" "Disj[" ", " "]" a;
showsl_formula showsl_atom (Conjunction fs) =
  let {
    a = map (showsl_formula showsl_atom) fs;
  } in showsl_list_gen id "True" "Conj[" ", " "]" a;
showsl_formula showsl_atom (NegAtom a) =
  (showsl_literal "! (" . showsl_atom a) . showsl_literal ")";
showsl_formula showsl_atom (Atom a) = showsl_atom a;

remove_Atom ::
  forall a b c.
    (Showl b) => (Term a (b, c) -> Formula (Term a (b, c))) ->
                   Formula (Term a (b, c)) -> Formula (Term a (b, c));
remove_Atom negate_atom (Atom phi) = form_not (negate_atom phi);
remove_Atom negate_atom (NegAtom phi) = NegAtom phi;
remove_Atom negate_atom (Disjunction phi_s) =
  Disjunction (map (remove_Atom negate_atom) phi_s);
remove_Atom negate_atom (Conjunction phi_s) =
  Conjunction (map (remove_Atom negate_atom) phi_s);

check_valid_formula ::
  forall a b c d.
    (Eq a, Eq b, Showl b, Eq c, Default d,
      Showl d) => (Term a (b, c) -> String -> String) ->
                    (d -> Formula (Term a (b, c)) ->
                            Sum (String -> String) ()) ->
                      (Term a (b, c) -> Formula (Term a (b, c))) ->
                        d -> Formula (Term a (b, c)) ->
                               Sum (String -> String) ();
check_valid_formula showsl_atom logic_checker negate_atom h phi =
  catch_error
    (case flatten phi of {
      Conjunction phi_s ->
        catch_error
          (forallM
            (\ phia ->
              catch_error
                (check (trivial_clause_checker phia)
                  "trivial clause checker failed")
                (\ _ ->
                  (case flatten (remove_Atom negate_atom phia) of {
                    Conjunction phi_sa ->
                      catch_error (forallM (logic_checker h) phi_sa)
                        (\ x -> Inl (snd x));
                  })))
            phi_s)
          (\ x -> Inl (snd x));
    })
    (\ x ->
      Inl (((showsl_lit "problem in checking validity of formula " .
              showsl_formula showsl_atom phi) .
             showsl_literal "\n") .
            x));

rA_exp_to_tpoly :: forall a. Term Sig (a, Ty) -> Tpoly a Rat;
rA_exp_to_tpoly (Var (a, ty)) = PVar a;
rA_exp_to_tpoly (Fun (SumF uu) asa) = PSum (map rA_exp_to_tpoly asa);
rA_exp_to_tpoly (Fun (ConstF a) []) = PNum a;
rA_exp_to_tpoly (Fun (ProdF uv) asa) = PMult (map rA_exp_to_tpoly asa);

rA_exp_to_poly ::
  forall a. (Eq a, Linorder a) => Term Sig (a, Ty) -> [(Monom a, Rat)];
rA_exp_to_poly = poly_of . rA_exp_to_tpoly;

showsl_monom_list ::
  forall a. (Linorder a, Showl a) => [(a, Nat)] -> String -> String;
showsl_monom_list [(x, p)] =
  (if equal_nat p one_nat then showsl_lit "x" . showsl x
    else ((showsl_lit "x" . showsl x) . showsl_lit "^") . showsl_nat p);
showsl_monom_list ((x, p) : v : va) =
  ((if equal_nat p one_nat then showsl_lit "x" . showsl x
     else ((showsl_lit "x" . showsl x) . showsl_literal "^") . showsl_nat p) .
    showsl_literal "*") .
    showsl_monom_list (v : va);
showsl_monom_list [] = showsl_literal "1";

showsl_monom :: forall a. (Linorder a, Showl a) => Monom a -> String -> String;
showsl_monom xa = showsl_monom_list (rep_monom xa);

showsl_poly ::
  forall a b.
    (Eq a, Linorder a, Showl a, One b, Eq b,
      Showl b) => [(Monom a, b)] -> String -> String;
showsl_poly [] = showsl_lit "0";
showsl_poly ((m, c) : p) =
  (if c == one then showsl_monom m
    else (if m == one_monom then showsl c
           else (showsl c . showsl_lit "*") . showsl_monom m)) .
    (if null p then id else showsl_lit " + " . showsl_poly p);

showsl_RA_exp ::
  forall a. (Eq a, Linorder a, Showl a) => Term Sig (a, Ty) -> String -> String;
showsl_RA_exp (Fun LessF [s, t]) =
  (showsl_RA_exp s . showsl_lit " < ") . showsl_RA_exp t;
showsl_RA_exp (Fun LeF [s, t]) =
  (showsl_RA_exp s . showsl_lit " <= ") . showsl_RA_exp t;
showsl_RA_exp (Fun EqF [s, t]) =
  (showsl_RA_exp s . showsl_lit " = ") . showsl_RA_exp t;
showsl_RA_exp (Var v) = showsl_poly (rA_exp_to_poly (Var v));
showsl_RA_exp (Fun LeF []) =
  (showsl_poly :: [(Monom a, Rat)] -> String -> String)
    ((rA_exp_to_poly :: Term Sig (a, Ty) -> [(Monom a, Rat)]) (Fun LeF []));
showsl_RA_exp (Fun LeF [v]) = showsl_poly (rA_exp_to_poly (Fun LeF [v]));
showsl_RA_exp (Fun LeF (v : vc : ve : vf)) =
  showsl_poly (rA_exp_to_poly (Fun LeF (v : vc : ve : vf)));
showsl_RA_exp (Fun (SumF vb) va) =
  showsl_poly (rA_exp_to_poly (Fun (SumF vb) va));
showsl_RA_exp (Fun (ConstF vb) va) =
  showsl_poly (rA_exp_to_poly (Fun (ConstF vb) va));
showsl_RA_exp (Fun (ProdF vb) va) =
  showsl_poly (rA_exp_to_poly (Fun (ProdF vb) va));
showsl_RA_exp (Fun EqF []) =
  (showsl_poly :: [(Monom a, Rat)] -> String -> String)
    ((rA_exp_to_poly :: Term Sig (a, Ty) -> [(Monom a, Rat)]) (Fun EqF []));
showsl_RA_exp (Fun EqF [v]) = showsl_poly (rA_exp_to_poly (Fun EqF [v]));
showsl_RA_exp (Fun EqF (v : vc : ve : vf)) =
  showsl_poly (rA_exp_to_poly (Fun EqF (v : vc : ve : vf)));
showsl_RA_exp (Fun v []) =
  (showsl_poly :: [(Monom a, Rat)] -> String -> String)
    ((rA_exp_to_poly :: Term Sig (a, Ty) -> [(Monom a, Rat)]) (Fun v []));
showsl_RA_exp (Fun v [vb]) = showsl_poly (rA_exp_to_poly (Fun v [vb]));
showsl_RA_exp (Fun v (vb : vd : vf : vg)) =
  showsl_poly (rA_exp_to_poly (Fun v (vb : vd : vf : vg)));

rA_exp_to_poly_constraint ::
  forall a. (Eq a, Linorder a) => Term Sig (a, Ty) -> Poly_constraint a;
rA_exp_to_poly_constraint (Fun LeF [a, b]) =
  Poly_Ge (poly_minus (rA_exp_to_poly b) (rA_exp_to_poly a));
rA_exp_to_poly_constraint (Fun EqF [a, b]) =
  Poly_Eq (poly_minus (rA_exp_to_poly b) (rA_exp_to_poly a));
rA_exp_to_poly_constraint (Fun LessF [a, b]) =
  Poly_Gt (poly_minus (rA_exp_to_poly b) (rA_exp_to_poly a));

showsl_poly_constraint ::
  forall a.
    (Eq a, Linorder a, Showl a) => Poly_constraint a -> String -> String;
showsl_poly_constraint (Poly_Ge p) = showsl_poly p . showsl_lit " >= 0";
showsl_poly_constraint (Poly_Gt p) = showsl_poly p . showsl_lit " > 0";
showsl_poly_constraint (Poly_Eq p) = showsl_poly p . showsl_lit " = 0";

translate_atom :: forall a. Formula a -> a;
translate_atom (Atom e) = e;

translate_atoms :: forall a. [Formula a] -> [a];
translate_atoms = map translate_atom;

translate_conj :: forall a. Formula a -> [a];
translate_conj (Conjunction phi_s) = translate_atoms phi_s;

vars_poly_constraint_list ::
  forall a. (Eq a, Linorder a) => Poly_constraint a -> [a];
vars_poly_constraint_list (Poly_Ge p) = poly_vars_list p;
vars_poly_constraint_list (Poly_Gt p) = poly_vars_list p;
vars_poly_constraint_list (Poly_Eq p) = poly_vars_list p;

interpret_poly_constraint ::
  forall a. (Linorder a) => (a -> Rat) -> Poly_constraint a -> Bool;
interpret_poly_constraint f (Poly_Ge p) = less_eq_rat zero_rat (eval_poly f p);
interpret_poly_constraint f (Poly_Gt p) = less_rat zero_rat (eval_poly f p);
interpret_poly_constraint f (Poly_Eq p) = equal_rat (eval_poly f p) zero_rat;

rpoly_to_linear_poly ::
  forall a.
    (Linorder a) => (a -> Nat) -> [(Monom a, Rat)] -> Maybe (Linear_poly, Rat);
rpoly_to_linear_poly rho [] = Just (zero_linear_poly, zero_rat);
rpoly_to_linear_poly rho ((monomial, c) : rest) =
  bind (rpoly_to_linear_poly rho rest)
    (\ (p, d) ->
      (case monom_linearity monomial of {
        Non_Linear -> Nothing;
        Onea -> Just (p, plus_rat c d);
        Variable x ->
          Just (plus_linear_poly (lp_monom (of_rat c) (rho x)) p, d);
      }));

to_linear_constraints ::
  forall a. (Linorder a) => (a -> Nat) -> Poly_constraint a -> [Constraint];
to_linear_constraints rho (Poly_Ge p) =
  (case rpoly_to_linear_poly rho p of {
    Nothing -> [];
    Just (q, c) -> [GEQ q (of_rat (uminus_rat c))];
  });
to_linear_constraints rho (Poly_Gt p) =
  (case rpoly_to_linear_poly rho p of {
    Nothing -> [];
    Just (q, c) -> [GT q (of_rat (uminus_rat c))];
  });
to_linear_constraints rho (Poly_Eq p) =
  (case rpoly_to_linear_poly rho p of {
    Nothing -> [];
    Just (q, c) -> [EQ q (of_rat (uminus_rat c))];
  });

unsat_via_la_solver ::
  forall a.
    (Ccompare a, Eq a, Mapping_impl a,
      Linorder a) => La_solver_type ->
                       [Poly_constraint a] -> Maybe (Maybe ([a], a -> Rat));
unsat_via_la_solver typea les =
  let {
    vs = remdups (concatMap vars_poly_constraint_list les);
    ren_map = of_alist (zip vs (upt zero_nat (size_list vs)));
    ren_fun = (\ v -> (case lookupa ren_map v of {
                        Nothing -> zero_nat;
                        Just n -> n;
                      }));
    cs = concatMap (to_linear_constraints ren_fun) les;
  } in (case la_solver typea cs of {
         Nothing -> Just Nothing;
         Just beta ->
           let {
             alpha = beta . ren_fun;
           } in (if all (interpret_poly_constraint alpha) les
                  then Just (Just (vs, alpha)) else Nothing);
       });

unsat_checker ::
  forall a.
    (Ccompare a, Eq a, Mapping_impl a, Linorder a,
      Showl a) => Hints -> [Poly_constraint a] -> Sum (String -> String) ();
unsat_checker hints cnjs =
  catch_error
    (case hints of {
      LA_Solver typea ->
        (case unsat_via_la_solver typea cnjs of {
          Nothing ->
            Inl (showsl_lit
                  "could not use linear arithmetic solver to prove unsatisfiability");
          Just Nothing -> Inr ();
          Just (Just (vs, alpha)) ->
            Inl (showsl_lit "the linear inequalities are satisfiable:\n" .
                  showsl_list_gen
                    (\ v ->
                      (showsl_monom (var_monom v) . showsl_lit " := ") .
                        showsl_rat (alpha v))
                    "" "" "\n" "" vs);
        });
    })
    (\ x ->
      Inl (((showsl_lit "The linear inequalities\n  " .
              showsl_sep showsl_poly_constraint (showsl_lit "\n  ") cnjs) .
             showsl_lit "\ncannot be proved unsatisfiable\n  ") .
            x));

check_clause ::
  forall a.
    (Ccompare a, Eq a, Mapping_impl a, Linorder a,
      Showl a) => Hints ->
                    Formula (Term Sig (a, Ty)) -> Sum (String -> String) ();
check_clause hints phi =
  let {
    es = map rA_exp_to_poly_constraint (translate_conj (form_not phi));
  } in catch_error (unsat_checker hints es)
         (\ x ->
           Inl (((showsl_lit
                    "Could not prove unsatisfiability of RA conjunction\n" .
                   showsl_list_gen showsl_poly_constraint "False" "" " && " ""
                     es) .
                  showsl_literal "\n") .
                 x));

convert_lin_constraint :: Lin_constraint String -> Term Sig ([Char], Ty);
convert_lin_constraint (Lin_Constraint p r c) =
  Fun (convert_lin_rel r) [convert_lin_poly p, Fun (ConstF (to_rat c)) []];

lra_validity_checker :: Formula (Lin_constraint String) -> String;
lra_validity_checker f =
  (case check_valid_formula showsl_RA_exp check_clause negatea
          (LA_Solver Simplex_Solver) (map_formula convert_lin_constraint f)
    of {
    Inl e ->
      (showsl_lit
         "formula is perhaps not valid, answer of solver should contain counter-model\n" .
        e)
        "";
    Inr _ -> "formula is valid";
  });

example_la_formula :: Formula (Lin_constraint String);
example_la_formula =
  Disjunction
    [NegAtom
       (Lin_Constraint [((2 :: Integer), "y")] Less_Equal (11 :: Integer)),
      NegAtom (Lin_Constraint [((-1 :: Integer), "x")] Less (-5 :: Integer)),
      Atom (Lin_Constraint [((-1 :: Integer), "x"), ((1 :: Integer), "y")] Less
             (0 :: Integer))];

}
