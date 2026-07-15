{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Str(Char, integer_of_char, equal_char, less_eq_char, less_char, implode,
       char_of_integer, explode, char_0x20, char_0x21, char_0x22, char_0x23,
       char_0x26, char_0x27, char_0x28, char_0x29, char_0x2A, char_0x2B,
       char_0x2C, char_0x2D, char_0x2F, char_0x30, char_0x31, char_0x32,
       char_0x33, char_0x34, char_0x35, char_0x36, char_0x37, char_0x38,
       char_0x39, char_0x3A, char_0x3B, char_0x3C, char_0x3D, char_0x3E,
       char_0x3F, char_0x41, char_0x42, char_0x43, char_0x44, char_0x45,
       char_0x46, char_0x47, char_0x48, char_0x49, char_0x4A, char_0x4B,
       char_0x4C, char_0x4D, char_0x4E, char_0x4F, char_0x50, char_0x51,
       char_0x52, char_0x53, char_0x54, char_0x55, char_0x56, char_0x57,
       char_0x58, char_0x59, char_0x5A, char_0x5B, char_0x5D, char_0x5F,
       char_0x61, char_0x62, char_0x63, char_0x64, char_0x65, char_0x66,
       char_0x67, char_0x68, char_0x69, char_0x6A, char_0x6B, char_0x6C,
       char_0x6D, char_0x6E, char_0x6F, char_0x70, char_0x71, char_0x72,
       char_0x73, char_0x74, char_0x75, char_0x76, char_0x77, char_0x78,
       char_0x79, char_0x7A)
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
import qualified Arith;
import qualified Countable;
import qualified Quasi_Order;
import qualified Orderings;

newtype Char = Chr Integer;

integer_of_char :: Char -> Integer;
integer_of_char (Chr x) = x;

equal_char :: Char -> Char -> Bool;
equal_char c d = integer_of_char c == integer_of_char d;

instance Eq Char where {
  a == b = equal_char a b;
};

less_eq_char :: Char -> Char -> Bool;
less_eq_char c d = integer_of_char c <= integer_of_char d;

less_char :: Char -> Char -> Bool;
less_char c d = integer_of_char c < integer_of_char d;

instance Orderings.Ord Char where {
  less_eq = less_eq_char;
  less = less_char;
};

instance Quasi_Order.Quasi_order Char where {
};

instance Quasi_Order.Weak_order Char where {
};

instance Orderings.Preorder Char where {
};

instance Orderings.Order Char where {
};

instance Orderings.Linorder Char where {
};

instance Countable.Countable Char where {
};

implode :: [Char] -> String;
implode cs = Str_Literal.literalOfAsciis (map integer_of_char cs);

char_of_integer :: Integer -> Char;
char_of_integer k =
  Chr (if (0 :: Integer) <= k && k < (256 :: Integer) then k
        else Arith.modulo_integer k (256 :: Integer));

explode :: String -> [Char];
explode s = map char_of_integer (Str_Literal.asciisOfLiteral s);

char_0x20 :: Char;
char_0x20 = Chr (32 :: Integer);

char_0x21 :: Char;
char_0x21 = Chr (33 :: Integer);

char_0x22 :: Char;
char_0x22 = Chr (34 :: Integer);

char_0x23 :: Char;
char_0x23 = Chr (35 :: Integer);

char_0x26 :: Char;
char_0x26 = Chr (38 :: Integer);

char_0x27 :: Char;
char_0x27 = Chr (39 :: Integer);

char_0x28 :: Char;
char_0x28 = Chr (40 :: Integer);

char_0x29 :: Char;
char_0x29 = Chr (41 :: Integer);

char_0x2A :: Char;
char_0x2A = Chr (42 :: Integer);

char_0x2B :: Char;
char_0x2B = Chr (43 :: Integer);

char_0x2C :: Char;
char_0x2C = Chr (44 :: Integer);

char_0x2D :: Char;
char_0x2D = Chr (45 :: Integer);

char_0x2F :: Char;
char_0x2F = Chr (47 :: Integer);

char_0x30 :: Char;
char_0x30 = Chr (48 :: Integer);

char_0x31 :: Char;
char_0x31 = Chr (49 :: Integer);

char_0x32 :: Char;
char_0x32 = Chr (50 :: Integer);

char_0x33 :: Char;
char_0x33 = Chr (51 :: Integer);

char_0x34 :: Char;
char_0x34 = Chr (52 :: Integer);

char_0x35 :: Char;
char_0x35 = Chr (53 :: Integer);

char_0x36 :: Char;
char_0x36 = Chr (54 :: Integer);

char_0x37 :: Char;
char_0x37 = Chr (55 :: Integer);

char_0x38 :: Char;
char_0x38 = Chr (56 :: Integer);

char_0x39 :: Char;
char_0x39 = Chr (57 :: Integer);

char_0x3A :: Char;
char_0x3A = Chr (58 :: Integer);

char_0x3B :: Char;
char_0x3B = Chr (59 :: Integer);

char_0x3C :: Char;
char_0x3C = Chr (60 :: Integer);

char_0x3D :: Char;
char_0x3D = Chr (61 :: Integer);

char_0x3E :: Char;
char_0x3E = Chr (62 :: Integer);

char_0x3F :: Char;
char_0x3F = Chr (63 :: Integer);

char_0x41 :: Char;
char_0x41 = Chr (65 :: Integer);

char_0x42 :: Char;
char_0x42 = Chr (66 :: Integer);

char_0x43 :: Char;
char_0x43 = Chr (67 :: Integer);

char_0x44 :: Char;
char_0x44 = Chr (68 :: Integer);

char_0x45 :: Char;
char_0x45 = Chr (69 :: Integer);

char_0x46 :: Char;
char_0x46 = Chr (70 :: Integer);

char_0x47 :: Char;
char_0x47 = Chr (71 :: Integer);

char_0x48 :: Char;
char_0x48 = Chr (72 :: Integer);

char_0x49 :: Char;
char_0x49 = Chr (73 :: Integer);

char_0x4A :: Char;
char_0x4A = Chr (74 :: Integer);

char_0x4B :: Char;
char_0x4B = Chr (75 :: Integer);

char_0x4C :: Char;
char_0x4C = Chr (76 :: Integer);

char_0x4D :: Char;
char_0x4D = Chr (77 :: Integer);

char_0x4E :: Char;
char_0x4E = Chr (78 :: Integer);

char_0x4F :: Char;
char_0x4F = Chr (79 :: Integer);

char_0x50 :: Char;
char_0x50 = Chr (80 :: Integer);

char_0x51 :: Char;
char_0x51 = Chr (81 :: Integer);

char_0x52 :: Char;
char_0x52 = Chr (82 :: Integer);

char_0x53 :: Char;
char_0x53 = Chr (83 :: Integer);

char_0x54 :: Char;
char_0x54 = Chr (84 :: Integer);

char_0x55 :: Char;
char_0x55 = Chr (85 :: Integer);

char_0x56 :: Char;
char_0x56 = Chr (86 :: Integer);

char_0x57 :: Char;
char_0x57 = Chr (87 :: Integer);

char_0x58 :: Char;
char_0x58 = Chr (88 :: Integer);

char_0x59 :: Char;
char_0x59 = Chr (89 :: Integer);

char_0x5A :: Char;
char_0x5A = Chr (90 :: Integer);

char_0x5B :: Char;
char_0x5B = Chr (91 :: Integer);

char_0x5D :: Char;
char_0x5D = Chr (93 :: Integer);

char_0x5F :: Char;
char_0x5F = Chr (95 :: Integer);

char_0x61 :: Char;
char_0x61 = Chr (97 :: Integer);

char_0x62 :: Char;
char_0x62 = Chr (98 :: Integer);

char_0x63 :: Char;
char_0x63 = Chr (99 :: Integer);

char_0x64 :: Char;
char_0x64 = Chr (100 :: Integer);

char_0x65 :: Char;
char_0x65 = Chr (101 :: Integer);

char_0x66 :: Char;
char_0x66 = Chr (102 :: Integer);

char_0x67 :: Char;
char_0x67 = Chr (103 :: Integer);

char_0x68 :: Char;
char_0x68 = Chr (104 :: Integer);

char_0x69 :: Char;
char_0x69 = Chr (105 :: Integer);

char_0x6A :: Char;
char_0x6A = Chr (106 :: Integer);

char_0x6B :: Char;
char_0x6B = Chr (107 :: Integer);

char_0x6C :: Char;
char_0x6C = Chr (108 :: Integer);

char_0x6D :: Char;
char_0x6D = Chr (109 :: Integer);

char_0x6E :: Char;
char_0x6E = Chr (110 :: Integer);

char_0x6F :: Char;
char_0x6F = Chr (111 :: Integer);

char_0x70 :: Char;
char_0x70 = Chr (112 :: Integer);

char_0x71 :: Char;
char_0x71 = Chr (113 :: Integer);

char_0x72 :: Char;
char_0x72 = Chr (114 :: Integer);

char_0x73 :: Char;
char_0x73 = Chr (115 :: Integer);

char_0x74 :: Char;
char_0x74 = Chr (116 :: Integer);

char_0x75 :: Char;
char_0x75 = Chr (117 :: Integer);

char_0x76 :: Char;
char_0x76 = Chr (118 :: Integer);

char_0x77 :: Char;
char_0x77 = Chr (119 :: Integer);

char_0x78 :: Char;
char_0x78 = Chr (120 :: Integer);

char_0x79 :: Char;
char_0x79 = Chr (121 :: Integer);

char_0x7A :: Char;
char_0x7A = Chr (122 :: Integer);

}
