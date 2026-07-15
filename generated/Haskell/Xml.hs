{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Xml(Xml(..), Xmldoc(..), doc_of_string) where {

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
import qualified Error_Monad;
import qualified Parser_Monad;
import qualified Sum_Type;
import qualified Showa;
import qualified HOL;
import qualified Arith;

data Xml = XML [Arith.Char] [([Arith.Char], [Arith.Char])] [Xml]
  | XML_text [Arith.Char];

data Xmldoc = XMLDOC [[Arith.Char]] Xml;

letters :: [Arith.Char];
letters =
  [Arith.char_0x61, Arith.char_0x62, Arith.char_0x63, Arith.char_0x64,
    Arith.char_0x65, Arith.char_0x66, Arith.char_0x67, Arith.char_0x68,
    Arith.char_0x69, Arith.char_0x6A, Arith.char_0x6B, Arith.char_0x6C,
    Arith.char_0x6D, Arith.char_0x6E, Arith.char_0x6F, Arith.char_0x70,
    Arith.char_0x71, Arith.char_0x72, Arith.char_0x73, Arith.char_0x74,
    Arith.char_0x75, Arith.char_0x76, Arith.char_0x77, Arith.char_0x78,
    Arith.char_0x79, Arith.char_0x7A, Arith.char_0x41, Arith.char_0x42,
    Arith.char_0x43, Arith.char_0x44, Arith.char_0x45, Arith.char_0x46,
    Arith.char_0x47, Arith.char_0x48, Arith.char_0x49, Arith.char_0x4A,
    Arith.char_0x4B, Arith.char_0x4C, Arith.char_0x4D, Arith.char_0x4E,
    Arith.char_0x4F, Arith.char_0x50, Arith.char_0x51, Arith.char_0x52,
    Arith.char_0x53, Arith.char_0x54, Arith.char_0x55, Arith.char_0x56,
    Arith.char_0x57, Arith.char_0x58, Arith.char_0x59, Arith.char_0x5A,
    Arith.char_0x5F, Arith.char_0x30, Arith.char_0x31, Arith.char_0x32,
    Arith.char_0x33, Arith.char_0x34, Arith.char_0x35, Arith.char_0x36,
    Arith.char_0x37, Arith.char_0x38, Arith.char_0x39, Arith.char_0x26,
    Arith.char_0x3B, Arith.char_0x3A, Arith.char_0x2D];

is_letter :: Arith.Char -> Bool;
is_letter c =
  let {
    ci = Arith.integer_of_char c;
  } in (97 :: Integer) <= ci && ci <= (122 :: Integer) ||
         ((65 :: Integer) <= ci && ci <= (90 :: Integer) ||
           ((48 :: Integer) <= ci && ci <= (59 :: Integer) ||
             (ci == (95 :: Integer) ||
               (ci == (38 :: Integer) || ci == (45 :: Integer)))));

comment_error :: () -> [Arith.Char];
comment_error x =
  (error :: forall a. String -> (() -> a) -> a) "comment not terminated"
    (\ _ -> []);

comment_error_hyphen :: () -> [Arith.Char];
comment_error_hyphen x =
  (error :: forall a. String -> (() -> a) -> a) "double hyphen within comment"
    (\ _ -> []);

rc_open_1 :: [Arith.Char] -> [Arith.Char];
rc_open_1 [] = [];
rc_open_1 (c : cs) =
  (if Arith.integer_of_char c == (60 :: Integer) then rc_open_2 cs
    else c : rc_open_1 cs);

rc_close_3 :: [Arith.Char] -> [Arith.Char];
rc_close_3 [] = comment_error ();
rc_close_3 (c : cs) =
  (if Arith.integer_of_char c == (62 :: Integer) then rc_open_1 cs
    else comment_error_hyphen ());

rc_close_2 :: [Arith.Char] -> [Arith.Char];
rc_close_2 [] = comment_error ();
rc_close_2 (c : cs) =
  (if Arith.integer_of_char c == (45 :: Integer) then rc_close_3 cs
    else rc_close_1 cs);

rc_close_1 :: [Arith.Char] -> [Arith.Char];
rc_close_1 [] = comment_error ();
rc_close_1 (c : cs) =
  (if Arith.integer_of_char c == (45 :: Integer) then rc_close_2 cs
    else rc_close_1 cs);

rc_open_4 :: [Arith.Char] -> [Arith.Char];
rc_open_4 [] = [Arith.char_0x3C, Arith.char_0x21, Arith.char_0x2D];
rc_open_4 (c : cs) =
  let {
    ic = Arith.integer_of_char c;
  } in (if ic == (45 :: Integer) then rc_close_1 cs
         else (if ic == (60 :: Integer)
                then c : Arith.char_0x21 : Arith.char_0x2D : rc_open_2 cs
                else Arith.char_0x3C :
                       Arith.char_0x21 : Arith.char_0x2D : c : rc_open_1 cs));

rc_open_3 :: [Arith.Char] -> [Arith.Char];
rc_open_3 [] = [Arith.char_0x3C, Arith.char_0x21];
rc_open_3 (c : cs) =
  let {
    ic = Arith.integer_of_char c;
  } in (if ic == (45 :: Integer) then rc_open_4 cs
         else (if ic == (60 :: Integer) then c : Arith.char_0x21 : rc_open_2 cs
                else Arith.char_0x3C : Arith.char_0x21 : c : rc_open_1 cs));

rc_open_2 :: [Arith.Char] -> [Arith.Char];
rc_open_2 [] = [Arith.char_0x3C];
rc_open_2 (c : cs) =
  let {
    ic = Arith.integer_of_char c;
  } in (if ic == (33 :: Integer) then rc_open_3 cs
         else (if ic == (60 :: Integer) then c : rc_open_2 cs
                else Arith.char_0x3C : c : rc_open_1 cs));

remove_comments :: [Arith.Char] -> [Arith.Char];
remove_comments xs = rc_open_1 xs;

parse_header ::
  [Arith.Char] -> Sum_Type.Sum [Arith.Char] ([[Arith.Char]], [Arith.Char]);
parse_header ts =
  (if Arith.take (Arith.nat_of_integer (2 :: Integer)) (Parser_Monad.trim ts) ==
        [Arith.char_0x3C, Arith.char_0x3F]
    then Parser_Monad.bind
           (Parser_Monad.scan_upto [Arith.char_0x3F, Arith.char_0x3E])
           (\ h ->
             Parser_Monad.bind parse_header
               (\ hs -> Parser_Monad.returna (h : hs)))
           ts
    else Parser_Monad.bind Parser_Monad.spaces (\ _ -> Parser_Monad.returna [])
           ts);

parse_attribute_value ::
  [Arith.Char] -> Sum_Type.Sum [Arith.Char] ([Arith.Char], [Arith.Char]);
parse_attribute_value =
  Parser_Monad.bind (Parser_Monad.exactly [Arith.char_0x22])
    (\ _ ->
      Parser_Monad.bind
        (Parser_Monad.many (\ y -> not (Arith.equal_char Arith.char_0x22 y)))
        (\ v ->
          Parser_Monad.bind (Parser_Monad.exactly [Arith.char_0x22])
            (\ _ -> Parser_Monad.returna v)));

many_letters_main :: [Arith.Char] -> ([Arith.Char], [Arith.Char]);
many_letters_main [] = ([], []);
many_letters_main (c : cs) =
  (if is_letter c then (case many_letters_main cs of {
                         (ds, a) -> (c : ds, a);
                       })
    else ([], c : cs));

parse_name ::
  [Arith.Char] -> Sum_Type.Sum [Arith.Char] ([Arith.Char], [Arith.Char]);
parse_name s =
  (case many_letters_main s of {
    (n, ts) ->
      (if null n
        then Sum_Type.Inl
               ([Arith.char_0x65, Arith.char_0x78, Arith.char_0x70,
                  Arith.char_0x65, Arith.char_0x63, Arith.char_0x74,
                  Arith.char_0x65, Arith.char_0x64, Arith.char_0x20,
                  Arith.char_0x6C, Arith.char_0x65, Arith.char_0x74,
                  Arith.char_0x74, Arith.char_0x65, Arith.char_0x72,
                  Arith.char_0x20] ++
                 letters ++
                   [Arith.char_0x20, Arith.char_0x62, Arith.char_0x75,
                     Arith.char_0x74, Arith.char_0x20, Arith.char_0x66,
                     Arith.char_0x69, Arith.char_0x72, Arith.char_0x73,
                     Arith.char_0x74, Arith.char_0x20, Arith.char_0x73,
                     Arith.char_0x79, Arith.char_0x6D, Arith.char_0x62,
                     Arith.char_0x6F, Arith.char_0x6C, Arith.char_0x20,
                     Arith.char_0x69, Arith.char_0x73, Arith.char_0x20,
                     Arith.char_0x22] ++
                     Arith.take Arith.one_nat s ++ [Arith.char_0x22])
        else Sum_Type.Inr (n, Parser_Monad.trim ts));
  });

parse_attributes ::
  [Arith.Char] ->
    Sum_Type.Sum [Arith.Char] ([([Arith.Char], [Arith.Char])], [Arith.Char]);
parse_attributes [] = Sum_Type.Inr ([], []);
parse_attributes (c : s) =
  let {
    ic = Arith.integer_of_char c;
  } in (if ic == (47 :: Integer) || ic == (62 :: Integer)
         then Sum_Type.Inr ([], c : s)
         else Parser_Monad.bind parse_name
                (\ k ->
                  Parser_Monad.bind (Parser_Monad.exactly [Arith.char_0x3D])
                    (\ _ ->
                      Parser_Monad.bind parse_attribute_value
                        (\ v ->
                          Parser_Monad.bind parse_attributes
                            (\ atts -> Parser_Monad.returna ((k, v) : atts)))))
                (c : s));

oneof_closed ::
  [Arith.Char] -> Sum_Type.Sum [Arith.Char] ([Arith.Char], [Arith.Char]);
oneof_closed (x : xs) =
  (if Arith.equal_char x Arith.char_0x3E
    then Sum_Type.Inr ([Arith.char_0x3E], Parser_Monad.trim xs)
    else (if Arith.equal_char x Arith.char_0x2F &&
               (case xs of {
                 [] -> False;
                 y : _ -> Arith.equal_char y Arith.char_0x3E;
               })
           then Sum_Type.Inr
                  ([Arith.char_0x2F, Arith.char_0x3E],
                    Parser_Monad.trim (Arith.tla xs))
           else Parser_Monad.err_expecting
                  [Arith.char_0x6F, Arith.char_0x6E, Arith.char_0x65,
                    Arith.char_0x20, Arith.char_0x6F, Arith.char_0x66,
                    Arith.char_0x20, Arith.char_0x5B, Arith.char_0x2F,
                    Arith.char_0x3E, Arith.char_0x2C, Arith.char_0x20,
                    Arith.char_0x3E, Arith.char_0x5D]
                  (x : xs)));
oneof_closed [] =
  Parser_Monad.err_expecting
    [Arith.char_0x6F, Arith.char_0x6E, Arith.char_0x65, Arith.char_0x20,
      Arith.char_0x6F, Arith.char_0x66, Arith.char_0x20, Arith.char_0x5B,
      Arith.char_0x2F, Arith.char_0x3E, Arith.char_0x2C, Arith.char_0x20,
      Arith.char_0x3E, Arith.char_0x5D]
    [];

parse_text_main :: [Arith.Char] -> [Arith.Char] -> ([Arith.Char], [Arith.Char]);
parse_text_main [] res = ([], reverse (Parser_Monad.trim res));
parse_text_main (c : cs) res =
  (if Arith.integer_of_char c == (60 :: Integer)
    then (c : cs, reverse (Parser_Monad.trim res))
    else parse_text_main cs (c : res));

parse_text_impl ::
  forall a. [Arith.Char] -> Sum_Type.Sum a (Maybe [Arith.Char], [Arith.Char]);
parse_text_impl cs =
  (case parse_text_main (Parser_Monad.trim cs) [] of {
    (rem, txt) ->
      (if null txt then Sum_Type.Inr (Nothing, rem)
        else Sum_Type.Inr (Just txt, rem));
  });

parse_text ::
  [Arith.Char] -> Sum_Type.Sum [Arith.Char] (Maybe [Arith.Char], [Arith.Char]);
parse_text cs = parse_text_impl cs;

parse_nodes :: [Arith.Char] -> Sum_Type.Sum [Arith.Char] ([Xml], [Arith.Char]);
parse_nodes ts =
  (if null ts ||
        Arith.take (Arith.nat_of_integer (2 :: Integer)) ts ==
          [Arith.char_0x3C, Arith.char_0x2F]
    then Parser_Monad.returna [] ts
    else (if not (Arith.equal_char (Arith.hda ts) Arith.char_0x3C)
           then Parser_Monad.bind parse_text
                  (\ t ->
                    Parser_Monad.bind parse_nodes
                      (\ ns ->
                        Parser_Monad.returna (XML_text (Arith.the t) : ns)))
                  ts
           else Parser_Monad.bind (Parser_Monad.exactly [Arith.char_0x3C])
                  (\ _ ->
                    Parser_Monad.bind parse_name
                      (\ n ->
                        Parser_Monad.bind parse_attributes
                          (\ atts ->
                            Parser_Monad.bind oneof_closed
                              (\ e ->
                                (if e == [Arith.char_0x2F, Arith.char_0x3E]
                                  then Parser_Monad.bind parse_nodes
 (\ cs -> Parser_Monad.returna (XML n atts [] : cs))
                                  else Parser_Monad.bind parse_nodes
 (\ cs ->
   Parser_Monad.bind (Parser_Monad.exactly [Arith.char_0x3C, Arith.char_0x2F])
     (\ _ ->
       Parser_Monad.bind (Parser_Monad.exactly n)
         (\ _ ->
           Parser_Monad.bind (Parser_Monad.exactly [Arith.char_0x3E])
             (\ _ ->
               Parser_Monad.bind parse_nodes
                 (\ ns -> Parser_Monad.returna (XML n atts cs : ns)))))))))))
                  ts));

parse_node :: [Arith.Char] -> Sum_Type.Sum [Arith.Char] (Xml, [Arith.Char]);
parse_node =
  Parser_Monad.bind (Parser_Monad.exactly [Arith.char_0x3C])
    (\ _ ->
      Parser_Monad.bind parse_name
        (\ n ->
          Parser_Monad.bind parse_attributes
            (\ atts ->
              Parser_Monad.bind oneof_closed
                (\ e ->
                  (if e == [Arith.char_0x2F, Arith.char_0x3E]
                    then Parser_Monad.returna (XML n atts [])
                    else Parser_Monad.bind parse_nodes
                           (\ cs ->
                             Parser_Monad.bind
                               (Parser_Monad.exactly
                                 [Arith.char_0x3C, Arith.char_0x2F])
                               (\ _ ->
                                 Parser_Monad.bind (Parser_Monad.exactly n)
                                   (\ _ ->
                                     Parser_Monad.bind
                                       (Parser_Monad.exactly [Arith.char_0x3E])
                                       (\ _ ->
 Parser_Monad.returna (XML n atts cs))))))))));

parse_doc :: [Arith.Char] -> Sum_Type.Sum [Arith.Char] (Xmldoc, [Arith.Char]);
parse_doc =
  Parser_Monad.bind (Parser_Monad.update_tokens remove_comments)
    (\ _ ->
      Parser_Monad.bind parse_header
        (\ h ->
          Parser_Monad.bind parse_node
            (\ xml ->
              Parser_Monad.bind Parser_Monad.eoi
                (\ _ -> Parser_Monad.returna (XMLDOC h xml)))));

doc_of_string :: [Arith.Char] -> Sum_Type.Sum [Arith.Char] Xmldoc;
doc_of_string s =
  Error_Monad.bind (parse_doc s) (\ (doc, _) -> Sum_Type.Inr doc);

}
