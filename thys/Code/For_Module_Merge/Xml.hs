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
import qualified Option;
import qualified Product_Type;
import qualified List;
import qualified Parser_Monad;
import qualified Sum_Type;
import qualified Showa;
import qualified HOL;
import qualified Arith;
import qualified Str;

data Xml = XML [Str.Char] [([Str.Char], [Str.Char])] [Xml]
  | XML_text [Str.Char];

data Xmldoc = XMLDOC [[Str.Char]] Xml;

letters :: [Str.Char];
letters =
  [Str.char_0x61, Str.char_0x62, Str.char_0x63, Str.char_0x64, Str.char_0x65,
    Str.char_0x66, Str.char_0x67, Str.char_0x68, Str.char_0x69, Str.char_0x6A,
    Str.char_0x6B, Str.char_0x6C, Str.char_0x6D, Str.char_0x6E, Str.char_0x6F,
    Str.char_0x70, Str.char_0x71, Str.char_0x72, Str.char_0x73, Str.char_0x74,
    Str.char_0x75, Str.char_0x76, Str.char_0x77, Str.char_0x78, Str.char_0x79,
    Str.char_0x7A, Str.char_0x41, Str.char_0x42, Str.char_0x43, Str.char_0x44,
    Str.char_0x45, Str.char_0x46, Str.char_0x47, Str.char_0x48, Str.char_0x49,
    Str.char_0x4A, Str.char_0x4B, Str.char_0x4C, Str.char_0x4D, Str.char_0x4E,
    Str.char_0x4F, Str.char_0x50, Str.char_0x51, Str.char_0x52, Str.char_0x53,
    Str.char_0x54, Str.char_0x55, Str.char_0x56, Str.char_0x57, Str.char_0x58,
    Str.char_0x59, Str.char_0x5A, Str.char_0x5F, Str.char_0x30, Str.char_0x31,
    Str.char_0x32, Str.char_0x33, Str.char_0x34, Str.char_0x35, Str.char_0x36,
    Str.char_0x37, Str.char_0x38, Str.char_0x39, Str.char_0x26, Str.char_0x3B,
    Str.char_0x3A, Str.char_0x2D];

is_letter :: Str.Char -> Bool;
is_letter c =
  let {
    ci = Str.integer_of_char c;
  } in (97 :: Integer) <= ci && ci <= (122 :: Integer) ||
         ((65 :: Integer) <= ci && ci <= (90 :: Integer) ||
           ((48 :: Integer) <= ci && ci <= (59 :: Integer) ||
             (ci == (95 :: Integer) ||
               (ci == (38 :: Integer) || ci == (45 :: Integer)))));

comment_error :: () -> [Str.Char];
comment_error x =
  (error :: forall a. String -> (() -> a) -> a) "comment not terminated"
    (\ _ -> []);

comment_error_hyphen :: () -> [Str.Char];
comment_error_hyphen x =
  (error :: forall a. String -> (() -> a) -> a) "double hyphen within comment"
    (\ _ -> []);

rc_open_1 :: [Str.Char] -> [Str.Char];
rc_open_1 [] = [];
rc_open_1 (c : cs) =
  (if Str.integer_of_char c == (60 :: Integer) then rc_open_2 cs
    else c : rc_open_1 cs);

rc_close_3 :: [Str.Char] -> [Str.Char];
rc_close_3 [] = comment_error ();
rc_close_3 (c : cs) =
  (if Str.integer_of_char c == (62 :: Integer) then rc_open_1 cs
    else comment_error_hyphen ());

rc_close_2 :: [Str.Char] -> [Str.Char];
rc_close_2 [] = comment_error ();
rc_close_2 (c : cs) =
  (if Str.integer_of_char c == (45 :: Integer) then rc_close_3 cs
    else rc_close_1 cs);

rc_close_1 :: [Str.Char] -> [Str.Char];
rc_close_1 [] = comment_error ();
rc_close_1 (c : cs) =
  (if Str.integer_of_char c == (45 :: Integer) then rc_close_2 cs
    else rc_close_1 cs);

rc_open_4 :: [Str.Char] -> [Str.Char];
rc_open_4 [] = [Str.char_0x3C, Str.char_0x21, Str.char_0x2D];
rc_open_4 (c : cs) =
  let {
    ic = Str.integer_of_char c;
  } in (if ic == (45 :: Integer) then rc_close_1 cs
         else (if ic == (60 :: Integer)
                then c : Str.char_0x21 : Str.char_0x2D : rc_open_2 cs
                else Str.char_0x3C :
                       Str.char_0x21 : Str.char_0x2D : c : rc_open_1 cs));

rc_open_3 :: [Str.Char] -> [Str.Char];
rc_open_3 [] = [Str.char_0x3C, Str.char_0x21];
rc_open_3 (c : cs) =
  let {
    ic = Str.integer_of_char c;
  } in (if ic == (45 :: Integer) then rc_open_4 cs
         else (if ic == (60 :: Integer) then c : Str.char_0x21 : rc_open_2 cs
                else Str.char_0x3C : Str.char_0x21 : c : rc_open_1 cs));

rc_open_2 :: [Str.Char] -> [Str.Char];
rc_open_2 [] = [Str.char_0x3C];
rc_open_2 (c : cs) =
  let {
    ic = Str.integer_of_char c;
  } in (if ic == (33 :: Integer) then rc_open_3 cs
         else (if ic == (60 :: Integer) then c : rc_open_2 cs
                else Str.char_0x3C : c : rc_open_1 cs));

remove_comments :: [Str.Char] -> [Str.Char];
remove_comments xs = rc_open_1 xs;

parse_header ::
  [Str.Char] -> Sum_Type.Sum [Str.Char] ([[Str.Char]], [Str.Char]);
parse_header ts =
  (if List.take (Arith.nat_of_integer (2 :: Integer)) (Parser_Monad.trim ts) ==
        [Str.char_0x3C, Str.char_0x3F]
    then Parser_Monad.bind
           (Parser_Monad.scan_upto [Str.char_0x3F, Str.char_0x3E])
           (\ h ->
             Parser_Monad.bind parse_header
               (\ hs -> Parser_Monad.returna (h : hs)))
           ts
    else Parser_Monad.bind Parser_Monad.spaces (\ _ -> Parser_Monad.returna [])
           ts);

parse_attribute_value ::
  [Str.Char] -> Sum_Type.Sum [Str.Char] ([Str.Char], [Str.Char]);
parse_attribute_value =
  Parser_Monad.bind (Parser_Monad.exactly [Str.char_0x22])
    (\ _ ->
      Parser_Monad.bind
        (Parser_Monad.many (\ y -> not (Str.equal_char Str.char_0x22 y)))
        (\ v ->
          Parser_Monad.bind (Parser_Monad.exactly [Str.char_0x22])
            (\ _ -> Parser_Monad.returna v)));

many_letters_main :: [Str.Char] -> ([Str.Char], [Str.Char]);
many_letters_main [] = ([], []);
many_letters_main (c : cs) =
  (if is_letter c then (case many_letters_main cs of {
                         (ds, a) -> (c : ds, a);
                       })
    else ([], c : cs));

parse_name :: [Str.Char] -> Sum_Type.Sum [Str.Char] ([Str.Char], [Str.Char]);
parse_name s =
  (case many_letters_main s of {
    (n, ts) ->
      (if null n
        then Sum_Type.Inl
               ([Str.char_0x65, Str.char_0x78, Str.char_0x70, Str.char_0x65,
                  Str.char_0x63, Str.char_0x74, Str.char_0x65, Str.char_0x64,
                  Str.char_0x20, Str.char_0x6C, Str.char_0x65, Str.char_0x74,
                  Str.char_0x74, Str.char_0x65, Str.char_0x72, Str.char_0x20] ++
                 letters ++
                   [Str.char_0x20, Str.char_0x62, Str.char_0x75, Str.char_0x74,
                     Str.char_0x20, Str.char_0x66, Str.char_0x69, Str.char_0x72,
                     Str.char_0x73, Str.char_0x74, Str.char_0x20, Str.char_0x73,
                     Str.char_0x79, Str.char_0x6D, Str.char_0x62, Str.char_0x6F,
                     Str.char_0x6C, Str.char_0x20, Str.char_0x69, Str.char_0x73,
                     Str.char_0x20, Str.char_0x22] ++
                     List.take Arith.one_nat s ++ [Str.char_0x22])
        else Sum_Type.Inr (n, Parser_Monad.trim ts));
  });

parse_attributes ::
  [Str.Char] ->
    Sum_Type.Sum [Str.Char] ([([Str.Char], [Str.Char])], [Str.Char]);
parse_attributes [] = Sum_Type.Inr ([], []);
parse_attributes (c : s) =
  let {
    ic = Str.integer_of_char c;
  } in (if ic == (47 :: Integer) || ic == (62 :: Integer)
         then Sum_Type.Inr ([], c : s)
         else Parser_Monad.bind parse_name
                (\ k ->
                  Parser_Monad.bind (Parser_Monad.exactly [Str.char_0x3D])
                    (\ _ ->
                      Parser_Monad.bind parse_attribute_value
                        (\ v ->
                          Parser_Monad.bind parse_attributes
                            (\ atts -> Parser_Monad.returna ((k, v) : atts)))))
                (c : s));

oneof_closed :: [Str.Char] -> Sum_Type.Sum [Str.Char] ([Str.Char], [Str.Char]);
oneof_closed (x : xs) =
  (if Str.equal_char x Str.char_0x3E
    then Sum_Type.Inr ([Str.char_0x3E], Parser_Monad.trim xs)
    else (if Str.equal_char x Str.char_0x2F &&
               (case xs of {
                 [] -> False;
                 y : _ -> Str.equal_char y Str.char_0x3E;
               })
           then Sum_Type.Inr
                  ([Str.char_0x2F, Str.char_0x3E],
                    Parser_Monad.trim (List.tl xs))
           else Parser_Monad.err_expecting
                  [Str.char_0x6F, Str.char_0x6E, Str.char_0x65, Str.char_0x20,
                    Str.char_0x6F, Str.char_0x66, Str.char_0x20, Str.char_0x5B,
                    Str.char_0x2F, Str.char_0x3E, Str.char_0x2C, Str.char_0x20,
                    Str.char_0x3E, Str.char_0x5D]
                  (x : xs)));
oneof_closed [] =
  Parser_Monad.err_expecting
    [Str.char_0x6F, Str.char_0x6E, Str.char_0x65, Str.char_0x20, Str.char_0x6F,
      Str.char_0x66, Str.char_0x20, Str.char_0x5B, Str.char_0x2F, Str.char_0x3E,
      Str.char_0x2C, Str.char_0x20, Str.char_0x3E, Str.char_0x5D]
    [];

parse_text_main :: [Str.Char] -> [Str.Char] -> ([Str.Char], [Str.Char]);
parse_text_main [] res = ([], reverse (Parser_Monad.trim res));
parse_text_main (c : cs) res =
  (if Str.integer_of_char c == (60 :: Integer)
    then (c : cs, reverse (Parser_Monad.trim res))
    else parse_text_main cs (c : res));

parse_text_impl ::
  forall a. [Str.Char] -> Sum_Type.Sum a (Maybe [Str.Char], [Str.Char]);
parse_text_impl cs =
  (case parse_text_main (Parser_Monad.trim cs) [] of {
    (rem, txt) ->
      (if null txt then Sum_Type.Inr (Nothing, rem)
        else Sum_Type.Inr (Just txt, rem));
  });

parse_text ::
  [Str.Char] -> Sum_Type.Sum [Str.Char] (Maybe [Str.Char], [Str.Char]);
parse_text cs = parse_text_impl cs;

parse_nodes :: [Str.Char] -> Sum_Type.Sum [Str.Char] ([Xml], [Str.Char]);
parse_nodes ts =
  (if null ts ||
        List.take (Arith.nat_of_integer (2 :: Integer)) ts ==
          [Str.char_0x3C, Str.char_0x2F]
    then Parser_Monad.returna [] ts
    else (if not (Str.equal_char (List.hd ts) Str.char_0x3C)
           then Parser_Monad.bind parse_text
                  (\ t ->
                    Parser_Monad.bind parse_nodes
                      (\ ns ->
                        Parser_Monad.returna (XML_text (Option.the t) : ns)))
                  ts
           else Parser_Monad.bind (Parser_Monad.exactly [Str.char_0x3C])
                  (\ _ ->
                    Parser_Monad.bind parse_name
                      (\ n ->
                        Parser_Monad.bind parse_attributes
                          (\ atts ->
                            Parser_Monad.bind oneof_closed
                              (\ e ->
                                (if e == [Str.char_0x2F, Str.char_0x3E]
                                  then Parser_Monad.bind parse_nodes
 (\ cs -> Parser_Monad.returna (XML n atts [] : cs))
                                  else Parser_Monad.bind parse_nodes
 (\ cs ->
   Parser_Monad.bind (Parser_Monad.exactly [Str.char_0x3C, Str.char_0x2F])
     (\ _ ->
       Parser_Monad.bind (Parser_Monad.exactly n)
         (\ _ ->
           Parser_Monad.bind (Parser_Monad.exactly [Str.char_0x3E])
             (\ _ ->
               Parser_Monad.bind parse_nodes
                 (\ ns -> Parser_Monad.returna (XML n atts cs : ns)))))))))))
                  ts));

parse_node :: [Str.Char] -> Sum_Type.Sum [Str.Char] (Xml, [Str.Char]);
parse_node =
  Parser_Monad.bind (Parser_Monad.exactly [Str.char_0x3C])
    (\ _ ->
      Parser_Monad.bind parse_name
        (\ n ->
          Parser_Monad.bind parse_attributes
            (\ atts ->
              Parser_Monad.bind oneof_closed
                (\ e ->
                  (if e == [Str.char_0x2F, Str.char_0x3E]
                    then Parser_Monad.returna (XML n atts [])
                    else Parser_Monad.bind parse_nodes
                           (\ cs ->
                             Parser_Monad.bind
                               (Parser_Monad.exactly
                                 [Str.char_0x3C, Str.char_0x2F])
                               (\ _ ->
                                 Parser_Monad.bind (Parser_Monad.exactly n)
                                   (\ _ ->
                                     Parser_Monad.bind
                                       (Parser_Monad.exactly [Str.char_0x3E])
                                       (\ _ ->
 Parser_Monad.returna (XML n atts cs))))))))));

parse_doc :: [Str.Char] -> Sum_Type.Sum [Str.Char] (Xmldoc, [Str.Char]);
parse_doc =
  Parser_Monad.bind (Parser_Monad.update_tokens remove_comments)
    (\ _ ->
      Parser_Monad.bind parse_header
        (\ h ->
          Parser_Monad.bind parse_node
            (\ xml ->
              Parser_Monad.bind Parser_Monad.eoi
                (\ _ -> Parser_Monad.returna (XMLDOC h xml)))));

doc_of_string :: [Str.Char] -> Sum_Type.Sum [Str.Char] Xmldoc;
doc_of_string s =
  Error_Monad.bind (parse_doc s) (\ (doc, _) -> Sum_Type.Inr doc);

}
