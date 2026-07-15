{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Xmlt(Xml_error, bind2, xml_error, xml_do, xml_or, xml_return, xml_int,
        xml_take_nat, xml_nat, xml_take_text, xml_text, xml_bool, xml_leaf,
        xml_take, xml_foldl, xml_change, parse_xml_string, xml_take_default,
        xml_take_many_sub, xml_take_optional)
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
import qualified Extended_Nat;
import qualified Number_Parser;
import qualified Map;
import qualified HOL;
import qualified Term_Rewriting;
import qualified Xml;
import qualified Arith;
import qualified Strict_Sum;
import qualified Sum_Type;

data Xml_error a = TagMismatch [String] | Fatal a;

bind2 ::
  forall a b c d.
    Strict_Sum.Sum_bot a b ->
      (a -> Strict_Sum.Sum_bot c d) ->
        (b -> Strict_Sum.Sum_bot c d) -> Strict_Sum.Sum_bot c d;
bind2 (Strict_Sum.Sumbot a) f g = (case a of {
                                    Sum_Type.Inl aa -> f aa;
                                    Sum_Type.Inr aa -> g aa;
                                  });

xml_error ::
  forall a b c d.
    String ->
      ([Xml.Xml], (a, (b, (c, [String])))) ->
        Strict_Sum.Sum_bot (Xml_error String) d;
xml_error str x =
  (case x of {
    (xmls, (_, (_, (_, pos)))) ->
      let {
        next =
          (case xmls of {
            [] -> "tag close";
            Xml.XML tag _ _ : _ -> ("<" ++ Arith.implode tag) ++ ">";
            Xml.XML_text stra : _ ->
              ("text element \"" ++ Arith.implode stra) ++ "\"";
          });
      } in Strict_Sum.left
             (Fatal
               ((((("parse error on " ++ next) ++ " at ") ++
                   Term_Rewriting.default_showsl_list Term_Rewriting.showsl_lit
                     pos "") ++
                  ":\n") ++
                 str));
  });

mismatch ::
  forall a b.
    String ->
      ([Xml.Xml], (a, (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xml_error String) b;
mismatch tag x =
  (case x of {
    (_, (_, (True, (cands, _)))) -> Strict_Sum.left (TagMismatch (tag : cands));
    (_, (_, (False, (cands, _)))) ->
      xml_error
        ("expecting " ++
          Term_Rewriting.default_showsl_list Term_Rewriting.showsl_lit
            (tag : cands) "")
        x;
  });

xml_do ::
  forall a.
    String ->
      (([Xml.Xml],
         ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xml_error String) a) ->
        (Xml.Xml,
          ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
          Strict_Sum.Sum_bot (Xml_error String) a;
xml_do tag p x =
  (case x of {
    (Xml.XML nam atts xmls, (_, (_, (_, pos)))) ->
      (if nam == Arith.explode tag
        then p (xmls, (atts, (False, ([], tag : pos))))
        else mismatch tag ([fst x], snd x));
    (Xml.XML_text _, _) -> mismatch tag ([fst x], snd x);
  });

xml_or ::
  forall a b c d e f g.
    ((a, (b, (Bool, (c, d)))) -> Strict_Sum.Sum_bot (Xml_error e) f) ->
      ((a, (b, (g, ([String], d)))) -> Strict_Sum.Sum_bot (Xml_error e) f) ->
        (a, (b, (g, (c, d)))) -> Strict_Sum.Sum_bot (Xml_error e) f;
xml_or p1 p2 x =
  (case x of {
    (x1, (atts, (flag, (cands, rest)))) ->
      bind2 (p1 (x1, (atts, (True, (cands, rest)))))
        (\ a ->
          (case a of {
            TagMismatch cands1 -> p2 (x1, (atts, (flag, (cands1, rest))));
            Fatal aa -> Strict_Sum.left (Fatal aa);
          }))
        Strict_Sum.right;
  });

xml_take_int ::
  forall a.
    (Arith.Int ->
      ([Xml.Xml],
        ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xml_error String) a) ->
      ([Xml.Xml],
        ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xml_error String) a;
xml_take_int p xs =
  (case xs of {
    ([], _) -> xml_error "expecting an integer" xs;
    (Xml.XML _ _ _ : _, _) -> xml_error "expecting an integer" xs;
    (Xml.XML_text text : xmls, s) ->
      (case Number_Parser.int_of_string text of {
        Sum_Type.Inl x -> xml_error x xs;
        Sum_Type.Inr n -> p n (xmls, s);
      });
  });

xml_return ::
  forall a.
    a -> ([Xml.Xml],
           ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
           Strict_Sum.Sum_bot (Xml_error String) a;
xml_return v x = (case x of {
                   ([], _) -> Strict_Sum.right v;
                   (_ : _, _) -> xml_error "expecting tag close" x;
                 });

xml_int ::
  String ->
    (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
      Strict_Sum.Sum_bot (Xml_error String) Arith.Int;
xml_int tag = xml_do tag (xml_take_int xml_return);

xml_take_nat ::
  forall a.
    (Arith.Nat ->
      ([Xml.Xml],
        ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xml_error String) a) ->
      ([Xml.Xml],
        ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xml_error String) a;
xml_take_nat p xs =
  (case xs of {
    ([], _) -> xml_error "expecting a number" xs;
    (Xml.XML _ _ _ : _, _) -> xml_error "expecting a number" xs;
    (Xml.XML_text text : xmls, s) ->
      (case Number_Parser.nat_of_string text of {
        Sum_Type.Inl x -> xml_error x xs;
        Sum_Type.Inr n -> p n (xmls, s);
      });
  });

xml_nat ::
  String ->
    (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
      Strict_Sum.Sum_bot (Xml_error String) Arith.Nat;
xml_nat tag = xml_do tag (xml_take_nat xml_return);

bool_of_string :: [Arith.Char] -> Sum_Type.Sum String Bool;
bool_of_string s =
  (if s == [Arith.char_0x74, Arith.char_0x72, Arith.char_0x75, Arith.char_0x65]
    then Sum_Type.Inr True
    else (if s == [Arith.char_0x66, Arith.char_0x61, Arith.char_0x6C,
                    Arith.char_0x73, Arith.char_0x65]
           then Sum_Type.Inr False
           else Sum_Type.Inl
                  (("cannot convert \"" ++ Arith.implode s) ++
                    "\" into Boolean")));

xml_take_text ::
  forall a.
    ([Arith.Char] ->
      ([Xml.Xml],
        ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xml_error String) a) ->
      ([Xml.Xml],
        ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
        Strict_Sum.Sum_bot (Xml_error String) a;
xml_take_text p xs =
  (case xs of {
    ([], _) -> xml_error "expecting a text" xs;
    (Xml.XML _ _ _ : _, _) -> xml_error "expecting a text" xs;
    (Xml.XML_text text : xmls, s) -> p text (xmls, s);
  });

xml_text ::
  String ->
    (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
      Strict_Sum.Sum_bot (Xml_error String) [Arith.Char];
xml_text tag = xml_do tag (xml_take_text xml_return);

xml_bool ::
  String ->
    (Xml.Xml, ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
      Strict_Sum.Sum_bot (Xml_error String) Bool;
xml_bool tag x =
  bind2 (xml_text tag x) Strict_Sum.left
    (\ str -> (case bool_of_string str of {
                Sum_Type.Inl err -> xml_error err ([fst x], snd x);
                Sum_Type.Inr a -> Strict_Sum.right a;
              }));

xml_leaf ::
  forall a.
    String ->
      a -> (Xml.Xml,
             ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
             Strict_Sum.Sum_bot (Xml_error String) a;
xml_leaf tag ret = xml_do tag (xml_return ret);

xml_take ::
  forall a b.
    ((Xml.Xml,
       ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
      Strict_Sum.Sum_bot (Xml_error String) a) ->
      (a -> ([Xml.Xml],
              ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
              Strict_Sum.Sum_bot (Xml_error String) b) ->
        ([Xml.Xml],
          ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
          Strict_Sum.Sum_bot (Xml_error String) b;
xml_take p1 p2 x =
  (case x of {
    ([], rest) ->
      bind2 (p1 (Xml.XML [] [] [], rest)) Strict_Sum.left
        (\ _ -> Strict_Sum.left (Fatal "unexpected"));
    (xa : xs, (atts, (flag, (cands, rest)))) ->
      bind2 (p1 (xa, (atts, (flag, (cands, rest))))) Strict_Sum.left
        (\ a -> p2 a (xs, (atts, (False, ([], rest)))));
  });

xml_error_to_string :: Xml_error String -> [Arith.Char];
xml_error_to_string (Fatal e) = Arith.explode ("Fatal: " ++ e);
xml_error_to_string (TagMismatch e) =
  Arith.explode
    ("tag mismatch: " ++
      Term_Rewriting.default_showsl_list Term_Rewriting.showsl_lit e "");

parse_xml ::
  forall a.
    ((Xml.Xml,
       ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
      Strict_Sum.Sum_bot (Xml_error String) a) ->
      Xml.Xml -> Strict_Sum.Sum_bot [Arith.Char] a;
parse_xml p xml =
  bind2 (xml_take p xml_return ([xml], ([], (False, ([], [])))))
    (Strict_Sum.left . xml_error_to_string) Strict_Sum.right;

xml_foldl ::
  forall a b.
    (a -> (Xml.Xml,
            ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
            Strict_Sum.Sum_bot (Xml_error String) b) ->
      (a -> b -> a) ->
        a -> ([Xml.Xml],
               ([([Arith.Char], [Arith.Char])],
                 (Bool, ([String], [String])))) ->
               Strict_Sum.Sum_bot (Xml_error String) a;
xml_foldl p f a xs =
  (case xs of {
    ([], _) -> Strict_Sum.right a;
    (_ : _, _) -> xml_take (p a) (\ b -> xml_foldl p f (f a b)) xs;
  });

xml_change ::
  forall a b.
    ((Xml.Xml,
       ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
      Strict_Sum.Sum_bot (Xml_error String) a) ->
      (a -> ([Xml.Xml],
              ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
              Strict_Sum.Sum_bot (Xml_error String) b) ->
        (Xml.Xml,
          ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
          Strict_Sum.Sum_bot (Xml_error String) b;
xml_change p f x =
  bind2 (p x) Strict_Sum.left (\ a -> (case x of {
(_, rest) -> f a ([], rest);
                                      }));

special_map :: [Arith.Char] -> Maybe [Arith.Char];
special_map =
  Map.map_of
    [([Arith.char_0x71, Arith.char_0x75, Arith.char_0x6F, Arith.char_0x74],
       [Arith.char_0x22]),
      ([Arith.char_0x23, Arith.char_0x33, Arith.char_0x34], [Arith.char_0x22]),
      ([Arith.char_0x61, Arith.char_0x6D, Arith.char_0x70], [Arith.char_0x26]),
      ([Arith.char_0x23, Arith.char_0x33, Arith.char_0x38], [Arith.char_0x26]),
      ([Arith.char_0x61, Arith.char_0x70, Arith.char_0x6F, Arith.char_0x73],
        [Arith.char_0x27]),
      ([Arith.char_0x23, Arith.char_0x33, Arith.char_0x39], [Arith.char_0x27]),
      ([Arith.char_0x6C, Arith.char_0x74], [Arith.char_0x3C]),
      ([Arith.char_0x23, Arith.char_0x36, Arith.char_0x30], [Arith.char_0x3C]),
      ([Arith.char_0x67, Arith.char_0x74], [Arith.char_0x3E]),
      ([Arith.char_0x23, Arith.char_0x36, Arith.char_0x32], [Arith.char_0x3E])];

map_xml_text :: ([Arith.Char] -> [Arith.Char]) -> Xml.Xml -> Xml.Xml;
map_xml_text f (Xml.XML t asa cs) = Xml.XML t asa (map (map_xml_text f) cs);
map_xml_text f (Xml.XML_text txt) = Xml.XML_text (f txt);

extract_special ::
  [Arith.Char] -> [Arith.Char] -> Maybe ([Arith.Char], [Arith.Char]);
extract_special acc [] = Nothing;
extract_special acc (x : xs) =
  (if Arith.equal_char x Arith.char_0x3B
    then Arith.map_option (\ s -> (s, xs)) (special_map (reverse acc))
    else extract_special (x : acc) xs);

normalize_special :: [Arith.Char] -> [Arith.Char];
normalize_special [] = [];
normalize_special (x : xs) =
  (if Arith.equal_char x Arith.char_0x26
    then (case extract_special [] xs of {
           Nothing -> [Arith.char_0x26] ++ normalize_special xs;
           Just (spec, ys) -> spec ++ normalize_special ys;
         })
    else x : normalize_special xs);

parse_xml_string ::
  forall a.
    ((Xml.Xml,
       ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
      Strict_Sum.Sum_bot (Xml_error String) a) ->
      [Arith.Char] -> Strict_Sum.Sum_bot [Arith.Char] a;
parse_xml_string p str =
  (case Xml.doc_of_string str of {
    Sum_Type.Inl a -> Strict_Sum.left a;
    Sum_Type.Inr (Xml.XMLDOC _ xml) ->
      parse_xml p (map_xml_text normalize_special xml);
  });

xml_take_default ::
  forall a b.
    a -> ((Xml.Xml,
            ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
           Strict_Sum.Sum_bot (Xml_error String) a) ->
           (a -> ([Xml.Xml],
                   ([([Arith.Char], [Arith.Char])],
                     (Bool, ([String], [String])))) ->
                   Strict_Sum.Sum_bot (Xml_error String) b) ->
             ([Xml.Xml],
               ([([Arith.Char], [Arith.Char])],
                 (Bool, ([String], [String])))) ->
               Strict_Sum.Sum_bot (Xml_error String) b;
xml_take_default a p1 p2 xs =
  (case xs of {
    ([], _) -> p2 a xs;
    (xml : xmls, (atts, (allow, (cands, rest)))) ->
      bind2 (p1 (xml, (atts, (True, (cands, rest)))))
        (\ e ->
          (case e of {
            TagMismatch cands1 ->
              p2 a (xml : xmls, (atts, (allow, (cands1, rest))));
            Fatal _ -> Strict_Sum.left e;
          }))
        (\ aa -> p2 aa (xmls, (atts, (False, ([], rest)))));
  });

xml_take_many_sub ::
  forall a b.
    [a] ->
      Arith.Nat ->
        Extended_Nat.Enat ->
          ((Xml.Xml,
             ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
            Strict_Sum.Sum_bot (Xml_error String) a) ->
            ([a] ->
              ([Xml.Xml],
                ([([Arith.Char], [Arith.Char])],
                  (Bool, ([String], [String])))) ->
                Strict_Sum.Sum_bot (Xml_error String) b) ->
              ([Xml.Xml],
                ([([Arith.Char], [Arith.Char])],
                  (Bool, ([String], [String])))) ->
                Strict_Sum.Sum_bot (Xml_error String) b;
xml_take_many_sub acc minOccurs maxOccurs p1 p2 ([], (atts, (allow, rest))) =
  (if Arith.equal_nat minOccurs Arith.zero_nat
    then p2 (reverse acc) ([], (atts, (allow, rest)))
    else bind2 (p1 (Xml.XML [] [] [], (atts, (False, rest)))) Strict_Sum.left
           (\ _ -> Strict_Sum.left (Fatal "unexpected")));
xml_take_many_sub acc minOccurs maxOccurs p1 p2
  (xml : xmls, (atts, (allow, (cands, rest)))) =
  (if Extended_Nat.equal_enat maxOccurs Extended_Nat.zero_enat
    then p2 (reverse acc) (xml : xmls, (atts, (allow, (cands, rest))))
    else bind2 (p1 (xml, (atts,
                           (Arith.equal_nat minOccurs Arith.zero_nat,
                             (cands, rest)))))
           (\ e ->
             (case e of {
               TagMismatch _ ->
                 p2 (reverse acc) (xml : xmls, (atts, (allow, (cands, rest))));
               Fatal _ -> Strict_Sum.left e;
             }))
           (\ a ->
             xml_take_many_sub (a : acc)
               (Arith.minus_nat minOccurs Arith.one_nat)
               (Extended_Nat.minus_enat maxOccurs Extended_Nat.one_enat) p1 p2
               (xmls, (atts, (False, ([], rest))))));

xml_take_optional ::
  forall a b.
    ((Xml.Xml,
       ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
      Strict_Sum.Sum_bot (Xml_error String) a) ->
      (Maybe a ->
        ([Xml.Xml],
          ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
          Strict_Sum.Sum_bot (Xml_error String) b) ->
        ([Xml.Xml],
          ([([Arith.Char], [Arith.Char])], (Bool, ([String], [String])))) ->
          Strict_Sum.Sum_bot (Xml_error String) b;
xml_take_optional p1 p2 xs =
  (case xs of {
    ([], _) -> p2 Nothing xs;
    (xml : xmls, (atts, (allow, (cands, rest)))) ->
      bind2 (p1 (xml, (atts, (True, (cands, rest)))))
        (\ e ->
          (case e of {
            TagMismatch cands1 ->
              p2 Nothing (xml : xmls, (atts, (allow, (cands1, rest))));
            Fatal _ -> Strict_Sum.left e;
          }))
        (\ a -> p2 (Just a) (xmls, (atts, (False, ([], rest)))));
  });

}
