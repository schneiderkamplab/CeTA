{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Parser_Monad(err_expecting, eoi, bind, many, trim, returna, spaces, exactly,
                scan_upto, update_tokens)
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
import qualified List;
import qualified HOL;
import qualified Arith;
import qualified Product_Type;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Str;
import qualified Showa;

err_expecting ::
  forall a b.
    (Showa.Showa a) => [Str.Char] -> [a] -> Sum_Type.Sum [Str.Char] (b, [a]);
err_expecting msg ts =
  Sum_Type.Inl
    ([Str.char_0x65, Str.char_0x78, Str.char_0x70, Str.char_0x65, Str.char_0x63,
       Str.char_0x74, Str.char_0x69, Str.char_0x6E, Str.char_0x67,
       Str.char_0x20] ++
      msg ++
        [Str.char_0x2C, Str.char_0x20, Str.char_0x62, Str.char_0x75,
          Str.char_0x74, Str.char_0x20, Str.char_0x66, Str.char_0x6F,
          Str.char_0x75, Str.char_0x6E, Str.char_0x64, Str.char_0x3A,
          Str.char_0x20] ++
          Showa.shows_quote
            (Showa.shows_prec_list Arith.zero_nat
              (List.take (Arith.nat_of_integer (30 :: Integer)) ts))
            []);

eoi :: forall a. (Showa.Showa a) => [a] -> Sum_Type.Sum [Str.Char] ((), [a]);
eoi [] = Sum_Type.Inr ((), []);
eoi (v : va) =
  err_expecting
    [Str.char_0x65, Str.char_0x6E, Str.char_0x64, Str.char_0x20, Str.char_0x6F,
      Str.char_0x66, Str.char_0x20, Str.char_0x69, Str.char_0x6E, Str.char_0x70,
      Str.char_0x75, Str.char_0x74]
    (v : va);

bind ::
  forall a b c.
    ([a] -> Sum_Type.Sum [Str.Char] (b, [a])) ->
      (b -> [a] -> Sum_Type.Sum [Str.Char] (c, [a])) ->
        [a] -> Sum_Type.Sum [Str.Char] (c, [a]);
bind m f ts = Error_Monad.bind (m ts) (\ (a, b) -> f a b);

many ::
  (Str.Char -> Bool) ->
    [Str.Char] -> Sum_Type.Sum [Str.Char] ([Str.Char], [Str.Char]);
many p (t : ts) =
  (if p t
    then Error_Monad.bind (many p ts)
           (\ (rs, tsa) -> Sum_Type.Inr (t : rs, tsa))
    else Sum_Type.Inr ([], t : ts));
many p [] = Sum_Type.Inr ([], []);

trim :: [Str.Char] -> [Str.Char];
trim =
  dropWhile
    (\ c ->
      let {
        ci = Str.integer_of_char c;
      } in (if (34 :: Integer) <= ci then False
             else ci == (32 :: Integer) ||
                    (ci == (10 :: Integer) ||
                      (ci == (9 :: Integer) || ci == (13 :: Integer)))));

returna :: forall a b. a -> [b] -> Sum_Type.Sum [Str.Char] (a, [b]);
returna x = (\ ts -> Sum_Type.Inr (x, ts));

spaces :: [Str.Char] -> Sum_Type.Sum [Str.Char] ((), [Str.Char]);
spaces cs = Sum_Type.Inr ((), trim cs);

exactly_aux ::
  [Str.Char] ->
    [Str.Char] ->
      [Str.Char] ->
        [Str.Char] -> Sum_Type.Sum [Str.Char] ([Str.Char], [Str.Char]);
exactly_aux s i (x : xs) (y : ys) =
  (if Str.equal_char x y then exactly_aux s i xs ys
    else err_expecting ([Str.char_0x22] ++ s ++ [Str.char_0x22]) i);
exactly_aux s i [] xs = Sum_Type.Inr (s, trim xs);
exactly_aux s i (x : xs) [] =
  err_expecting ([Str.char_0x22] ++ s ++ [Str.char_0x22]) i;

exactly ::
  [Str.Char] -> [Str.Char] -> Sum_Type.Sum [Str.Char] ([Str.Char], [Str.Char]);
exactly s x = exactly_aux s x s x;

scan_upto ::
  [Str.Char] -> [Str.Char] -> Sum_Type.Sum [Str.Char] ([Str.Char], [Str.Char]);
scan_upto end (t : ts) =
  (if map snd (zip end (t : ts)) == end
    then Sum_Type.Inr (end, List.drop (List.size_list end) (t : ts))
    else Error_Monad.bind (scan_upto end ts)
           (\ (res, tsa) -> Sum_Type.Inr (t : res, tsa)));
scan_upto end [] =
  Sum_Type.Inl
    ([Str.char_0x64, Str.char_0x69, Str.char_0x64, Str.char_0x20, Str.char_0x6E,
       Str.char_0x6F, Str.char_0x74, Str.char_0x20, Str.char_0x66,
       Str.char_0x69, Str.char_0x6E, Str.char_0x64, Str.char_0x20,
       Str.char_0x65, Str.char_0x6E, Str.char_0x64, Str.char_0x2D,
       Str.char_0x6D, Str.char_0x61, Str.char_0x72, Str.char_0x6B,
       Str.char_0x65, Str.char_0x72, Str.char_0x20] ++
      Showa.shows_quote (Showa.shows_prec_list Arith.zero_nat end) []);

update_tokens ::
  forall a. ([a] -> [a]) -> [a] -> Sum_Type.Sum [Str.Char] ([a], [a]);
update_tokens f ts = Sum_Type.Inr (ts, f ts);

}
