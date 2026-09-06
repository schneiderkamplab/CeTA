{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module GM04_Complete_Transformation(gm04_top_pairs, gm04_non_top_rules) where {

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
import qualified HOL;
import qualified Name;
import qualified Term_Rewriting;
import qualified Arith;

gm04_vars :: forall a. Arith.Nat -> [Term_Rewriting.Term a [Arith.Char]];
gm04_vars n = map Term_Rewriting.Var (Name.x_1_to_x_n n);

gm04_ok_rule ::
  forall a.
    a -> a -> (a, Arith.Nat) ->
                (Term_Rewriting.Term a [Arith.Char],
                  Term_Rewriting.Term a [Arith.Char]);
gm04_ok_rule proper ok fn =
  let {
    f = fst fn;
    n = snd fn;
    xs = gm04_vars n;
  } in (if Arith.equal_nat n Arith.zero_nat
         then (Term_Rewriting.Fun proper [Term_Rewriting.Fun f []],
                Term_Rewriting.Fun ok [Term_Rewriting.Fun f []])
         else (Term_Rewriting.Fun f (map (\ x -> Term_Rewriting.Fun ok [x]) xs),
                Term_Rewriting.Fun ok [Term_Rewriting.Fun f xs]));

gm04_mark_rule ::
  forall a.
    a -> (a, Arith.Nat) ->
           Arith.Nat ->
             (Term_Rewriting.Term a [Arith.Char],
               Term_Rewriting.Term a [Arith.Char]);
gm04_mark_rule mark fn i =
  let {
    f = fst fn;
    n = snd fn;
    xs = gm04_vars n;
  } in (Term_Rewriting.Fun f
          (Arith.list_update xs i (Term_Rewriting.Fun mark [Arith.nth xs i])),
         Term_Rewriting.Fun mark [Term_Rewriting.Fun f xs]);

gm04_top_pairs ::
  forall a.
    a -> a -> a -> a -> a -> [(Term_Rewriting.Term a [Arith.Char],
                                Term_Rewriting.Term a [Arith.Char])];
gm04_top_pairs active mark proper ok top_sharp =
  [(Term_Rewriting.Fun top_sharp
      [Term_Rewriting.Fun ok
         [Term_Rewriting.Var
            [Arith.char_0x5F, Arith.char_0x5F, Arith.char_0x67, Arith.char_0x6D,
              Arith.char_0x30, Arith.char_0x34, Arith.char_0x5F,
              Arith.char_0x78]]],
     Term_Rewriting.Fun top_sharp
       [Term_Rewriting.Fun active
          [Term_Rewriting.Var
             [Arith.char_0x5F, Arith.char_0x5F, Arith.char_0x67,
               Arith.char_0x6D, Arith.char_0x30, Arith.char_0x34,
               Arith.char_0x5F, Arith.char_0x78]]]),
    (Term_Rewriting.Fun top_sharp
       [Term_Rewriting.Fun mark
          [Term_Rewriting.Var
             [Arith.char_0x5F, Arith.char_0x5F, Arith.char_0x67,
               Arith.char_0x6D, Arith.char_0x30, Arith.char_0x34,
               Arith.char_0x5F, Arith.char_0x78]]],
      Term_Rewriting.Fun top_sharp
        [Term_Rewriting.Fun proper
           [Term_Rewriting.Var
              [Arith.char_0x5F, Arith.char_0x5F, Arith.char_0x67,
                Arith.char_0x6D, Arith.char_0x30, Arith.char_0x34,
                Arith.char_0x5F, Arith.char_0x78]]])];

gm04_mark_rules ::
  forall a.
    ((a, Arith.Nat) -> Arith.Set Arith.Nat) ->
      a -> [(a, Arith.Nat)] ->
             [(Term_Rewriting.Term a [Arith.Char],
                Term_Rewriting.Term a [Arith.Char])];
gm04_mark_rules mu mark f =
  concatMap
    (\ fn ->
      Arith.map_filter
        (\ x ->
          (if Arith.less_nat x (snd fn) then Just (gm04_mark_rule mark fn x)
            else Nothing))
        (Arith.sorted_list_of_set (mu fn)))
    f;

gm04_active_rule ::
  forall a.
    a -> (a, Arith.Nat) ->
           Arith.Nat ->
             (Term_Rewriting.Term a [Arith.Char],
               Term_Rewriting.Term a [Arith.Char]);
gm04_active_rule active fn i =
  let {
    f = fst fn;
    n = snd fn;
    xs = gm04_vars n;
  } in (Term_Rewriting.Fun active [Term_Rewriting.Fun f xs],
         Term_Rewriting.Fun f
           (Arith.list_update xs i
             (Term_Rewriting.Fun active [Arith.nth xs i])));

gm04_proper_rule ::
  forall a.
    a -> a -> (a, Arith.Nat) ->
                (Term_Rewriting.Term a [Arith.Char],
                  Term_Rewriting.Term a [Arith.Char]);
gm04_proper_rule proper ok fn =
  let {
    f = fst fn;
    n = snd fn;
    xs = gm04_vars n;
  } in (if Arith.equal_nat n Arith.zero_nat
         then (Term_Rewriting.Fun proper [Term_Rewriting.Fun f []],
                Term_Rewriting.Fun ok [Term_Rewriting.Fun f []])
         else (Term_Rewriting.Fun proper [Term_Rewriting.Fun f xs],
                Term_Rewriting.Fun f
                  (map (\ x -> Term_Rewriting.Fun proper [x]) xs)));

gm04_active_rules ::
  forall a.
    ((a, Arith.Nat) -> Arith.Set Arith.Nat) ->
      a -> [(a, Arith.Nat)] ->
             [(Term_Rewriting.Term a [Arith.Char],
                Term_Rewriting.Term a [Arith.Char])];
gm04_active_rules mu active f =
  concatMap
    (\ fn ->
      Arith.map_filter
        (\ x ->
          (if Arith.less_nat x (snd fn) then Just (gm04_active_rule active fn x)
            else Nothing))
        (Arith.sorted_list_of_set (mu fn)))
    f;

gm04_source_rules ::
  forall a b c d.
    a -> b -> [(Term_Rewriting.Term a c, Term_Rewriting.Term b d)] ->
                [(Term_Rewriting.Term a c, Term_Rewriting.Term b d)];
gm04_source_rules active mark r =
  map (\ (l, ra) ->
        (Term_Rewriting.Fun active [l], Term_Rewriting.Fun mark [ra]))
    r;

gm04_non_top_rules ::
  forall a.
    ((a, Arith.Nat) -> Arith.Set Arith.Nat) ->
      a -> a -> a -> a -> [(a, Arith.Nat)] ->
                            [(Term_Rewriting.Term a [Arith.Char],
                               Term_Rewriting.Term a [Arith.Char])] ->
                              [(Term_Rewriting.Term a [Arith.Char],
                                 Term_Rewriting.Term a [Arith.Char])];
gm04_non_top_rules mu active mark proper ok f r =
  gm04_source_rules active mark r ++
    gm04_active_rules mu active f ++
      gm04_mark_rules mu mark f ++
        map (gm04_proper_rule proper ok) f ++
          Arith.map_filter
            (\ x ->
              (if Arith.less_nat Arith.zero_nat (snd x)
                then Just (gm04_ok_rule proper ok x) else Nothing))
            f;

}
