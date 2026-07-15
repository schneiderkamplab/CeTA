{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Term_More(showsl_term, showsl_terma, subt_at, hole_pos, mk_subst, var_poss,
             linear_term, funs_term_ms, subt_at_ctxt, funs_term_list,
             vars_term_list, funas_term_list, ctxt_of_pos_term,
             map_funs_term_wa, funas_args_term_list, showsl_actxta)
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
import qualified Multiset;
import qualified Term_Impl;
import qualified Set_Interval;
import qualified Complete_Lattices;
import qualified Phantom_Type;
import qualified Set;
import qualified Cardinality;
import qualified Collection_Enum;
import qualified Collection_Order;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Option;
import qualified Map;
import qualified Subterm_and_Context;
import qualified List;
import qualified Arith;
import qualified Term;
import qualified Shows_Literal;

showsl_term ::
  forall a b.
    (a -> String -> String) ->
      (b -> String -> String) -> Term.Term a b -> String -> String;
showsl_term fun var (Term.Var x) = var x;
showsl_term fun var (Term.Fun f ts) =
  fun f .
    Shows_Literal.showsl_list_gen id "" "(" ", " ")"
      (map (showsl_term fun var) ts);

showsl_terma ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => Term.Term a b -> String -> String;
showsl_terma t = showsl_term Shows_Literal.showsl Shows_Literal.showsl t;

showsl_list_term ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => [Term.Term a b] -> String -> String;
showsl_list_term xs = Shows_Literal.default_showsl_list showsl_terma xs;

instance (Shows_Literal.Showl a,
           Shows_Literal.Showl b) => Shows_Literal.Showl (Term.Term a b) where {
  showsl = showsl_terma;
  showsl_list = showsl_list_term;
};

subt_at :: forall a b. Term.Term a b -> [Arith.Nat] -> Term.Term a b;
subt_at s [] = s;
subt_at (Term.Fun f ss) (i : p) = subt_at (List.nth ss i) p;

hole_pos :: forall a b. Subterm_and_Context.Actxt a b -> [Arith.Nat];
hole_pos Subterm_and_Context.Hole = [];
hole_pos (Subterm_and_Context.More f ss d ts) = List.size_list ss : hole_pos d;

mk_subst ::
  forall a b c.
    (Eq a) => (a -> Term.Term b c) ->
                [(a, Term.Term b c)] -> a -> Term.Term b c;
mk_subst d xts = (\ x -> (case Map.map_of xts x of {
                           Nothing -> d x;
                           Just t -> t;
                         }));

var_poss :: forall a b. Term.Term a b -> Set.Set [Arith.Nat];
var_poss (Term.Var x) =
  Set.insert []
    (Set_Impl.set_empty (Phantom_Type.of_phantom Set_Impl.set_impl_list));
var_poss (Term.Fun f ts) =
  Complete_Lattices.sup_set
    (Set.image (\ i -> Set.image (\ a -> i : a) (var_poss (List.nth ts i)))
      (Set_Interval.atLeastLessThan Arith.zero_nat (List.size_list ts)));

linear_term ::
  forall a b.
    (Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Set_Impl.Set_impl b) => Term.Term a b -> Bool;
linear_term t = not (Option.is_none (Term_Impl.linear_term_impl Set.bot_set t));

funs_term_ms :: forall a b. (Eq a) => Term.Term a b -> Multiset.Multiset a;
funs_term_ms (Term.Var x) = Multiset.zero_multiset;
funs_term_ms (Term.Fun f ts) =
  Multiset.plus_multiset (Multiset.add_mset f Multiset.zero_multiset)
    (Multiset.sum_mset (Multiset.mset (map funs_term_ms ts)));

subt_at_ctxt ::
  forall a b.
    Subterm_and_Context.Actxt a (Term.Term a b) ->
      [Arith.Nat] -> Subterm_and_Context.Actxt a (Term.Term a b);
subt_at_ctxt c [] = c;
subt_at_ctxt (Subterm_and_Context.More f bef c aft) (i : p) = subt_at_ctxt c p;

showsl_actxt ::
  forall a b.
    (a -> String -> String) ->
      (b -> String -> String) ->
        Subterm_and_Context.Actxt a b -> String -> String;
showsl_actxt fun arg Subterm_and_Context.Hole = Shows_Literal.showsl_lit "[]";
showsl_actxt fun arg (Subterm_and_Context.More f ss1 d ss2) =
  (((fun f . Shows_Literal.showsl_literal "(") .
     Shows_Literal.showsl_list_gen arg "" "" ", " ", " ss1) .
    showsl_actxt fun arg d) .
    Shows_Literal.showsl_list_gen arg ")" ", " ", " ")" ss2;

funs_term_list :: forall a b. Term.Term a b -> [a];
funs_term_list t = Term_Impl.add_funs_term t [];

vars_term_list :: forall a b. Term.Term a b -> [b];
vars_term_list t = Term_Impl.add_vars_term t [];

funas_term_list :: forall a b. Term.Term a b -> [(a, Arith.Nat)];
funas_term_list (Term.Var uu) = [];
funas_term_list (Term.Fun f ts) =
  (f, List.size_list ts) : concatMap funas_term_list ts;

ctxt_of_pos_term ::
  forall a b.
    [Arith.Nat] -> Term.Term a b -> Subterm_and_Context.Actxt a (Term.Term a b);
ctxt_of_pos_term [] t = Subterm_and_Context.Hole;
ctxt_of_pos_term (i : ps) (Term.Fun f ts) =
  Subterm_and_Context.More f (List.take i ts)
    (ctxt_of_pos_term ps (List.nth ts i)) (List.drop (Arith.suc i) ts);

map_funs_term_wa ::
  forall a b c. ((a, Arith.Nat) -> b) -> Term.Term a c -> Term.Term b c;
map_funs_term_wa fg (Term.Var x) = Term.Var x;
map_funs_term_wa fg (Term.Fun f ts) =
  Term.Fun (fg (f, List.size_list ts)) (map (map_funs_term_wa fg) ts);

funas_args_term_list :: forall a b. Term.Term a b -> [(a, Arith.Nat)];
funas_args_term_list t = concatMap funas_term_list (Term.args t);

showsl_actxta ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => Subterm_and_Context.Actxt a b ->
                                  String -> String;
showsl_actxta t = showsl_actxt Shows_Literal.showsl Shows_Literal.showsl t;

}
