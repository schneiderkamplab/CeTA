{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Term_Impl(comparator_term, compare_term, in_poss, mk_subst_domain, subst_eq,
             poss_list, supt_impl, supteq_list, supt_list, check_supt,
             check_no_var, check_supteq, add_funs_term, add_vars_term,
             subst_compose_impl, commutes_impl, fun_poss_list, mk_subst_case,
             var_poss_list, add_funas_term, range_vars_impl, vars_subst_impl,
             check_funas_term, insert_vars_term, is_renaming_impl,
             linear_term_impl, subst_power_impl, check_ground_term,
             check_linear_term, contains_var_term, flatten_term_enum,
             insert_funas_term, subst_replace_impl, add_funas_args_term,
             subst_compose_impla, insert_funas_args_term,
             is_inverse_renaming_impl)
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
import qualified Missing_List;
import qualified Option;
import qualified Error_Monad;
import qualified Compare_Instances;
import qualified Term_More;
import qualified Check_Monad;
import qualified Sum_Type;
import qualified Shows_Literal;
import qualified Product_Type;
import qualified HOL;
import qualified Set;
import qualified Collection_Order;
import qualified Collection_Enum;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Container_Setup;
import qualified List;
import qualified Arith;
import qualified Quasi_Order;
import qualified Comparator;
import qualified Term;
import qualified Compare;
import qualified Orderings;

comparator_term ::
  forall a b.
    (a -> a -> Comparator.Order) ->
      (b -> b -> Comparator.Order) ->
        Term.Term a b -> Term.Term a b -> Comparator.Order;
comparator_term comp_f comp_v (Term.Var x) (Term.Var y) = comp_v x y;
comparator_term comp_f comp_v (Term.Var x) (Term.Fun ya yb) = Comparator.Lt;
comparator_term comp_f comp_v (Term.Fun x xa) (Term.Var y) = Comparator.Gt;
comparator_term comp_f comp_v (Term.Fun x xa) (Term.Fun ya yb) =
  (case comp_f x ya of {
    Comparator.Eqa ->
      Compare_Instances.comparator_list (comparator_term comp_f comp_v) xa yb;
    Comparator.Lt -> Comparator.Lt;
    Comparator.Gt -> Comparator.Gt;
  });

compare_term ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => Term.Term a b -> Term.Term a b -> Comparator.Order;
compare_term = comparator_term Compare.compare Compare.compare;

less_eq_term ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => Term.Term a b -> Term.Term a b -> Bool;
less_eq_term = Comparator.le_of_comp compare_term;

less_term ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => Term.Term a b -> Term.Term a b -> Bool;
less_term = Comparator.lt_of_comp compare_term;

instance (Compare.Compare a,
           Compare.Compare b) => Orderings.Ord (Term.Term a b) where {
  less_eq = less_eq_term;
  less = less_term;
};

instance (Compare.Compare a,
           Compare.Compare b) => Compare.Compare (Term.Term a b) where {
  compare = compare_term;
};

instance (Compare.Compare a,
           Compare.Compare b) => Quasi_Order.Quasi_order (Term.Term a b) where {
};

instance (Compare.Compare a,
           Compare.Compare b) => Quasi_Order.Weak_order (Term.Term a b) where {
};

instance (Compare.Compare a,
           Compare.Compare b) => Orderings.Preorder (Term.Term a b) where {
};

instance (Compare.Compare a,
           Compare.Compare b) => Orderings.Order (Term.Term a b) where {
};

instance (Compare.Compare a,
           Compare.Compare b) => Orderings.Linorder (Term.Term a b) where {
};

instance (Compare.Compare a,
           Compare.Compare b) => Compare.Compare_order (Term.Term a b) where {
};

in_poss :: forall a b. [Arith.Nat] -> Term.Term a b -> Bool;
in_poss [] uu = True;
in_poss (i : p) (Term.Fun f ts) =
  Arith.less_nat i (List.size_list ts) && in_poss p (List.nth ts i);
in_poss (i : p) (Term.Var uv) = False;

mk_subst_domain ::
  forall a b. (Eq a, Eq b) => [(a, Term.Term b a)] -> [(a, Term.Term b a)];
mk_subst_domain sigma =
  let {
    tau = Term_More.mk_subst Term.Var sigma;
  } in filter (\ (x, t) -> not (Term.equal_term (Term.Var x) t))
         (map (\ x -> (x, tau x)) (List.remdups (map fst sigma)));

subst_eq ::
  forall a b.
    (Collection_Enum.Cenum a, Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Compare.Compare a, Eq a, Set_Impl.Set_impl a, Compare.Compare b,
      Eq b) => [(a, Term.Term b a)] -> [(a, Term.Term b a)] -> Bool;
subst_eq sigma tau =
  let {
    sigmaa = mk_subst_domain sigma;
    taua = mk_subst_domain tau;
  } in Collection_Eq.set_eq (List.set sigmaa) (List.set taua);

poss_list :: forall a b. Term.Term a b -> [[Arith.Nat]];
poss_list (Term.Var x) = [[]];
poss_list (Term.Fun f ss) =
  [] : concatMap (\ (i, a) -> map (\ aa -> i : aa) a)
         (zip (List.upt Arith.zero_nat (List.size_list ss)) (map poss_list ss));

supt_impl :: forall a b. (Eq a, Eq b) => Term.Term a b -> Term.Term a b -> Bool;
supt_impl (Term.Var x) t = False;
supt_impl (Term.Fun f ss) t = List.member ss t || any (\ s -> supt_impl s t) ss;

supteq_list :: forall a b. Term.Term a b -> [Term.Term a b];
supteq_list (Term.Var x) = [Term.Var x];
supteq_list (Term.Fun f ts) = Term.Fun f ts : concatMap supteq_list ts;

supt_list :: forall a b. Term.Term a b -> [Term.Term a b];
supt_list (Term.Var x) = [];
supt_list (Term.Fun f ts) = concatMap supteq_list ts;

check_supt ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => Term.Term a b ->
                                  Term.Term a b ->
                                    Sum_Type.Sum (String -> String) ();
check_supt s t =
  Check_Monad.check (supt_impl s t)
    ((Term_More.showsl_terma t .
       Shows_Literal.showsl_literal " is not a proper subterm of ") .
      Term_More.showsl_terma s);

check_no_var ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => Term.Term a b ->
                                  Sum_Type.Sum (String -> String) ();
check_no_var t =
  Check_Monad.check (not (Term.is_Var t))
    (Shows_Literal.showsl_literal "variable found\n");

check_supteq ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => Term.Term a b ->
                                  Term.Term a b ->
                                    Sum_Type.Sum (String -> String) ();
check_supteq s t =
  Check_Monad.check (Term.equal_term s t || supt_impl s t)
    ((Term_More.showsl_terma t .
       Shows_Literal.showsl_literal " is not a subterm of ") .
      Term_More.showsl_terma s);

add_funs_term :: forall a b. Term.Term a b -> [a] -> [a];
add_funs_term (Term.Var uu) fs = fs;
add_funs_term (Term.Fun f ts) fs = f : List.foldr add_funs_term ts fs;

add_vars_term :: forall a b. Term.Term a b -> [b] -> [b];
add_vars_term (Term.Var x) xs = x : xs;
add_vars_term (Term.Fun uu ts) xs = List.foldr add_vars_term ts xs;

subst_compose_impl ::
  forall a b.
    (Eq a,
      Eq b) => [(a, Term.Term b a)] ->
                 [(a, Term.Term b a)] -> [(a, Term.Term b a)];
subst_compose_impl sigma tau =
  let {
    sigmaa = mk_subst_domain sigma;
    taua = mk_subst_domain tau;
    d_sigma = map fst sigmaa;
  } in map (\ (x, t) ->
             (x, Term.eval_term Term.Fun t (Term_More.mk_subst Term.Var taua)))
         sigmaa ++
         filter (\ (x, _) -> not (List.member d_sigma x)) taua;

commutes_impl ::
  forall a b.
    (Collection_Enum.Cenum a, Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Compare.Compare a, Eq a, Set_Impl.Set_impl a, Compare.Compare b,
      Eq b) => [(a, Term.Term b a)] -> [(a, Term.Term b a)] -> Bool;
commutes_impl sigma mu =
  subst_eq (subst_compose_impl sigma mu) (subst_compose_impl mu sigma);

fun_poss_list :: forall a b. Term.Term a b -> [[Arith.Nat]];
fun_poss_list (Term.Var x) = [];
fun_poss_list (Term.Fun f ss) =
  [] : concatMap (\ (i, a) -> map (\ aa -> i : aa) a)
         (zip (List.upt Arith.zero_nat (List.size_list ss))
           (map fun_poss_list ss));

mk_subst_case ::
  forall a b.
    (Eq a,
      Eq b) => [a] ->
                 (a -> Term.Term b a) ->
                   [(a, Term.Term b a)] -> [(a, Term.Term b a)];
mk_subst_case xs sigma tau =
  subst_compose_impl (map (\ x -> (x, sigma x)) xs) tau;

var_poss_list :: forall a b. Term.Term a b -> [[Arith.Nat]];
var_poss_list (Term.Var x) = [[]];
var_poss_list (Term.Fun f ss) =
  concatMap (\ (i, a) -> map (\ aa -> i : aa) a)
    (zip (List.upt Arith.zero_nat (List.size_list ss)) (map var_poss_list ss));

add_funas_term ::
  forall a b. Term.Term a b -> [(a, Arith.Nat)] -> [(a, Arith.Nat)];
add_funas_term (Term.Var uu) fs = fs;
add_funas_term (Term.Fun f ts) fs =
  (f, List.size_list ts) : List.foldr add_funas_term ts fs;

range_vars_impl :: forall a b. (Eq a, Eq b) => [(a, Term.Term b a)] -> [a];
range_vars_impl sigma = let {
                          a = mk_subst_domain sigma;
                        } in concatMap (Term_More.vars_term_list . snd) a;

vars_subst_impl :: forall a b. (Eq a, Eq b) => [(a, Term.Term b a)] -> [a];
vars_subst_impl sigma =
  let {
    sigmaa = mk_subst_domain sigma;
  } in map fst sigmaa ++ concatMap (Term_More.vars_term_list . snd) sigmaa;

check_funas_term ::
  forall a b.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Shows_Literal.Showl a,
      Shows_Literal.Showl b) => Set.Set (a, Arith.Nat) ->
                                  Term.Term a b ->
                                    Sum_Type.Sum (String -> String) ();
check_funas_term fa (Term.Fun f ts) =
  Error_Monad.bind
    (Check_Monad.check (Set.member (f, List.size_list ts) fa)
      (((Term_More.showsl_terma (Term.Fun f ts) .
          Shows_Literal.showsl_lit "problem: root of subterm  ") .
         Shows_Literal.showsl f) .
        Shows_Literal.showsl_lit " not in signature\n"))
    (\ _ ->
      Error_Monad.catch_error (Error_Monad.forallM (check_funas_term fa) ts)
        (\ x -> Sum_Type.Inl (snd x)));
check_funas_term f (Term.Var uu) = Sum_Type.Inr ();

insert_vars_term :: forall a b. (Eq b) => Term.Term a b -> [b] -> [b];
insert_vars_term (Term.Var x) xs = List.insert x xs;
insert_vars_term (Term.Fun f ts) xs = List.foldr insert_vars_term ts xs;

is_renaming_impl :: forall a b. (Eq a, Eq b) => [(a, Term.Term b a)] -> Bool;
is_renaming_impl sigma = let {
                           sigmaa = map snd (mk_subst_domain sigma);
                         } in all Term.is_Var sigmaa && List.distinct sigmaa;

linear_term_impl ::
  forall a b.
    (Collection_Eq.Ceq a,
      Collection_Order.Ccompare a) => Set.Set a ->
Term.Term b a -> Maybe (Set.Set a);
linear_term_impl xs (Term.Var x) =
  (if Set.member x xs then Nothing else Just (Set.insert x xs));
linear_term_impl xs (Term.Fun uu []) = Just xs;
linear_term_impl xs (Term.Fun f (t : ts)) =
  (case linear_term_impl xs t of {
    Nothing -> Nothing;
    Just ys -> linear_term_impl ys (Term.Fun f ts);
  });

subst_power_impl ::
  forall a b.
    (Eq a, Eq b) => [(a, Term.Term b a)] -> Arith.Nat -> [(a, Term.Term b a)];
subst_power_impl sigma n =
  (if Arith.equal_nat n Arith.zero_nat then []
    else subst_compose_impl sigma
           (subst_power_impl sigma (Arith.minus_nat n Arith.one_nat)));

check_ground_term ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => Term.Term a b ->
                                  Sum_Type.Sum (String -> String) ();
check_ground_term s =
  Check_Monad.check (Term.ground s)
    ((Shows_Literal.showsl_literal "the term " . Term_More.showsl_terma s) .
      Shows_Literal.showsl_literal " is not a ground term\n");

check_linear_term ::
  forall a b.
    (Shows_Literal.Showl a, Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Set_Impl.Set_impl b,
      Shows_Literal.Showl b) => Term.Term a b ->
                                  Sum_Type.Sum (String -> String) ();
check_linear_term s =
  Check_Monad.check (Term_More.linear_term s)
    ((Shows_Literal.showsl_literal "the term " . Term_More.showsl_terma s) .
      Shows_Literal.showsl_literal " is not linear\n");

contains_var_term :: forall a b. (Eq a) => a -> Term.Term b a -> Bool;
contains_var_term x (Term.Var y) = x == y;
contains_var_term x (Term.Fun uu ts) = any (contains_var_term x) ts;

flatten_term_enum :: forall a b. Term.Term [a] b -> [Term.Term a b];
flatten_term_enum (Term.Var x) = [Term.Var x];
flatten_term_enum (Term.Fun fs ts) =
  let {
    lts = map flatten_term_enum ts;
    ss = Missing_List.concat_lists lts;
  } in concatMap (\ f -> map (Term.Fun f) ss) fs;

insert_funas_term ::
  forall a b. (Eq a) => Term.Term a b -> [(a, Arith.Nat)] -> [(a, Arith.Nat)];
insert_funas_term (Term.Var x) fs = fs;
insert_funas_term (Term.Fun f ts) fs =
  List.insert (f, List.size_list ts) (List.foldr insert_funas_term ts fs);

subst_replace_impl ::
  forall a b.
    (Eq a) => [(a, Term.Term b a)] ->
                a -> Term.Term b a -> [(a, Term.Term b a)];
subst_replace_impl sigma x t = (x, t) : filter (\ (y, _) -> not (y == x)) sigma;

add_funas_args_term ::
  forall a b. Term.Term a b -> [(a, Arith.Nat)] -> [(a, Arith.Nat)];
add_funas_args_term t fs = List.foldr add_funas_term (Term.args t) fs;

subst_compose_impla ::
  forall a b.
    (Eq a,
      Eq b) => [(a, Term.Term b a)] ->
                 (a -> Term.Term b a) -> [(a, Term.Term b a)];
subst_compose_impla sigma rho =
  map (\ (x, s) -> (x, Term.eval_term Term.Fun s rho)) (mk_subst_domain sigma);

insert_funas_args_term ::
  forall a b. (Eq a) => Term.Term a b -> [(a, Arith.Nat)] -> [(a, Arith.Nat)];
insert_funas_args_term t fs = List.foldr insert_funas_term (Term.args t) fs;

is_inverse_renaming_impl ::
  forall a b. (Eq a, Eq b) => [(a, Term.Term b a)] -> [(a, Term.Term b a)];
is_inverse_renaming_impl sigma =
  let {
    a = mk_subst_domain sigma;
  } in map (\ (x, y) -> (Term.the_Var y, Term.Var x)) a;

}
