{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Trs_Impl(rewrite, is_root_step, is_rstep, is_NF_trs, showsl_rulea,
            showsl_trsa, showsl_trs, is_NF_terms, showsl_rule,
            check_varcond_no_Var_lhs, check_varcond_subset, check_wf_trs,
            defined_list, showsl_rules, add_funs_rule, add_vars_rule,
            compute_rstep_NF, check_join_NF, reverse_rules, wf_rules_impl,
            add_funas_rule, check_wf_reltrs, reachable_terms, check_linear_trs,
            insert_funas_trs, insert_roots_trs, insert_vars_rule,
            check_CS_subseteq, map_funs_rules_wa, add_funas_args_rule,
            non_collapsing_impl, check_join_BFS_limit, check_left_linear_trs,
            insert_funas_args_trs)
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
import qualified Abstract_Rewriting_Impl;
import qualified Set_Impl;
import qualified HOL;
import qualified Trs;
import qualified Check_Monad;
import qualified Term_More;
import qualified Collection_Eq;
import qualified Container_Setup;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Shows_Literal;
import qualified Term_Impl;
import qualified RBT_Map_Set_Extension;
import qualified Option_Util;
import qualified RBT;
import qualified Compare_Order_Instances;
import qualified Compare_Instances;
import qualified Option;
import qualified Matching;
import qualified Set;
import qualified Compare;
import qualified Product_Type;
import qualified List;
import qualified Term;
import qualified Arith;
import qualified Mapping_Impl;
import qualified Collection_Order;

rrewrite ::
  forall a b.
    (Eq a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b) => [(Term.Term a b, Term.Term a b)] ->
Term.Term a b -> [Term.Term a b];
rrewrite r s =
  concatMap (\ (l, ra) -> (case Matching.match s l of {
                            Nothing -> [];
                            Just sigma -> [Term.eval_term Term.Fun ra sigma];
                          }))
    r;

rewrite ::
  forall a b.
    (Eq a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b) => [(Term.Term a b, Term.Term a b)] ->
Term.Term a b -> [Term.Term a b];
rewrite r s =
  rrewrite r s ++
    (case s of {
      Term.Var _ -> [];
      Term.Fun f ss ->
        concatMap
          (\ (i, si) ->
            map (\ ti -> Term.Fun f (List.list_update ss i ti)) (rewrite r si))
          (zip (List.upt Arith.zero_nat (List.size_list ss)) ss);
    });

is_root_step ::
  forall a b.
    (Compare.Compare a, Eq a, Collection_Order.Ccompare b, Compare.Compare b,
      Eq b,
      Mapping_Impl.Mapping_impl b) => Set.Set (Term.Term a b, Term.Term a b) ->
Term.Term a b -> Term.Term a b -> Bool;
is_root_step r s t =
  Set.bex r
    (\ (l, ra) -> (case Matching.match_list Term.Var [(l, s), (ra, t)] of {
                    Nothing -> False;
                    Just _ -> True;
                  }));

is_rstep ::
  forall a b.
    (Compare.Compare a, Eq a, Collection_Order.Ccompare b, Compare.Compare b,
      Eq b,
      Mapping_Impl.Mapping_impl b) => Set.Set (Term.Term a b, Term.Term a b) ->
Term.Term a b -> Term.Term a b -> Bool;
is_rstep r (Term.Fun f ts) (Term.Fun g ss) =
  f == g &&
    Arith.equal_nat (List.size_list ts) (List.size_list ss) &&
      any (\ i ->
            ss == List.list_update ts i (List.nth ss i) &&
              is_rstep r (List.nth ts i) (List.nth ss i))
        (List.upt Arith.zero_nat (List.size_list ss)) ||
    is_root_step r (Term.Fun f ts) (Term.Fun g ss);
is_rstep r (Term.Var v) t = is_root_step r (Term.Var v) t;
is_rstep r s (Term.Var v) = is_root_step r s (Term.Var v);

term_map ::
  forall a b.
    (Compare.Compare_order a) => [Term.Term a b] ->
                                   (a, Arith.Nat) -> [Term.Term a b];
term_map ts =
  Option_Util.fun_of_map
    (RBT.lookup
      (RBT_Map_Set_Extension.elem_list_to_rm (Option.the . Term.root) ts))
    [];

is_NF_main ::
  forall a b.
    (Compare.Compare_order a, Eq a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b) => Bool ->
Bool -> ((a, Arith.Nat) -> [Term.Term a b]) -> Term.Term a b -> Bool;
is_NF_main var_cond r_empty m =
  (if var_cond then (\ _ -> False)
    else (if r_empty then (\ _ -> True)
           else (\ t ->
                  all (\ u ->
                        (if not (Term.is_Var u)
                          then all (\ l -> not (Matching.matches u l))
                                 (m (Option.the (Term.root u)))
                          else True))
                    (Term_Impl.supteq_list t))));

is_NF_trs ::
  forall a b c.
    (Compare.Compare_order a, Eq a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b) => [(Term.Term a b, c)] ->
Term.Term a b -> Bool;
is_NF_trs r =
  is_NF_main (any (\ ra -> Term.is_Var (fst ra)) r) (null r)
    (term_map (map fst r));

showsl_rulea ::
  forall a b.
    (a -> String -> String) ->
      (b -> String -> String) ->
        String -> (Term.Term a b, Term.Term a b) -> String -> String;
showsl_rulea fun var arr (l, r) =
  (Term_More.showsl_term fun var l . Shows_Literal.showsl_literal arr) .
    Term_More.showsl_term fun var r;

showsl_rulesa ::
  forall a b.
    (a -> String -> String) ->
      (b -> String -> String) ->
        String -> [(Term.Term a b, Term.Term a b)] -> String -> String;
showsl_rulesa fun var arr trs =
  Shows_Literal.showsl_list_gen (showsl_rulea fun var arr) "" "" "\n" "" trs .
    Shows_Literal.showsl_literal "\n";

showsl_trsa ::
  forall a b.
    (a -> String -> String) ->
      (b -> String -> String) ->
        String ->
          String -> [(Term.Term a b, Term.Term a b)] -> String -> String;
showsl_trsa fun var name arr r =
  (Shows_Literal.showsl_literal name . Shows_Literal.showsl_literal "\n\n") .
    showsl_rulesa fun var arr r;

showsl_trs ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => [(Term.Term a b, Term.Term a b)] ->
                                  String -> String;
showsl_trs =
  showsl_trsa Shows_Literal.showsl Shows_Literal.showsl "rewrite system:"
    " -> ";

is_NF_terms ::
  forall a b.
    (Compare.Compare_order a, Eq a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b) => [Term.Term a b] -> Term.Term a b -> Bool;
is_NF_terms q = is_NF_main (any Term.is_Var q) (null q) (term_map q);

showsl_rule ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => (Term.Term a b, Term.Term a b) ->
                                  String -> String;
showsl_rule = showsl_rulea Shows_Literal.showsl Shows_Literal.showsl " -> ";

check_varcond_no_Var_lhs ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => [(Term.Term a b, Term.Term a b)] ->
                                  Sum_Type.Sum (String -> String) ();
check_varcond_no_Var_lhs =
  (\ xs ->
    Error_Monad.catch_error
      (Error_Monad.forallM
        (\ rule ->
          Check_Monad.check (not (Term.is_Var (fst rule)))
            ((Shows_Literal.showsl_literal "variable left-hand side in rule " .
               showsl_rule rule) .
              Shows_Literal.showsl_literal "\n"))
        xs)
      (\ x -> Sum_Type.Inl (snd x)));

check_varcond_subset ::
  forall a b.
    (Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => [(Term.Term a b, Term.Term a b)] ->
                                  Sum_Type.Sum (String -> String) ();
check_varcond_subset r =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ rule ->
        Error_Monad.catch_error
          (Check_Monad.check_subseteq (Term_Impl.insert_vars_term (snd rule) [])
            (Term_Impl.insert_vars_term (fst rule) []))
          (\ x ->
            Sum_Type.Inl
              ((((Shows_Literal.showsl_literal "free variable " .
                   Shows_Literal.showsl x) .
                  Shows_Literal.showsl_literal " in right-hand side of rule ") .
                 showsl_rule rule) .
                Shows_Literal.showsl_literal "\n")))
      r)
    (\ x -> Sum_Type.Inl (snd x));

check_wf_trs ::
  forall a b.
    (Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => [(Term.Term a b, Term.Term a b)] ->
                                  Sum_Type.Sum (String -> String) ();
check_wf_trs r =
  Error_Monad.catch_error
    (Error_Monad.bind (check_varcond_no_Var_lhs r)
      (\ _ -> check_varcond_subset r))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_literal "the TRS is not well-formed\n" . x));

defined_list ::
  forall a b. [(Term.Term a b, Term.Term a b)] -> [(a, Arith.Nat)];
defined_list r =
  concatMap
    (\ (l, _) ->
      (if not (Term.is_Var l) then [Option.the (Term.root l)] else []))
    r;

showsl_rules ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => [(Term.Term a b, Term.Term a b)] ->
                                  String -> String;
showsl_rules = showsl_rulesa Shows_Literal.showsl Shows_Literal.showsl " -> ";

add_funs_rule :: forall a b. (Term.Term a b, Term.Term a b) -> [a] -> [a];
add_funs_rule r fs =
  Term_Impl.add_funs_term (fst r) (Term_Impl.add_funs_term (snd r) fs);

add_vars_rule :: forall a b. (Term.Term a b, Term.Term a b) -> [b] -> [b];
add_vars_rule r xs =
  Term_Impl.add_vars_term (fst r) (Term_Impl.add_vars_term (snd r) xs);

first_rewrite ::
  forall a b.
    (Eq a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b) => [(Term.Term a b, Term.Term a b)] ->
Term.Term a b -> Maybe (Term.Term a b);
first_rewrite r s = (case rewrite r s of {
                      [] -> Nothing;
                      t : _ -> Just t;
                    });

compute_rstep_NF ::
  forall a b.
    (Eq a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b) => [(Term.Term a b, Term.Term a b)] ->
Term.Term a b -> Maybe (Term.Term a b);
compute_rstep_NF r s = Abstract_Rewriting_Impl.compute_NF (first_rewrite r) s;

check_join_NF ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b,
      Shows_Literal.Showl b) => [(Term.Term a b, Term.Term a b)] ->
                                  Term.Term a b ->
                                    Term.Term a b ->
                                      Sum_Type.Sum (String -> String) ();
check_join_NF r s t =
  (case (compute_rstep_NF r s, compute_rstep_NF r t) of {
    (Nothing, _) ->
      Sum_Type.Inl
        (Shows_Literal.showsl_literal
          "strange error in normal form computation");
    (Just _, Nothing) ->
      Sum_Type.Inl
        (Shows_Literal.showsl_literal
          "strange error in normal form computation");
    (Just sa, Just ta) ->
      Check_Monad.check (Term.equal_term sa ta)
        (((((((Shows_Literal.showsl_literal "the normal form " .
                Term_More.showsl_terma sa) .
               Shows_Literal.showsl_literal " of ") .
              Term_More.showsl_terma s) .
             Shows_Literal.showsl_literal " differs from\nthe normal form ") .
            Term_More.showsl_terma ta) .
           Shows_Literal.showsl_literal " of ") .
          Term_More.showsl_terma t);
  });

reverse_rules ::
  forall a b.
    [(Term.Term a b, Term.Term a b)] -> [(Term.Term a b, Term.Term a b)];
reverse_rules rs = map Product_Type.swap rs;

wf_rules_impl ::
  forall a b.
    (Eq b) => [(Term.Term a b, Term.Term a b)] ->
                [(Term.Term a b, Term.Term a b)];
wf_rules_impl r = filter Trs.wf_rule r;

add_funas_rule ::
  forall a b.
    (Term.Term a b, Term.Term a b) -> [(a, Arith.Nat)] -> [(a, Arith.Nat)];
add_funas_rule r fs =
  Term_Impl.add_funas_term (fst r) (Term_Impl.add_funas_term (snd r) fs);

check_wf_reltrs ::
  forall a b c d.
    (Shows_Literal.Showl a, Eq b, Shows_Literal.Showl b, Shows_Literal.Showl c,
      Eq d,
      Shows_Literal.Showl d) => ([(Term.Term a b, Term.Term a b)],
                                  [(Term.Term c d, Term.Term c d)]) ->
                                  Sum_Type.Sum (String -> String) ();
check_wf_reltrs (r, s) =
  Error_Monad.bind (check_wf_trs r)
    (\ _ -> (if null r then Sum_Type.Inr () else check_varcond_subset s));

reachable_terms ::
  forall a b.
    (Eq a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b) => [(Term.Term a b, Term.Term a b)] ->
Term.Term a b -> Arith.Nat -> [Term.Term a b];
reachable_terms r s n =
  (if Arith.equal_nat n Arith.zero_nat then [s]
    else let {
           ts = reachable_terms r s (Arith.minus_nat n Arith.one_nat);
         } in List.remdups (ts ++ concatMap (rewrite r) ts));

check_linear_trs ::
  forall a b.
    (Shows_Literal.Showl a, Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Set_Impl.Set_impl b,
      Shows_Literal.Showl b) => [(Term.Term a b, Term.Term a b)] ->
                                  Sum_Type.Sum (String -> String) ();
check_linear_trs r =
  Error_Monad.catch_error
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ x ->
          (if (case x of {
                (l, ra) -> Term_More.linear_term l && Term_More.linear_term ra;
              })
            then Sum_Type.Inr () else Sum_Type.Inl x))
        r)
      (\ x -> Sum_Type.Inl (snd x)))
    (\ _ ->
      Sum_Type.Inl
        (showsl_trs r . Shows_Literal.showsl_literal "\nis not linear\n"));

insert_funas_rule ::
  forall a b.
    (Eq a) => (Term.Term a b, Term.Term a b) ->
                [(a, Arith.Nat)] -> [(a, Arith.Nat)];
insert_funas_rule r fs =
  Term_Impl.insert_funas_term (fst r) (Term_Impl.insert_funas_term (snd r) fs);

insert_funas_trs ::
  forall a b.
    (Eq a) => [(Term.Term a b, Term.Term a b)] ->
                [(a, Arith.Nat)] -> [(a, Arith.Nat)];
insert_funas_trs trs = List.foldr insert_funas_rule trs;

insert_roots_rule ::
  forall a b.
    (Eq a) => (Term.Term a b, Term.Term a b) ->
                [(a, Arith.Nat)] -> [(a, Arith.Nat)];
insert_roots_rule r fs =
  List.foldr List.insert
    (Option_Util.option_to_list (Term.root (fst r)) ++
      Option_Util.option_to_list (Term.root (snd r)))
    fs;

insert_roots_trs ::
  forall a b.
    (Eq a) => [(Term.Term a b, Term.Term a b)] ->
                [(a, Arith.Nat)] -> [(a, Arith.Nat)];
insert_roots_trs trs = List.foldr insert_roots_rule trs;

insert_vars_rule ::
  forall a b. (Eq b) => (Term.Term a b, Term.Term a b) -> [b] -> [b];
insert_vars_rule r xs =
  Term_Impl.insert_vars_term (fst r) (Term_Impl.insert_vars_term (snd r) xs);

check_CS_subseteq ::
  forall a b.
    (Eq a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b) => [(Term.Term a b, Term.Term a b)] ->
[(Term.Term a b, Term.Term a b)] ->
  Sum_Type.Sum (Term.Term a b, Term.Term a b) ();
check_CS_subseteq r s =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ (l, ra) ->
        Check_Monad.check (any (Trs.instance_rule (l, ra)) s) (l, ra))
      r)
    (\ x -> Sum_Type.Inl (snd x));

map_funs_rules_wa ::
  forall a b c.
    ((a, Arith.Nat) -> b) ->
      [(Term.Term a c, Term.Term a c)] -> [(Term.Term b c, Term.Term b c)];
map_funs_rules_wa fg r =
  map (\ (l, ra) ->
        (Term_More.map_funs_term_wa fg l, Term_More.map_funs_term_wa fg ra))
    r;

add_funas_args_rule ::
  forall a b.
    (Term.Term a b, Term.Term a b) -> [(a, Arith.Nat)] -> [(a, Arith.Nat)];
add_funas_args_rule r fs =
  Term_Impl.add_funas_args_term (fst r)
    (Term_Impl.add_funas_args_term (snd r) fs);

non_collapsing_impl :: forall a b c. [(a, Term.Term b c)] -> Bool;
non_collapsing_impl r = all ((\ t -> not (Term.is_Var t)) . snd) r;

iterative_join_search_main ::
  forall a b.
    (Eq a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b) => [(Term.Term a b, Term.Term a b)] ->
Term.Term a b -> Term.Term a b -> Arith.Nat -> Arith.Nat -> Bool;
iterative_join_search_main r s t i n =
  (if Arith.less_eq_nat i n
    then not (null (List.inter_list_set (reachable_terms r s i)
                     (reachable_terms r t i))) ||
           iterative_join_search_main r s t (Arith.suc i) n
    else False);

iterative_join_search ::
  forall a b.
    (Eq a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b) => [(Term.Term a b, Term.Term a b)] ->
Term.Term a b -> Term.Term a b -> Arith.Nat -> Bool;
iterative_join_search r s t n =
  iterative_join_search_main r s t Arith.zero_nat n;

check_join_BFS_limit ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b,
      Shows_Literal.Showl b) => Arith.Nat ->
                                  [(Term.Term a b, Term.Term a b)] ->
                                    Term.Term a b ->
                                      Term.Term a b ->
Sum_Type.Sum (String -> String) ();
check_join_BFS_limit n r s t =
  Check_Monad.check (iterative_join_search r s t n)
    ((((((Shows_Literal.showsl_literal
            "could not find a joining sequence of length at most " .
           Shows_Literal.showsl_nat n) .
          Shows_Literal.showsl_literal " for the terms ") .
         Term_More.showsl_terma s) .
        Shows_Literal.showsl_literal " and ") .
       Term_More.showsl_terma t) .
      Shows_Literal.showsl_literal "\n");

check_left_linear_trs ::
  forall a b.
    (Shows_Literal.Showl a, Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Set_Impl.Set_impl b,
      Shows_Literal.Showl b) => [(Term.Term a b, Term.Term a b)] ->
                                  Sum_Type.Sum (String -> String) ();
check_left_linear_trs trs =
  Error_Monad.catch_error
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ x ->
          (if Term_More.linear_term (fst x) then Sum_Type.Inr ()
            else Sum_Type.Inl x))
        trs)
      (\ x -> Sum_Type.Inl (snd x)))
    (\ _ ->
      Sum_Type.Inl
        (showsl_trs trs .
          Shows_Literal.showsl_literal "\nis not left-linear\n"));

insert_funas_args_rule ::
  forall a b.
    (Eq a) => (Term.Term a b, Term.Term a b) ->
                [(a, Arith.Nat)] -> [(a, Arith.Nat)];
insert_funas_args_rule r fs =
  Term_Impl.insert_funas_args_term (fst r)
    (Term_Impl.insert_funas_args_term (snd r) fs);

insert_funas_args_trs ::
  forall a b.
    (Eq a) => [(Term.Term a b, Term.Term a b)] ->
                [(a, Arith.Nat)] -> [(a, Arith.Nat)];
insert_funas_args_trs trs = List.foldr insert_funas_args_rule trs;

}
