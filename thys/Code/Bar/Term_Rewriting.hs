{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Term_Rewriting(set_impl_rat, Term(..), equal_term, set_impl_term, showsl_term,
                  showsl_terma, Atom(..), Trans_var(..), Formula(..),
                  equal_formula, Transition_rule(..), equal_transition_rule,
                  Gctxt(..), equal_gctxt, Ta_rule(..), compare_ta_rule,
                  set_impl_ta_rule, Mctxt(..), equal_mctxt, Filtered(..),
                  Sharp(..), equal_sharp, showsl_sharp, showsl_list_sharp,
                  Actxt(..), equal_actxt, Ty(..), Linear_poly, Sig(..),
                  Lts_impl(..), State(..), Lts_ext, Direction, Constraint(..),
                  Af_entry(..), Afs, Ns_constraint(..), Ta_ext(..),
                  Rel_impl_ext(..), Rel_impl_type(..), Poly_constraint(..),
                  X_compare_order_x_x_f_afs_option_x_x_nat_x_compare_order_x_x_f_prod_set_af_entry_nat_x_compare_order_x_x_f_prod_fun_prod_option,
                  root, transitions_impl, initiala, assertion_impl,
                  assertion_of, lts_of, source, target, subst, ground,
                  insert_vars_term, is_Var, wf_rule, vars_term_list, vars_term,
                  vars_rule, vars_trs, to_ns, funas_term, funas_rule, funas_trs,
                  match_list, match, eval_term, args, form_or, form_and,
                  initial, vars_list, map2fun, from_ns, v, coeff,
                  assert_bound_code, u, init_state, scaleRat_linear_poly,
                  uminus_linear_poly, plus_linear_poly, var, check_code, u_c,
                  atom_var, zero_linear_poly, preprocess, simplex, subst_of,
                  contains_var_term, subst_list, unify, mgu, form_not, get_Atom,
                  matches, rewrite, assertion, transition_of, the_Var,
                  vars_term_ms, in_poss, subt_at, add_funs_rule, funs_trs_list,
                  instance_rule, map_term, map_funs_rule, vars_trs_list,
                  is_root_step, is_rstep, nodes_lts_impl, rec_term, mk_subst,
                  mk_subst_domain, subst_eq, hole_pos, var_poss, funas_trs_list,
                  funs_rule_list, vars_rule_list, supteq_list, is_NF_trs,
                  mgu_var_disjoint_generic, mgu_vd, poss_list, supt_impl,
                  supt_list, r_sym, funas_rule_list, showsl_rulea, showsl_trsa,
                  showsl_trs, merge, matcha, succ_transitions, check_supt,
                  r_lhs_states, r_rhs, ta_rules, ta_eps, eq_rule_mod_vars,
                  is_NF_terms, showsl_rule, linear_term, ta_final, ta_syms,
                  trim_ta, check_varcond_no_Var_lhs, check_varcond_subset,
                  check_wf_trs, defined_list, showsl_rules, default_af_entry,
                  afs_of, has_type, is_bool, formula, transition_rule,
                  check_lts_impl, check_no_var, check_supteq, funs_term_ms,
                  subt_at_ctxt, ta_empty, compute_rstep_NF, check_join_NF,
                  reverse_rules, wf_rules_impl, af_term, in_vars_formula,
                  subst_compose_impl, commutes_impl, fun_poss_list,
                  mk_subst_case, prc_nat, prl_nat, ta_member,
                  funas_args_trs_list, af_rules, pos_gctxt, unifiable,
                  funs_term_list, check_wf_reltrs, reachable_terms, vars,
                  range_vars_impl, vars_subst_impl, funas_term_list,
                  check_linear_trs, insert_funas_term, insert_funas_trs,
                  insert_roots_trs, insert_vars_rule, check_funas_term,
                  is_renaming_impl, subst_power_impl, ctxt_of_pos_term,
                  map_funs_term_wa, s, rel_impl_s, intersect_ta,
                  check_CS_subseteq, map_funs_rules_wa, natural, map_formula,
                  hole_poss, check_ground_term, check_linear_term,
                  flatten_term_enum, sn, af, ns, rel_impl_ns, rel_impl_of,
                  showsl_funa, is_sharp, del_transitions_impl, fill_holes,
                  split_term, uncap_till, subst_replace_impl, cpx, nst,
                  rel_impl_nst, r_root, non_collapsing_impl, lp_monom,
                  funas_mctxt, subst_compose_impla, desc, check_join_BFS_limit,
                  mgu_vd_string, gc_matcher, ground_mctxt, rename_vars_exp,
                  intp_actxt, funas_args_term_list, valid,
                  check_left_linear_trs, insert_funas_args_trs, permutation_afs,
                  if_Fun_in_set, no_complexity_check, faulty_rel_impl, top_af,
                  mono_af, not_sst, not_wst, subst_s, standard,
                  rel_impl_redpair, ce_compat, filtered_rel_impl,
                  check_trivial_implication, actxt_compose,
                  refine_transition_formulas, funas_mctxt_list, vars_mctxt,
                  is_inverse_renaming_impl, rel_impl_redtriple, call_graph_impl,
                  flat_transition, subst_apply_mctxt, map_actxt,
                  filtered_rel_impl_af, sharp_transition,
                  closed_under_rewriting, showsl_formula, rel_impl_mono_redpair,
                  showsl_actxta, rel_impl_root_redtriple, compare_res,
                  ta_det_impl, ta_eps_impl, ta_idx_impl, set_impl_ty,
                  type_of_fun, showsl_IA_exp, def_checker,
                  rel_impl_co_rewrite_pair, rel_impl_mono_ce_redpair,
                  memo_rtrancl, ta_make_code, showsl_formulaa, ta_final_impl,
                  ta_rules_impl, ta_eps_cl_impl, ta_eps_icl_impl,
                  subst_apply_term, check_valid_formula, ta_rhs_states_impl,
                  rel_impl_co_discrimination_pair,
                  rel_impl_quasi_reduction_triple, union_image_rs_code,
                  showsl_gctxt, showsl_poly_constraint, showsl_mctxt,
                  iA_exp_to_poly_constraint, interpret_poly_constraint,
                  vars_poly_constraint_list, check_skip_transition)
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
import qualified SetIteratorOperations;
import qualified RBT_add;
import qualified Labelings_Impl;
import qualified Show_Literal_Polynomial;
import qualified Transitive_Closure_RBT_Impl;
import qualified Autoref_Bindings_HOL;
import qualified Impl_List_Set;
import qualified Gen_Set;
import qualified Foldi;
import qualified Tree_Automata_Det_Container;
import qualified Intf_Comp;
import qualified Term_Order;
import qualified Show_Instances;
import qualified Missing_List;
import qualified Groups_List;
import qualified Simplex_Auxiliary;
import qualified Map_Choice;
import qualified Util;
import qualified FSet;
import qualified Relation;
import qualified Option_Monad;
import qualified Error_Monad;
import qualified Abstract_Rewriting_Impl;
import qualified Check_Monad;
import qualified Abstract_Matching;
import qualified Renaming2;
import qualified Fresh;
import qualified Set_Interval;
import qualified Map;
import qualified Simplex_Algebra;
import qualified RBT_Map_Set_Extension;
import qualified Option_Util;
import qualified RBT;
import qualified Compare_Order_Instances;
import qualified Multiset;
import qualified Map_Of;
import qualified HOL;
import qualified Complete_Lattices;
import qualified Fun;
import qualified Complexity;
import qualified Sum_Type;
import qualified Polynomials;
import qualified Finite_Map;
import qualified Forbidden_Patterns;
import qualified Linear_Polynomial;
import qualified SN_Order_Carrier;
import qualified QDelta;
import qualified Labelings;
import qualified Mapping;
import qualified Shows_Literal;
import qualified Quasi_Order;
import qualified Real;
import qualified Phantom_Type;
import qualified Arith;
import qualified Comparator;
import qualified Rat;
import qualified Compare;

compare_rat :: Rat.Rat -> Rat.Rat -> Comparator.Order;
compare_rat = Comparator.comparator_of;

instance Compare.Compare Rat.Rat where {
  compare = compare_rat;
};

ceq_rat :: Maybe (Rat.Rat -> Rat.Rat -> Bool);
ceq_rat = Just Rat.equal_rat;

instance Arith.Ceq Rat.Rat where {
  ceq = ceq_rat;
};

set_impl_rat :: Phantom_Type.Phantom Rat.Rat Arith.Set_impla;
set_impl_rat = Phantom_Type.Phantom Arith.Set_RBT;

instance Arith.Set_impl Rat.Rat where {
  set_impl = set_impl_rat;
};

cEnum_rat ::
  Maybe ([Rat.Rat], ((Rat.Rat -> Bool) -> Bool, (Rat.Rat -> Bool) -> Bool));
cEnum_rat = Nothing;

instance Arith.Cenum Rat.Rat where {
  cEnum = cEnum_rat;
};

ccompare_rat :: Maybe (Rat.Rat -> Rat.Rat -> Comparator.Order);
ccompare_rat = Just compare_rat;

instance Arith.Ccompare Rat.Rat where {
  ccompare = ccompare_rat;
};

ceq_real :: Maybe (Real.Real -> Real.Real -> Bool);
ceq_real = Just Real.equal_real;

instance Arith.Ceq Real.Real where {
  ceq = ceq_real;
};

set_impl_real :: Phantom_Type.Phantom Real.Real Arith.Set_impla;
set_impl_real = Phantom_Type.Phantom Arith.Set_RBT;

instance Arith.Set_impl Real.Real where {
  set_impl = set_impl_real;
};

cEnum_real ::
  Maybe ([Real.Real],
          ((Real.Real -> Bool) -> Bool, (Real.Real -> Bool) -> Bool));
cEnum_real = Nothing;

instance Arith.Cenum Real.Real where {
  cEnum = cEnum_real;
};

compare_real :: Real.Real -> Real.Real -> Comparator.Order;
compare_real = Comparator.comparator_of;

ccompare_real :: Maybe (Real.Real -> Real.Real -> Comparator.Order);
ccompare_real = Just compare_real;

instance Arith.Ccompare Real.Real where {
  ccompare = ccompare_real;
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

comparator_term ::
  forall a b.
    (a -> a -> Comparator.Order) ->
      (b -> b -> Comparator.Order) -> Term a b -> Term a b -> Comparator.Order;
comparator_term comp_f comp_v (Var x) (Var y) = comp_v x y;
comparator_term comp_f comp_v (Var x) (Fun ya yb) = Comparator.Lt;
comparator_term comp_f comp_v (Fun x xa) (Var y) = Comparator.Gt;
comparator_term comp_f comp_v (Fun x xa) (Fun ya yb) =
  (case comp_f x ya of {
    Comparator.Eqa ->
      Arith.comparator_list (comparator_term comp_f comp_v) xa yb;
    Comparator.Lt -> Comparator.Lt;
    Comparator.Gt -> Comparator.Gt;
  });

compare_term ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => Term a b -> Term a b -> Comparator.Order;
compare_term = comparator_term Compare.compare Compare.compare;

less_eq_term ::
  forall a b.
    (Compare.Compare a, Compare.Compare b) => Term a b -> Term a b -> Bool;
less_eq_term = Comparator.le_of_comp compare_term;

less_term ::
  forall a b.
    (Compare.Compare a, Compare.Compare b) => Term a b -> Term a b -> Bool;
less_term = Comparator.lt_of_comp compare_term;

instance (Compare.Compare a,
           Compare.Compare b) => Quasi_Order.Ord (Term a b) where {
  less_eq = less_eq_term;
  less = less_term;
};

instance (Compare.Compare a,
           Compare.Compare b) => Compare.Compare (Term a b) where {
  compare = compare_term;
};

instance (Compare.Compare a,
           Compare.Compare b) => Quasi_Order.Quasi_order (Term a b) where {
};

instance (Compare.Compare a,
           Compare.Compare b) => Quasi_Order.Weak_order (Term a b) where {
};

instance (Compare.Compare a,
           Compare.Compare b) => Quasi_Order.Preorder (Term a b) where {
};

instance (Compare.Compare a,
           Compare.Compare b) => Quasi_Order.Order (Term a b) where {
};

ceq_term :: forall a b. (Eq a, Eq b) => Maybe (Term a b -> Term a b -> Bool);
ceq_term = Just equal_term;

instance (Eq a, Eq b) => Arith.Ceq (Term a b) where {
  ceq = ceq_term;
};

set_impl_term :: forall a b. Phantom_Type.Phantom (Term a b) Arith.Set_impla;
set_impl_term = Phantom_Type.Phantom Arith.Set_RBT;

instance Arith.Set_impl (Term a b) where {
  set_impl = set_impl_term;
};

instance (Compare.Compare a,
           Compare.Compare b) => Quasi_Order.Linorder (Term a b) where {
};

showsl_term ::
  forall a b.
    (a -> String -> String) ->
      (b -> String -> String) -> Term a b -> String -> String;
showsl_term fun var (Var x) = var x;
showsl_term fun var (Fun f ts) =
  fun f .
    Shows_Literal.showsl_list_gen id "" "(" ", " ")"
      (map (showsl_term fun var) ts);

showsl_terma ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => Term a b -> String -> String;
showsl_terma t = showsl_term Shows_Literal.showsl Shows_Literal.showsl t;

showsl_list_term ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => [Term a b] -> String -> String;
showsl_list_term xs = Shows_Literal.default_showsl_list showsl_terma xs;

instance (Shows_Literal.Showl a,
           Shows_Literal.Showl b) => Shows_Literal.Showl (Term a b) where {
  showsl = showsl_terma;
  showsl_list = showsl_list_term;
};

cEnum_term ::
  forall a b.
    Maybe ([Term a b],
            ((Term a b -> Bool) -> Bool, (Term a b -> Bool) -> Bool));
cEnum_term = Nothing;

instance Arith.Cenum (Term a b) where {
  cEnum = cEnum_term;
};

instance (Compare.Compare a,
           Compare.Compare b) => Compare.Compare_order (Term a b) where {
};

finite_UNIV_term :: forall a b. Phantom_Type.Phantom (Term a b) Bool;
finite_UNIV_term = Phantom_Type.Phantom False;

instance Arith.Finite_UNIV (Term a b) where {
  finite_UNIV = finite_UNIV_term;
};

ccompare_term ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => Maybe (Term a b -> Term a b -> Comparator.Order);
ccompare_term = Just compare_term;

instance (Compare.Compare a,
           Compare.Compare b) => Arith.Ccompare (Term a b) where {
  ccompare = ccompare_term;
};

cproper_interval_term ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => Maybe (Term a b) -> Maybe (Term a b) -> Bool;
cproper_interval_term = (\ _ _ -> False);

instance (Compare.Compare a,
           Compare.Compare b) => Arith.Cproper_interval (Term a b) where {
  cproper_interval = cproper_interval_term;
};

data Atom a = Leq Arith.Nat a | Geq Arith.Nat a;

equal_atom :: forall a. (Eq a) => Atom a -> Atom a -> Bool;
equal_atom (Leq x11 x12) (Geq x21 x22) = False;
equal_atom (Geq x21 x22) (Leq x11 x12) = False;
equal_atom (Geq x21 x22) (Geq y21 y22) = Arith.equal_nat x21 y21 && x22 == y22;
equal_atom (Leq x11 x12) (Leq y11 y12) = Arith.equal_nat x11 y11 && x12 == y12;

ceq_atom :: forall a. (Eq a) => Maybe (Atom a -> Atom a -> Bool);
ceq_atom = Just equal_atom;

instance (Eq a) => Arith.Ceq (Atom a) where {
  ceq = ceq_atom;
};

set_impl_atom :: forall a. Phantom_Type.Phantom (Atom a) Arith.Set_impla;
set_impl_atom = Phantom_Type.Phantom Arith.Set_RBT;

instance Arith.Set_impl (Atom a) where {
  set_impl = set_impl_atom;
};

comparator_atom ::
  forall a.
    (a -> a -> Comparator.Order) -> Atom a -> Atom a -> Comparator.Order;
comparator_atom comp_a (Leq x xa) (Leq y ya) =
  (case Comparator.comparator_of x y of {
    Comparator.Eqa -> comp_a xa ya;
    Comparator.Lt -> Comparator.Lt;
    Comparator.Gt -> Comparator.Gt;
  });
comparator_atom comp_a (Leq x xa) (Geq yb yc) = Comparator.Lt;
comparator_atom comp_a (Geq x xa) (Leq y ya) = Comparator.Gt;
comparator_atom comp_a (Geq x xa) (Geq yb yc) =
  (case Comparator.comparator_of x yb of {
    Comparator.Eqa -> comp_a xa yc;
    Comparator.Lt -> Comparator.Lt;
    Comparator.Gt -> Comparator.Gt;
  });

ccompare_atom ::
  forall a. (Arith.Ccompare a) => Maybe (Atom a -> Atom a -> Comparator.Order);
ccompare_atom = (case Arith.ccompare of {
                  Nothing -> Nothing;
                  Just comp_a -> Just (comparator_atom comp_a);
                });

instance (Arith.Ccompare a) => Arith.Ccompare (Atom a) where {
  ccompare = ccompare_atom;
};

data Trans_var a = Pre a | Post a | Intermediate a;

equal_trans_var :: forall a. (Eq a) => Trans_var a -> Trans_var a -> Bool;
equal_trans_var (Post x2) (Intermediate x3) = False;
equal_trans_var (Intermediate x3) (Post x2) = False;
equal_trans_var (Pre x1) (Intermediate x3) = False;
equal_trans_var (Intermediate x3) (Pre x1) = False;
equal_trans_var (Pre x1) (Post x2) = False;
equal_trans_var (Post x2) (Pre x1) = False;
equal_trans_var (Intermediate x3) (Intermediate y3) = x3 == y3;
equal_trans_var (Post x2) (Post y2) = x2 == y2;
equal_trans_var (Pre x1) (Pre y1) = x1 == y1;

instance (Eq a) => Eq (Trans_var a) where {
  a == b = equal_trans_var a b;
};

comparator_trans_var ::
  forall a.
    (a -> a -> Comparator.Order) ->
      Trans_var a -> Trans_var a -> Comparator.Order;
comparator_trans_var comp_v (Pre x) (Pre y) = comp_v x y;
comparator_trans_var comp_v (Pre x) (Post ya) = Comparator.Lt;
comparator_trans_var comp_v (Pre x) (Intermediate yb) = Comparator.Lt;
comparator_trans_var comp_v (Post x) (Pre y) = Comparator.Gt;
comparator_trans_var comp_v (Post x) (Post ya) = comp_v x ya;
comparator_trans_var comp_v (Post x) (Intermediate yb) = Comparator.Lt;
comparator_trans_var comp_v (Intermediate x) (Pre y) = Comparator.Gt;
comparator_trans_var comp_v (Intermediate x) (Post ya) = Comparator.Gt;
comparator_trans_var comp_v (Intermediate x) (Intermediate yb) = comp_v x yb;

compare_trans_var ::
  forall a.
    (Compare.Compare a) => Trans_var a -> Trans_var a -> Comparator.Order;
compare_trans_var = comparator_trans_var Compare.compare;

less_eq_trans_var ::
  forall a. (Compare.Compare a) => Trans_var a -> Trans_var a -> Bool;
less_eq_trans_var = Comparator.le_of_comp compare_trans_var;

less_trans_var ::
  forall a. (Compare.Compare a) => Trans_var a -> Trans_var a -> Bool;
less_trans_var = Comparator.lt_of_comp compare_trans_var;

instance (Compare.Compare a) => Quasi_Order.Ord (Trans_var a) where {
  less_eq = less_eq_trans_var;
  less = less_trans_var;
};

instance (Compare.Compare a) => Quasi_Order.Quasi_order (Trans_var a) where {
};

instance (Compare.Compare a) => Quasi_Order.Weak_order (Trans_var a) where {
};

instance (Compare.Compare a) => Quasi_Order.Preorder (Trans_var a) where {
};

instance (Compare.Compare a) => Quasi_Order.Order (Trans_var a) where {
};

instance (Compare.Compare a) => Quasi_Order.Linorder (Trans_var a) where {
};

showsl_trans_var ::
  forall a. (Shows_Literal.Showl a) => Trans_var a -> String -> String;
showsl_trans_var (Pre v) = Shows_Literal.showsl v;
showsl_trans_var (Post v) =
  Shows_Literal.showsl v . Shows_Literal.showsl_lit "\'";
showsl_trans_var (Intermediate v) =
  Shows_Literal.showsl v . Shows_Literal.showsl_lit "#";

showsl_list_trans_var ::
  forall a. (Shows_Literal.Showl a) => [Trans_var a] -> String -> String;
showsl_list_trans_var xs =
  Shows_Literal.default_showsl_list showsl_trans_var xs;

instance (Shows_Literal.Showl a) => Shows_Literal.Showl (Trans_var a) where {
  showsl = showsl_trans_var;
  showsl_list = showsl_list_trans_var;
};

ccompare_trans_var ::
  forall a.
    (Arith.Ccompare a) => Maybe (Trans_var a ->
                                  Trans_var a -> Comparator.Order);
ccompare_trans_var = (case Arith.ccompare of {
                       Nothing -> Nothing;
                       Just comp_v -> Just (comparator_trans_var comp_v);
                     });

instance (Arith.Ccompare a) => Arith.Ccompare (Trans_var a) where {
  ccompare = ccompare_trans_var;
};

mapping_impl_trans_var ::
  forall a. Phantom_Type.Phantom (Trans_var a) Mapping.Mapping_impla;
mapping_impl_trans_var = Phantom_Type.Phantom Mapping.Mapping_RBT;

instance Mapping.Mapping_impl (Trans_var a) where {
  mapping_impl = mapping_impl_trans_var;
};

ceq_lab ::
  forall a b.
    (Eq a, Eq b) => Maybe (Labelings.Lab a b -> Labelings.Lab a b -> Bool);
ceq_lab = Just Labelings.equal_lab;

instance (Eq a, Eq b) => Arith.Ceq (Labelings.Lab a b) where {
  ceq = ceq_lab;
};

set_impl_lab ::
  forall a b. Phantom_Type.Phantom (Labelings.Lab a b) Arith.Set_impla;
set_impl_lab = Phantom_Type.Phantom Arith.Set_RBT;

instance Arith.Set_impl (Labelings.Lab a b) where {
  set_impl = set_impl_lab;
};

finite_UNIV_lab :: forall a b. Phantom_Type.Phantom (Labelings.Lab a b) Bool;
finite_UNIV_lab = Phantom_Type.Phantom False;

card_UNIV_lab :: forall a b. Phantom_Type.Phantom (Labelings.Lab a b) Arith.Nat;
card_UNIV_lab = Phantom_Type.Phantom Arith.zero_nat;

instance Arith.Finite_UNIV (Labelings.Lab a b) where {
  finite_UNIV = finite_UNIV_lab;
};

instance Arith.Card_UNIV (Labelings.Lab a b) where {
  card_UNIV = card_UNIV_lab;
};

cEnum_lab ::
  forall a b.
    Maybe ([Labelings.Lab a b],
            ((Labelings.Lab a b -> Bool) -> Bool,
              (Labelings.Lab a b -> Bool) -> Bool));
cEnum_lab = Nothing;

instance Arith.Cenum (Labelings.Lab a b) where {
  cEnum = cEnum_lab;
};

ccompare_lab ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => Maybe (Labelings.Lab a b ->
                                    Labelings.Lab a b -> Comparator.Order);
ccompare_lab = Just Labelings_Impl.compare_lab;

instance (Compare.Compare a,
           Compare.Compare b) => Arith.Ccompare (Labelings.Lab a b) where {
  ccompare = ccompare_lab;
};

mapping_impl_lab ::
  forall a b. Phantom_Type.Phantom (Labelings.Lab a b) Mapping.Mapping_impla;
mapping_impl_lab = Phantom_Type.Phantom Mapping.Mapping_RBT;

instance Mapping.Mapping_impl (Labelings.Lab a b) where {
  mapping_impl = mapping_impl_lab;
};

cproper_interval_lab ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => Maybe (Labelings.Lab a b) ->
                              Maybe (Labelings.Lab a b) -> Bool;
cproper_interval_lab = (\ _ _ -> False);

instance (Compare.Compare a,
           Compare.Compare b) => Arith.Cproper_interval (Labelings.Lab a
                  b) where {
  cproper_interval = cproper_interval_lab;
};

ccompare_QDelta :: Maybe (QDelta.QDelta -> QDelta.QDelta -> Comparator.Order);
ccompare_QDelta = Just Comparator.comparator_of;

instance Arith.Ccompare QDelta.QDelta where {
  ccompare = ccompare_QDelta;
};

data Formula a = Atom a | NegAtom a | Conjunction [Formula a]
  | Disjunction [Formula a];

instance (Eq a) => Eq (Formula a) where {
  a == b = equal_formula a b;
};

equal_formula :: forall a. (Eq a) => Formula a -> Formula a -> Bool;
equal_formula (Conjunction x3) (Disjunction x4) = False;
equal_formula (Disjunction x4) (Conjunction x3) = False;
equal_formula (NegAtom x2) (Disjunction x4) = False;
equal_formula (Disjunction x4) (NegAtom x2) = False;
equal_formula (NegAtom x2) (Conjunction x3) = False;
equal_formula (Conjunction x3) (NegAtom x2) = False;
equal_formula (Atom x1) (Disjunction x4) = False;
equal_formula (Disjunction x4) (Atom x1) = False;
equal_formula (Atom x1) (Conjunction x3) = False;
equal_formula (Conjunction x3) (Atom x1) = False;
equal_formula (Atom x1) (NegAtom x2) = False;
equal_formula (NegAtom x2) (Atom x1) = False;
equal_formula (Disjunction x4) (Disjunction y4) = x4 == y4;
equal_formula (Conjunction x3) (Conjunction y3) = x3 == y3;
equal_formula (NegAtom x2) (NegAtom y2) = x2 == y2;
equal_formula (Atom x1) (Atom y1) = x1 == y1;

data Transition_rule a b c d =
  Transition d d (Formula (Term a (Trans_var b, c)));

equal_transition_rule ::
  forall a b c d.
    (Eq a, Eq b, Eq c,
      Eq d) => Transition_rule a b c d -> Transition_rule a b c d -> Bool;
equal_transition_rule (Transition x1 x2 x3) (Transition y1 y2 y3) =
  x1 == y1 && x2 == y2 && equal_formula x3 y3;

ceq_transition_rule ::
  forall a b c d.
    (Eq a, Eq b, Eq c,
      Eq d) => Maybe (Transition_rule a b c d ->
                       Transition_rule a b c d -> Bool);
ceq_transition_rule = Just equal_transition_rule;

instance (Eq a, Eq b, Eq c, Eq d) => Arith.Ceq (Transition_rule a b c d) where {
  ceq = ceq_transition_rule;
};

set_impl_transition_rule ::
  forall a b c d.
    Phantom_Type.Phantom (Transition_rule a b c d) Arith.Set_impla;
set_impl_transition_rule = Phantom_Type.Phantom Arith.Set_RBT;

instance Arith.Set_impl (Transition_rule a b c d) where {
  set_impl = set_impl_transition_rule;
};

comparator_formula ::
  forall a.
    (a -> a -> Comparator.Order) -> Formula a -> Formula a -> Comparator.Order;
comparator_formula comp_a (Atom x) (Atom y) = comp_a x y;
comparator_formula comp_a (Atom x) (NegAtom ya) = Comparator.Lt;
comparator_formula comp_a (Atom x) (Conjunction yb) = Comparator.Lt;
comparator_formula comp_a (Atom x) (Disjunction yc) = Comparator.Lt;
comparator_formula comp_a (NegAtom x) (Atom y) = Comparator.Gt;
comparator_formula comp_a (NegAtom x) (NegAtom ya) = comp_a x ya;
comparator_formula comp_a (NegAtom x) (Conjunction yb) = Comparator.Lt;
comparator_formula comp_a (NegAtom x) (Disjunction yc) = Comparator.Lt;
comparator_formula comp_a (Conjunction x) (Atom y) = Comparator.Gt;
comparator_formula comp_a (Conjunction x) (NegAtom ya) = Comparator.Gt;
comparator_formula comp_a (Conjunction x) (Conjunction yb) =
  Arith.comparator_list (comparator_formula comp_a) x yb;
comparator_formula comp_a (Conjunction x) (Disjunction yc) = Comparator.Lt;
comparator_formula comp_a (Disjunction x) (Atom y) = Comparator.Gt;
comparator_formula comp_a (Disjunction x) (NegAtom ya) = Comparator.Gt;
comparator_formula comp_a (Disjunction x) (Conjunction yb) = Comparator.Gt;
comparator_formula comp_a (Disjunction x) (Disjunction yc) =
  Arith.comparator_list (comparator_formula comp_a) x yc;

comparator_transition_rule ::
  forall a b c d.
    (a -> a -> Comparator.Order) ->
      (b -> b -> Comparator.Order) ->
        (c -> c -> Comparator.Order) ->
          (d -> d -> Comparator.Order) ->
            Transition_rule a b c d ->
              Transition_rule a b c d -> Comparator.Order;
comparator_transition_rule comp_f comp_v comp_t comp_l (Transition x xa xb)
  (Transition y ya yb) =
  (case comp_l x y of {
    Comparator.Eqa ->
      (case comp_l xa ya of {
        Comparator.Eqa ->
          comparator_formula
            (comparator_term comp_f
              (Arith.comparator_prod (comparator_trans_var comp_v) comp_t))
            xb yb;
        Comparator.Lt -> Comparator.Lt;
        Comparator.Gt -> Comparator.Gt;
      });
    Comparator.Lt -> Comparator.Lt;
    Comparator.Gt -> Comparator.Gt;
  });

ccompare_transition_rule ::
  forall a b c d.
    (Arith.Ccompare a, Arith.Ccompare b, Arith.Ccompare c,
      Arith.Ccompare d) => Maybe (Transition_rule a b c d ->
                                   Transition_rule a b c d -> Comparator.Order);
ccompare_transition_rule =
  (case Arith.ccompare of {
    Nothing -> Nothing;
    Just comp_f ->
      (case Arith.ccompare of {
        Nothing -> Nothing;
        Just comp_v ->
          (case Arith.ccompare of {
            Nothing -> Nothing;
            Just comp_t ->
              (case Arith.ccompare of {
                Nothing -> Nothing;
                Just comp_l ->
                  Just (comparator_transition_rule comp_f comp_v comp_t comp_l);
              });
          });
      });
  });

instance (Arith.Ccompare a, Arith.Ccompare b, Arith.Ccompare c,
           Arith.Ccompare d) => Arith.Ccompare (Transition_rule a b c d) where {
  ccompare = ccompare_transition_rule;
};

data Gctxt a b = GCHole | GCFun a [Gctxt a b];

instance (Eq a) => Eq (Gctxt a b) where {
  a == b = equal_gctxt a b;
};

equal_gctxt :: forall a b. (Eq a) => Gctxt a b -> Gctxt a b -> Bool;
equal_gctxt GCHole (GCFun x21 x22) = False;
equal_gctxt (GCFun x21 x22) GCHole = False;
equal_gctxt (GCFun x21 x22) (GCFun y21 y22) = x21 == y21 && x22 == y22;
equal_gctxt GCHole GCHole = True;

ceq_gctxt :: forall a b. (Eq a) => Maybe (Gctxt a b -> Gctxt a b -> Bool);
ceq_gctxt = Just equal_gctxt;

instance (Eq a) => Arith.Ceq (Gctxt a b) where {
  ceq = ceq_gctxt;
};

set_impl_gctxt :: forall a b. Phantom_Type.Phantom (Gctxt a b) Arith.Set_impla;
set_impl_gctxt = Phantom_Type.Phantom Arith.Set_RBT;

instance Arith.Set_impl (Gctxt a b) where {
  set_impl = set_impl_gctxt;
};

comparator_gctxt ::
  forall a b.
    (a -> a -> Comparator.Order) -> Gctxt a b -> Gctxt a b -> Comparator.Order;
comparator_gctxt comp_f GCHole GCHole = Comparator.Eqa;
comparator_gctxt comp_f GCHole (GCFun y ya) = Comparator.Lt;
comparator_gctxt comp_f (GCFun x xa) GCHole = Comparator.Gt;
comparator_gctxt comp_f (GCFun x xa) (GCFun y ya) =
  (case comp_f x y of {
    Comparator.Eqa -> Arith.comparator_list (comparator_gctxt comp_f) xa ya;
    Comparator.Lt -> Comparator.Lt;
    Comparator.Gt -> Comparator.Gt;
  });

compare_gctxt ::
  forall a b. (Compare.Compare a) => Gctxt a b -> Gctxt a b -> Comparator.Order;
compare_gctxt = comparator_gctxt Compare.compare;

ccompare_gctxt ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => Maybe (Gctxt a b -> Gctxt a b -> Comparator.Order);
ccompare_gctxt = Just compare_gctxt;

instance (Compare.Compare a,
           Compare.Compare b) => Arith.Ccompare (Gctxt a b) where {
  ccompare = ccompare_gctxt;
};

data Ta_rule a b = TA_rule b [a] a;

equal_ta_rule :: forall a b. (Eq a, Eq b) => Ta_rule a b -> Ta_rule a b -> Bool;
equal_ta_rule (TA_rule x1 x2 x3) (TA_rule y1 y2 y3) =
  x1 == y1 && x2 == y2 && x3 == y3;

instance (Eq a, Eq b) => Eq (Ta_rule a b) where {
  a == b = equal_ta_rule a b;
};

comparator_ta_rule ::
  forall a b.
    (a -> a -> Comparator.Order) ->
      (b -> b -> Comparator.Order) ->
        Ta_rule a b -> Ta_rule a b -> Comparator.Order;
comparator_ta_rule comp_q comp_f (TA_rule x xa xb) (TA_rule y ya yb) =
  (case comp_f x y of {
    Comparator.Eqa -> (case Arith.comparator_list comp_q xa ya of {
                        Comparator.Eqa -> comp_q xb yb;
                        Comparator.Lt -> Comparator.Lt;
                        Comparator.Gt -> Comparator.Gt;
                      });
    Comparator.Lt -> Comparator.Lt;
    Comparator.Gt -> Comparator.Gt;
  });

compare_ta_rule ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => Ta_rule a b -> Ta_rule a b -> Comparator.Order;
compare_ta_rule = comparator_ta_rule Compare.compare Compare.compare;

less_eq_ta_rule ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => Ta_rule a b -> Ta_rule a b -> Bool;
less_eq_ta_rule = Comparator.le_of_comp compare_ta_rule;

less_ta_rule ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => Ta_rule a b -> Ta_rule a b -> Bool;
less_ta_rule = Comparator.lt_of_comp compare_ta_rule;

instance (Compare.Compare a,
           Compare.Compare b) => Quasi_Order.Ord (Ta_rule a b) where {
  less_eq = less_eq_ta_rule;
  less = less_ta_rule;
};

instance (Compare.Compare a,
           Compare.Compare b) => Quasi_Order.Quasi_order (Ta_rule a b) where {
};

instance (Compare.Compare a,
           Compare.Compare b) => Quasi_Order.Weak_order (Ta_rule a b) where {
};

instance (Compare.Compare a,
           Compare.Compare b) => Quasi_Order.Preorder (Ta_rule a b) where {
};

instance (Compare.Compare a,
           Compare.Compare b) => Quasi_Order.Order (Ta_rule a b) where {
};

ceq_ta_rule ::
  forall a b. (Eq a, Eq b) => Maybe (Ta_rule a b -> Ta_rule a b -> Bool);
ceq_ta_rule = Just equal_ta_rule;

instance (Eq a, Eq b) => Arith.Ceq (Ta_rule a b) where {
  ceq = ceq_ta_rule;
};

set_impl_ta_rule ::
  forall a b. Phantom_Type.Phantom (Ta_rule a b) Arith.Set_impla;
set_impl_ta_rule = Phantom_Type.Phantom Arith.Set_RBT;

instance Arith.Set_impl (Ta_rule a b) where {
  set_impl = set_impl_ta_rule;
};

instance (Compare.Compare a,
           Compare.Compare b) => Quasi_Order.Linorder (Ta_rule a b) where {
};

cEnum_ta_rule ::
  forall a b.
    Maybe ([Ta_rule a b],
            ((Ta_rule a b -> Bool) -> Bool, (Ta_rule a b -> Bool) -> Bool));
cEnum_ta_rule = Nothing;

instance Arith.Cenum (Ta_rule a b) where {
  cEnum = cEnum_ta_rule;
};

finite_UNIV_ta_rule :: forall a b. Phantom_Type.Phantom (Ta_rule a b) Bool;
finite_UNIV_ta_rule = Phantom_Type.Phantom False;

instance Arith.Finite_UNIV (Ta_rule a b) where {
  finite_UNIV = finite_UNIV_ta_rule;
};

ccompare_ta_rule ::
  forall a b.
    (Arith.Ccompare a,
      Arith.Ccompare b) => Maybe (Ta_rule a b ->
                                   Ta_rule a b -> Comparator.Order);
ccompare_ta_rule =
  (case Arith.ccompare of {
    Nothing -> Nothing;
    Just comp_q -> (case Arith.ccompare of {
                     Nothing -> Nothing;
                     Just comp_f -> Just (comparator_ta_rule comp_q comp_f);
                   });
  });

instance (Arith.Ccompare a,
           Arith.Ccompare b) => Arith.Ccompare (Ta_rule a b) where {
  ccompare = ccompare_ta_rule;
};

cproper_interval_ta_rule ::
  forall a b.
    (Arith.Ccompare a,
      Arith.Ccompare b) => Maybe (Ta_rule a b) -> Maybe (Ta_rule a b) -> Bool;
cproper_interval_ta_rule = (\ _ _ -> False);

instance (Arith.Ccompare a,
           Arith.Ccompare b) => Arith.Cproper_interval (Ta_rule a b) where {
  cproper_interval = cproper_interval_ta_rule;
};

data Mctxt a b = MVar b | MHole | MFun a [Mctxt a b];

instance (Eq a, Eq b) => Eq (Mctxt a b) where {
  a == b = equal_mctxt a b;
};

equal_mctxt :: forall a b. (Eq a, Eq b) => Mctxt a b -> Mctxt a b -> Bool;
equal_mctxt MHole (MFun x31 x32) = False;
equal_mctxt (MFun x31 x32) MHole = False;
equal_mctxt (MVar x1) (MFun x31 x32) = False;
equal_mctxt (MFun x31 x32) (MVar x1) = False;
equal_mctxt (MVar x1) MHole = False;
equal_mctxt MHole (MVar x1) = False;
equal_mctxt (MFun x31 x32) (MFun y31 y32) = x31 == y31 && x32 == y32;
equal_mctxt (MVar x1) (MVar y1) = x1 == y1;
equal_mctxt MHole MHole = True;

ceq_mctxt :: forall a b. (Eq a, Eq b) => Maybe (Mctxt a b -> Mctxt a b -> Bool);
ceq_mctxt = Just equal_mctxt;

instance (Eq a, Eq b) => Arith.Ceq (Mctxt a b) where {
  ceq = ceq_mctxt;
};

set_impl_mctxt :: forall a b. Phantom_Type.Phantom (Mctxt a b) Arith.Set_impla;
set_impl_mctxt = Phantom_Type.Phantom Arith.Set_RBT;

instance Arith.Set_impl (Mctxt a b) where {
  set_impl = set_impl_mctxt;
};

comparator_mctxt ::
  forall a b.
    (a -> a -> Comparator.Order) ->
      (b -> b -> Comparator.Order) ->
        Mctxt a b -> Mctxt a b -> Comparator.Order;
comparator_mctxt comp_f comp_v (MVar x) (MVar y) = comp_v x y;
comparator_mctxt comp_f comp_v (MVar x) MHole = Comparator.Lt;
comparator_mctxt comp_f comp_v (MVar x) (MFun ya yb) = Comparator.Lt;
comparator_mctxt comp_f comp_v MHole (MVar y) = Comparator.Gt;
comparator_mctxt comp_f comp_v MHole MHole = Comparator.Eqa;
comparator_mctxt comp_f comp_v MHole (MFun ya yb) = Comparator.Lt;
comparator_mctxt comp_f comp_v (MFun x xa) (MVar y) = Comparator.Gt;
comparator_mctxt comp_f comp_v (MFun x xa) MHole = Comparator.Gt;
comparator_mctxt comp_f comp_v (MFun x xa) (MFun ya yb) =
  (case comp_f x ya of {
    Comparator.Eqa ->
      Arith.comparator_list (comparator_mctxt comp_f comp_v) xa yb;
    Comparator.Lt -> Comparator.Lt;
    Comparator.Gt -> Comparator.Gt;
  });

compare_mctxt ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => Mctxt a b -> Mctxt a b -> Comparator.Order;
compare_mctxt = comparator_mctxt Compare.compare Compare.compare;

ccompare_mctxt ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => Maybe (Mctxt a b -> Mctxt a b -> Comparator.Order);
ccompare_mctxt = Just compare_mctxt;

instance (Compare.Compare a,
           Compare.Compare b) => Arith.Ccompare (Mctxt a b) where {
  ccompare = ccompare_mctxt;
};

ceq_arctic ::
  Maybe (SN_Order_Carrier.Arctic -> SN_Order_Carrier.Arctic -> Bool);
ceq_arctic = Just SN_Order_Carrier.equal_arctic;

instance Arith.Ceq SN_Order_Carrier.Arctic where {
  ceq = ceq_arctic;
};

set_impl_arctic :: Phantom_Type.Phantom SN_Order_Carrier.Arctic Arith.Set_impla;
set_impl_arctic = Phantom_Type.Phantom Arith.Set_RBT;

instance Arith.Set_impl SN_Order_Carrier.Arctic where {
  set_impl = set_impl_arctic;
};

cEnum_arctic ::
  Maybe ([SN_Order_Carrier.Arctic],
          ((SN_Order_Carrier.Arctic -> Bool) -> Bool,
            (SN_Order_Carrier.Arctic -> Bool) -> Bool));
cEnum_arctic = Nothing;

instance Arith.Cenum SN_Order_Carrier.Arctic where {
  cEnum = cEnum_arctic;
};

comparator_arctic ::
  SN_Order_Carrier.Arctic -> SN_Order_Carrier.Arctic -> Comparator.Order;
comparator_arctic SN_Order_Carrier.MinInfty SN_Order_Carrier.MinInfty =
  Comparator.Eqa;
comparator_arctic SN_Order_Carrier.MinInfty (SN_Order_Carrier.Num_arc y) =
  Comparator.Lt;
comparator_arctic (SN_Order_Carrier.Num_arc x) SN_Order_Carrier.MinInfty =
  Comparator.Gt;
comparator_arctic (SN_Order_Carrier.Num_arc x) (SN_Order_Carrier.Num_arc y) =
  Comparator.comparator_of x y;

compare_arctic ::
  SN_Order_Carrier.Arctic -> SN_Order_Carrier.Arctic -> Comparator.Order;
compare_arctic = comparator_arctic;

ccompare_arctic ::
  Maybe (SN_Order_Carrier.Arctic ->
          SN_Order_Carrier.Arctic -> Comparator.Order);
ccompare_arctic = Just compare_arctic;

instance Arith.Ccompare SN_Order_Carrier.Arctic where {
  ccompare = ccompare_arctic;
};

data Filtered a = FPair a Arith.Nat;

equal_filtered :: forall a. (Eq a) => Filtered a -> Filtered a -> Bool;
equal_filtered (FPair x1 x2) (FPair y1 y2) = x1 == y1 && Arith.equal_nat x2 y2;

instance (Eq a) => Eq (Filtered a) where {
  a == b = equal_filtered a b;
};

comparator_filtered ::
  forall a.
    (a -> a -> Comparator.Order) ->
      Filtered a -> Filtered a -> Comparator.Order;
comparator_filtered comp_f (FPair x xa) (FPair y ya) =
  (case comp_f x y of {
    Comparator.Eqa -> Comparator.comparator_of xa ya;
    Comparator.Lt -> Comparator.Lt;
    Comparator.Gt -> Comparator.Gt;
  });

compare_filtered ::
  forall a. (Compare.Compare a) => Filtered a -> Filtered a -> Comparator.Order;
compare_filtered = comparator_filtered Compare.compare;

less_eq_filtered ::
  forall a. (Compare.Compare a) => Filtered a -> Filtered a -> Bool;
less_eq_filtered = Comparator.le_of_comp compare_filtered;

less_filtered ::
  forall a. (Compare.Compare a) => Filtered a -> Filtered a -> Bool;
less_filtered = Comparator.lt_of_comp compare_filtered;

instance (Compare.Compare a) => Quasi_Order.Ord (Filtered a) where {
  less_eq = less_eq_filtered;
  less = less_filtered;
};

instance (Compare.Compare a) => Compare.Compare (Filtered a) where {
  compare = compare_filtered;
};

instance (Compare.Compare a) => Quasi_Order.Quasi_order (Filtered a) where {
};

instance (Compare.Compare a) => Quasi_Order.Weak_order (Filtered a) where {
};

instance (Compare.Compare a) => Quasi_Order.Preorder (Filtered a) where {
};

instance (Compare.Compare a) => Quasi_Order.Order (Filtered a) where {
};

equality_filtered ::
  forall a. (a -> a -> Bool) -> Filtered a -> Filtered a -> Bool;
equality_filtered eq_f (FPair x xa) (FPair y ya) =
  eq_f x y && Arith.equal_nat xa ya;

ceq_filtered ::
  forall a. (Arith.Ceq a) => Maybe (Filtered a -> Filtered a -> Bool);
ceq_filtered = (case Arith.ceq of {
                 Nothing -> Nothing;
                 Just eq_f -> Just (equality_filtered eq_f);
               });

instance (Arith.Ceq a) => Arith.Ceq (Filtered a) where {
  ceq = ceq_filtered;
};

set_impl_filtered ::
  forall a.
    (Arith.Set_impl a) => Phantom_Type.Phantom (Filtered a) Arith.Set_impla;
set_impl_filtered =
  Phantom_Type.Phantom
    (Phantom_Type.of_phantom
      (Arith.set_impl :: Phantom_Type.Phantom a Arith.Set_impla));

instance (Arith.Set_impl a) => Arith.Set_impl (Filtered a) where {
  set_impl = set_impl_filtered;
};

instance (Compare.Compare a) => Quasi_Order.Linorder (Filtered a) where {
};

filtered_fun :: forall a. Filtered a -> a;
filtered_fun (FPair f n) = f;

showsl_filtered ::
  forall a. (Shows_Literal.Showl a) => Filtered a -> String -> String;
showsl_filtered f = Shows_Literal.showsl (filtered_fun f);

showsl_list_filtered ::
  forall a. (Shows_Literal.Showl a) => [Filtered a] -> String -> String;
showsl_list_filtered xs = Shows_Literal.default_showsl_list showsl_filtered xs;

instance (Shows_Literal.Showl a) => Shows_Literal.Showl (Filtered a) where {
  showsl = showsl_filtered;
  showsl_list = showsl_list_filtered;
};

instance (Compare.Compare a) => Compare.Compare_order (Filtered a) where {
};

ccompare_filtered ::
  forall a.
    (Arith.Ccompare a) => Maybe (Filtered a -> Filtered a -> Comparator.Order);
ccompare_filtered = (case Arith.ccompare of {
                      Nothing -> Nothing;
                      Just comp_f -> Just (comparator_filtered comp_f);
                    });

instance (Arith.Ccompare a) => Arith.Ccompare (Filtered a) where {
  ccompare = ccompare_filtered;
};

cEnum_l_poly ::
  forall a b.
    Maybe ([Linear_Polynomial.L_poly a b],
            ((Linear_Polynomial.L_poly a b -> Bool) -> Bool,
              (Linear_Polynomial.L_poly a b -> Bool) -> Bool));
cEnum_l_poly = Nothing;

instance Arith.Cenum (Linear_Polynomial.L_poly a b) where {
  cEnum = cEnum_l_poly;
};

data Sharp a = Flat a | Sharp a;

equal_sharp :: forall a. (Eq a) => Sharp a -> Sharp a -> Bool;
equal_sharp (Flat x1) (Sharp x2) = False;
equal_sharp (Sharp x2) (Flat x1) = False;
equal_sharp (Sharp x2) (Sharp y2) = x2 == y2;
equal_sharp (Flat x1) (Flat y1) = x1 == y1;

instance (Eq a) => Eq (Sharp a) where {
  a == b = equal_sharp a b;
};

comparator_sharp ::
  forall a.
    (a -> a -> Comparator.Order) -> Sharp a -> Sharp a -> Comparator.Order;
comparator_sharp comp_l (Flat x) (Flat y) = comp_l x y;
comparator_sharp comp_l (Flat x) (Sharp ya) = Comparator.Lt;
comparator_sharp comp_l (Sharp x) (Flat y) = Comparator.Gt;
comparator_sharp comp_l (Sharp x) (Sharp ya) = comp_l x ya;

compare_sharp ::
  forall a. (Compare.Compare a) => Sharp a -> Sharp a -> Comparator.Order;
compare_sharp = comparator_sharp Compare.compare;

less_eq_sharp :: forall a. (Compare.Compare a) => Sharp a -> Sharp a -> Bool;
less_eq_sharp = Comparator.le_of_comp compare_sharp;

less_sharp :: forall a. (Compare.Compare a) => Sharp a -> Sharp a -> Bool;
less_sharp = Comparator.lt_of_comp compare_sharp;

instance (Compare.Compare a) => Quasi_Order.Ord (Sharp a) where {
  less_eq = less_eq_sharp;
  less = less_sharp;
};

instance (Compare.Compare a) => Compare.Compare (Sharp a) where {
  compare = compare_sharp;
};

instance (Compare.Compare a) => Quasi_Order.Quasi_order (Sharp a) where {
};

instance (Compare.Compare a) => Quasi_Order.Weak_order (Sharp a) where {
};

instance (Compare.Compare a) => Quasi_Order.Preorder (Sharp a) where {
};

instance (Compare.Compare a) => Quasi_Order.Order (Sharp a) where {
};

ceq_sharp :: forall a. (Eq a) => Maybe (Sharp a -> Sharp a -> Bool);
ceq_sharp = Just equal_sharp;

instance (Eq a) => Arith.Ceq (Sharp a) where {
  ceq = ceq_sharp;
};

set_impl_sharp :: forall a. Phantom_Type.Phantom (Sharp a) Arith.Set_impla;
set_impl_sharp = Phantom_Type.Phantom Arith.Set_RBT;

instance Arith.Set_impl (Sharp a) where {
  set_impl = set_impl_sharp;
};

instance (Compare.Compare a) => Quasi_Order.Linorder (Sharp a) where {
};

showsl_sharp ::
  forall a. (Shows_Literal.Showl a) => Sharp a -> String -> String;
showsl_sharp (Flat s) = Shows_Literal.showsl s;
showsl_sharp (Sharp s) = Shows_Literal.showsl_lit "#" . Shows_Literal.showsl s;

showsl_list_sharp ::
  forall a. (Shows_Literal.Showl a) => [Sharp a] -> String -> String;
showsl_list_sharp xs = Shows_Literal.default_showsl_list showsl_sharp xs;

instance (Shows_Literal.Showl a) => Shows_Literal.Showl (Sharp a) where {
  showsl = showsl_sharp;
  showsl_list = showsl_list_sharp;
};

cEnum_sharp ::
  forall a.
    Maybe ([Sharp a], ((Sharp a -> Bool) -> Bool, (Sharp a -> Bool) -> Bool));
cEnum_sharp = Nothing;

instance Arith.Cenum (Sharp a) where {
  cEnum = cEnum_sharp;
};

instance (Compare.Compare a) => Compare.Compare_order (Sharp a) where {
};

ccompare_sharp ::
  forall a.
    (Arith.Ccompare a) => Maybe (Sharp a -> Sharp a -> Comparator.Order);
ccompare_sharp = (case Arith.ccompare of {
                   Nothing -> Nothing;
                   Just comp_l -> Just (comparator_sharp comp_l);
                 });

instance (Arith.Ccompare a) => Arith.Ccompare (Sharp a) where {
  ccompare = ccompare_sharp;
};

mapping_impl_sharp ::
  forall a. Phantom_Type.Phantom (Sharp a) Mapping.Mapping_impla;
mapping_impl_sharp = Phantom_Type.Phantom Mapping.Mapping_RBT;

instance Mapping.Mapping_impl (Sharp a) where {
  mapping_impl = mapping_impl_sharp;
};

data Actxt a b = Hole | More a [b] (Actxt a b) [b];

equal_actxt :: forall a b. (Eq a, Eq b) => Actxt a b -> Actxt a b -> Bool;
equal_actxt Hole (More x21 x22 x23 x24) = False;
equal_actxt (More x21 x22 x23 x24) Hole = False;
equal_actxt (More x21 x22 x23 x24) (More y21 y22 y23 y24) =
  x21 == y21 && x22 == y22 && equal_actxt x23 y23 && x24 == y24;
equal_actxt Hole Hole = True;

instance (Eq a, Eq b) => Eq (Actxt a b) where {
  a == b = equal_actxt a b;
};

ceq_actxt :: forall a b. (Eq a, Eq b) => Maybe (Actxt a b -> Actxt a b -> Bool);
ceq_actxt = Just equal_actxt;

instance (Eq a, Eq b) => Arith.Ceq (Actxt a b) where {
  ceq = ceq_actxt;
};

set_impl_actxt :: forall a b. Phantom_Type.Phantom (Actxt a b) Arith.Set_impla;
set_impl_actxt = Phantom_Type.Phantom Arith.Set_RBT;

instance Arith.Set_impl (Actxt a b) where {
  set_impl = set_impl_actxt;
};

comparator_actxt ::
  forall a b.
    (a -> a -> Comparator.Order) ->
      (b -> b -> Comparator.Order) ->
        Actxt a b -> Actxt a b -> Comparator.Order;
comparator_actxt comp_f comp_a Hole Hole = Comparator.Eqa;
comparator_actxt comp_f comp_a Hole (More y ya yb yc) = Comparator.Lt;
comparator_actxt comp_f comp_a (More x xa xb xc) Hole = Comparator.Gt;
comparator_actxt comp_f comp_a (More x xa xb xc) (More y ya yb yc) =
  (case comp_f x y of {
    Comparator.Eqa ->
      (case Arith.comparator_list comp_a xa ya of {
        Comparator.Eqa ->
          (case comparator_actxt comp_f comp_a xb yb of {
            Comparator.Eqa -> Arith.comparator_list comp_a xc yc;
            Comparator.Lt -> Comparator.Lt;
            Comparator.Gt -> Comparator.Gt;
          });
        Comparator.Lt -> Comparator.Lt;
        Comparator.Gt -> Comparator.Gt;
      });
    Comparator.Lt -> Comparator.Lt;
    Comparator.Gt -> Comparator.Gt;
  });

compare_actxt ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => Actxt a b -> Actxt a b -> Comparator.Order;
compare_actxt = comparator_actxt Compare.compare Compare.compare;

ccompare_actxt ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => Maybe (Actxt a b -> Actxt a b -> Comparator.Order);
ccompare_actxt = Just compare_actxt;

instance (Compare.Compare a,
           Compare.Compare b) => Arith.Ccompare (Actxt a b) where {
  ccompare = ccompare_actxt;
};

ceq_location ::
  Maybe (Forbidden_Patterns.Location -> Forbidden_Patterns.Location -> Bool);
ceq_location = Just Forbidden_Patterns.equal_location;

instance Arith.Ceq Forbidden_Patterns.Location where {
  ceq = ceq_location;
};

set_impl_location ::
  Phantom_Type.Phantom Forbidden_Patterns.Location Arith.Set_impla;
set_impl_location = Phantom_Type.Phantom Arith.Set_RBT;

instance Arith.Set_impl Forbidden_Patterns.Location where {
  set_impl = set_impl_location;
};

comparator_location ::
  Forbidden_Patterns.Location ->
    Forbidden_Patterns.Location -> Comparator.Order;
comparator_location Forbidden_Patterns.H Forbidden_Patterns.H = Comparator.Eqa;
comparator_location Forbidden_Patterns.H Forbidden_Patterns.A = Comparator.Lt;
comparator_location Forbidden_Patterns.H Forbidden_Patterns.B = Comparator.Lt;
comparator_location Forbidden_Patterns.H Forbidden_Patterns.R = Comparator.Lt;
comparator_location Forbidden_Patterns.A Forbidden_Patterns.H = Comparator.Gt;
comparator_location Forbidden_Patterns.A Forbidden_Patterns.A = Comparator.Eqa;
comparator_location Forbidden_Patterns.A Forbidden_Patterns.B = Comparator.Lt;
comparator_location Forbidden_Patterns.A Forbidden_Patterns.R = Comparator.Lt;
comparator_location Forbidden_Patterns.B Forbidden_Patterns.H = Comparator.Gt;
comparator_location Forbidden_Patterns.B Forbidden_Patterns.A = Comparator.Gt;
comparator_location Forbidden_Patterns.B Forbidden_Patterns.B = Comparator.Eqa;
comparator_location Forbidden_Patterns.B Forbidden_Patterns.R = Comparator.Lt;
comparator_location Forbidden_Patterns.R Forbidden_Patterns.H = Comparator.Gt;
comparator_location Forbidden_Patterns.R Forbidden_Patterns.A = Comparator.Gt;
comparator_location Forbidden_Patterns.R Forbidden_Patterns.B = Comparator.Gt;
comparator_location Forbidden_Patterns.R Forbidden_Patterns.R = Comparator.Eqa;

compare_location ::
  Forbidden_Patterns.Location ->
    Forbidden_Patterns.Location -> Comparator.Order;
compare_location = comparator_location;

ccompare_location ::
  Maybe (Forbidden_Patterns.Location ->
          Forbidden_Patterns.Location -> Comparator.Order);
ccompare_location = Just compare_location;

instance Arith.Ccompare Forbidden_Patterns.Location where {
  ccompare = ccompare_location;
};

ceq_arctic_delta ::
  forall a.
    (Eq a) => Maybe (SN_Order_Carrier.Arctic_delta a ->
                      SN_Order_Carrier.Arctic_delta a -> Bool);
ceq_arctic_delta = Just SN_Order_Carrier.equal_arctic_delta;

instance (Eq a) => Arith.Ceq (SN_Order_Carrier.Arctic_delta a) where {
  ceq = ceq_arctic_delta;
};

set_impl_arctic_delta ::
  forall a.
    Phantom_Type.Phantom (SN_Order_Carrier.Arctic_delta a) Arith.Set_impla;
set_impl_arctic_delta = Phantom_Type.Phantom Arith.Set_RBT;

instance Arith.Set_impl (SN_Order_Carrier.Arctic_delta a) where {
  set_impl = set_impl_arctic_delta;
};

cEnum_arctic_delta ::
  forall a.
    Maybe ([SN_Order_Carrier.Arctic_delta a],
            ((SN_Order_Carrier.Arctic_delta a -> Bool) -> Bool,
              (SN_Order_Carrier.Arctic_delta a -> Bool) -> Bool));
cEnum_arctic_delta = Nothing;

instance Arith.Cenum (SN_Order_Carrier.Arctic_delta a) where {
  cEnum = cEnum_arctic_delta;
};

comparator_arctic_delta ::
  forall a.
    (a -> a -> Comparator.Order) ->
      SN_Order_Carrier.Arctic_delta a ->
        SN_Order_Carrier.Arctic_delta a -> Comparator.Order;
comparator_arctic_delta comp_a SN_Order_Carrier.MinInfty_delta
  SN_Order_Carrier.MinInfty_delta = Comparator.Eqa;
comparator_arctic_delta comp_a SN_Order_Carrier.MinInfty_delta
  (SN_Order_Carrier.Num_arc_delta y) = Comparator.Lt;
comparator_arctic_delta comp_a (SN_Order_Carrier.Num_arc_delta x)
  SN_Order_Carrier.MinInfty_delta = Comparator.Gt;
comparator_arctic_delta comp_a (SN_Order_Carrier.Num_arc_delta x)
  (SN_Order_Carrier.Num_arc_delta y) = comp_a x y;

compare_arctic_delta ::
  forall a.
    (Compare.Compare a) => SN_Order_Carrier.Arctic_delta a ->
                             SN_Order_Carrier.Arctic_delta a ->
                               Comparator.Order;
compare_arctic_delta = comparator_arctic_delta Compare.compare;

ccompare_arctic_delta ::
  forall a.
    (Compare.Compare a) => Maybe (SN_Order_Carrier.Arctic_delta a ->
                                   SN_Order_Carrier.Arctic_delta a ->
                                     Comparator.Order);
ccompare_arctic_delta = Just compare_arctic_delta;

instance (Compare.Compare a) => Arith.Ccompare (SN_Order_Carrier.Arctic_delta
         a) where {
  ccompare = ccompare_arctic_delta;
};

data Ty = BoolT | IntT;

equal_ty :: Ty -> Ty -> Bool;
equal_ty BoolT IntT = False;
equal_ty IntT BoolT = False;
equal_ty IntT IntT = True;
equal_ty BoolT BoolT = True;

instance Eq Ty where {
  a == b = equal_ty a b;
};

ceq_ty :: Maybe (Ty -> Ty -> Bool);
ceq_ty = Just equal_ty;

instance Arith.Ceq Ty where {
  ceq = ceq_ty;
};

showsl_ty :: Ty -> String -> String;
showsl_ty BoolT = Shows_Literal.showsl_lit "Bool";
showsl_ty IntT = Shows_Literal.showsl_lit "Int";

showsl_list_ty :: [Ty] -> String -> String;
showsl_list_ty xs = Shows_Literal.default_showsl_list showsl_ty xs;

instance Shows_Literal.Showl Ty where {
  showsl = showsl_ty;
  showsl_list = showsl_list_ty;
};

comparator_ty :: Ty -> Ty -> Comparator.Order;
comparator_ty BoolT BoolT = Comparator.Eqa;
comparator_ty BoolT IntT = Comparator.Lt;
comparator_ty IntT BoolT = Comparator.Gt;
comparator_ty IntT IntT = Comparator.Eqa;

ccompare_ty :: Maybe (Ty -> Ty -> Comparator.Order);
ccompare_ty = Just comparator_ty;

instance Arith.Ccompare Ty where {
  ccompare = ccompare_ty;
};

newtype Linear_poly = LinearPoly (Finite_Map.Fmap Arith.Nat Rat.Rat);

linear_poly_map :: Linear_poly -> Finite_Map.Fmap Arith.Nat Rat.Rat;
linear_poly_map (LinearPoly x) = x;

equal_linear_poly :: Linear_poly -> Linear_poly -> Bool;
equal_linear_poly x y =
  Finite_Map.equal_fmap (linear_poly_map x) (linear_poly_map y);

instance Eq Linear_poly where {
  a == b = equal_linear_poly a b;
};

data Sig = LessF | LeF | SumF Arith.Nat | ConstF Arith.Int | ProdF Arith.Nat
  | EqF;

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
equal_sig (ProdF x5) (ProdF y5) = Arith.equal_nat x5 y5;
equal_sig (ConstF x4) (ConstF y4) = Arith.equal_int x4 y4;
equal_sig (SumF x3) (SumF y3) = Arith.equal_nat x3 y3;
equal_sig EqF EqF = True;
equal_sig LeF LeF = True;
equal_sig LessF LessF = True;

instance Eq Sig where {
  a == b = equal_sig a b;
};

showsl_sig :: Sig -> String -> String;
showsl_sig LessF = Shows_Literal.showsl_lit "<";
showsl_sig LeF = Shows_Literal.showsl_lit "<=";
showsl_sig EqF = Shows_Literal.showsl_lit "=";
showsl_sig (SumF n) = Shows_Literal.showsl_lit "+";
showsl_sig (ProdF n) = Shows_Literal.showsl_lit "*";
showsl_sig (ConstF n) = Shows_Literal.showsl_int n;

showsl_list_sig :: [Sig] -> String -> String;
showsl_list_sig xs = Shows_Literal.default_showsl_list showsl_sig xs;

instance Shows_Literal.Showl Sig where {
  showsl = showsl_sig;
  showsl_list = showsl_list_sig;
};

comparator_sig :: Sig -> Sig -> Comparator.Order;
comparator_sig LessF LessF = Comparator.Eqa;
comparator_sig LessF LeF = Comparator.Lt;
comparator_sig LessF (SumF y) = Comparator.Lt;
comparator_sig LessF (ConstF ya) = Comparator.Lt;
comparator_sig LessF (ProdF yb) = Comparator.Lt;
comparator_sig LessF EqF = Comparator.Lt;
comparator_sig LeF LessF = Comparator.Gt;
comparator_sig LeF LeF = Comparator.Eqa;
comparator_sig LeF (SumF y) = Comparator.Lt;
comparator_sig LeF (ConstF ya) = Comparator.Lt;
comparator_sig LeF (ProdF yb) = Comparator.Lt;
comparator_sig LeF EqF = Comparator.Lt;
comparator_sig (SumF x) LessF = Comparator.Gt;
comparator_sig (SumF x) LeF = Comparator.Gt;
comparator_sig (SumF x) (SumF y) = Comparator.comparator_of x y;
comparator_sig (SumF x) (ConstF ya) = Comparator.Lt;
comparator_sig (SumF x) (ProdF yb) = Comparator.Lt;
comparator_sig (SumF x) EqF = Comparator.Lt;
comparator_sig (ConstF x) LessF = Comparator.Gt;
comparator_sig (ConstF x) LeF = Comparator.Gt;
comparator_sig (ConstF x) (SumF y) = Comparator.Gt;
comparator_sig (ConstF x) (ConstF ya) = Comparator.comparator_of x ya;
comparator_sig (ConstF x) (ProdF yb) = Comparator.Lt;
comparator_sig (ConstF x) EqF = Comparator.Lt;
comparator_sig (ProdF x) LessF = Comparator.Gt;
comparator_sig (ProdF x) LeF = Comparator.Gt;
comparator_sig (ProdF x) (SumF y) = Comparator.Gt;
comparator_sig (ProdF x) (ConstF ya) = Comparator.Gt;
comparator_sig (ProdF x) (ProdF yb) = Comparator.comparator_of x yb;
comparator_sig (ProdF x) EqF = Comparator.Lt;
comparator_sig EqF LessF = Comparator.Gt;
comparator_sig EqF LeF = Comparator.Gt;
comparator_sig EqF (SumF y) = Comparator.Gt;
comparator_sig EqF (ConstF ya) = Comparator.Gt;
comparator_sig EqF (ProdF yb) = Comparator.Gt;
comparator_sig EqF EqF = Comparator.Eqa;

ccompare_sig :: Maybe (Sig -> Sig -> Comparator.Order);
ccompare_sig = Just comparator_sig;

instance Arith.Ccompare Sig where {
  ccompare = ccompare_sig;
};

data Lts_impl a b c d e =
  Lts_Impl [d] [(e, Transition_rule a b c d)] [(d, Formula (Term a (b, c)))];

data State a b =
  State [(Arith.Nat, Linear_poly)] (Mapping.Mapping Arith.Nat (a, b))
    (Mapping.Mapping Arith.Nat (a, b)) (Mapping.Mapping Arith.Nat b) Bool
    (Maybe [a]);

data Istate a =
  IState Arith.Nat [(Arith.Nat, Linear_poly)] [(a, Atom QDelta.QDelta)]
    (Linear_poly -> Maybe Arith.Nat) [a];

data Lts_ext a b c d e =
  Lts_ext (Arith.Set d) (Arith.Set (Transition_rule a b c d))
    (d -> Formula (Term a (b, c))) e;

data Direction a b =
  Direction (b -> b -> Bool) (State a b -> Mapping.Mapping Arith.Nat (a, b))
    (State a b -> Mapping.Mapping Arith.Nat (a, b))
    (State a b -> Arith.Nat -> Maybe b) (State a b -> Arith.Nat -> Maybe b)
    (State a b -> Arith.Nat -> a) (State a b -> Arith.Nat -> a)
    ((Mapping.Mapping Arith.Nat (a, b) -> Mapping.Mapping Arith.Nat (a, b)) ->
      State a b -> State a b)
    (Arith.Nat -> b -> Atom b) (Arith.Nat -> b -> Atom b)
    (Rat.Rat -> Rat.Rat -> Bool);

data Constraint = LT Linear_poly Rat.Rat | GT Linear_poly Rat.Rat
  | LEQ Linear_poly Rat.Rat | GEQ Linear_poly Rat.Rat | EQ Linear_poly Rat.Rat;

data Af_entry = Collapse Arith.Nat | AFList [Arith.Nat];

newtype Afs a = Abs_afs ((a, Arith.Nat) -> Af_entry, Arith.Set (a, Arith.Nat));

data Ns_constraint a = LEQ_ns Linear_poly a | GEQ_ns Linear_poly a;

data Ta_ext a b c =
  Ta_ext (Arith.Set a) (Arith.Set (Ta_rule a b)) (Arith.Set (a, a)) c;

data Rel_impl_ext a b c =
  Rel_impl_ext (Sum_Type.Sum (String -> String) ())
    (Sum_Type.Sum (String -> String) ()) (String -> String)
    ((Term a b, Term a b) -> Sum_Type.Sum (String -> String) ())
    ((Term a b, Term a b) -> Sum_Type.Sum (String -> String) ())
    ((Term a b, Term a b) -> Sum_Type.Sum (String -> String) ())
    ((a, Arith.Nat) -> Arith.Set Arith.Nat)
    ((a, Arith.Nat) -> Arith.Set Arith.Nat) (Sum_Type.Sum (String -> String) ())
    (Sum_Type.Sum (String -> String) ()) (Sum_Type.Sum (String -> String) ())
    (Sum_Type.Sum (String -> String) ()) (Sum_Type.Sum (String -> String) ())
    (Sum_Type.Sum (String -> String) ()) ((a, Arith.Nat) -> Arith.Set Arith.Nat)
    ([(a, Arith.Nat)] -> Sum_Type.Sum (String -> String) ())
    (Maybe [(a, Arith.Nat)]) (Maybe [(a, Arith.Nat)])
    (Complexity.Complexity_measure a b ->
      Complexity.Complexity_class -> Sum_Type.Sum (String -> String) ())
    c;

newtype Rel_impl_type b a c = Abs_rel_impl_type (c -> Rel_impl_ext b a ());

data Poly_constraint a = Poly_Ge [(Polynomials.Monom a, Arith.Int)]
  | Poly_Eq [(Polynomials.Monom a, Arith.Int)];

newtype
  X_compare_order_x_x_f_afs_option_x_x_nat_x_compare_order_x_x_f_prod_set_af_entry_nat_x_compare_order_x_x_f_prod_fun_prod_option
    a
  = Abs_x_compare_order_x_x_f_afs_option_x_x_nat_x_compare_order_x_x_f_prod_set_af_entry_nat_x_compare_order_x_x_f_prod_fun_prod_option
  (Maybe ((a, Arith.Nat) -> Af_entry, Arith.Set (a, Arith.Nat)));

root :: forall a b. Term a b -> Maybe (a, Arith.Nat);
root (Var x) = Nothing;
root (Fun f ts) = Just (f, Arith.size_list ts);

transitions_impl ::
  forall a b c d e. Lts_impl a b c d e -> [(e, Transition_rule a b c d)];
transitions_impl (Lts_Impl x1 x2 x3) = x2;

initiala :: forall a b c d e. Lts_impl a b c d e -> [d];
initiala (Lts_Impl x1 x2 x3) = x1;

assertion_impl ::
  forall a b c d e. Lts_impl a b c d e -> [(d, Formula (Term a (b, c)))];
assertion_impl (Lts_Impl x1 x2 x3) = x3;

assertion_of ::
  forall a b c d e.
    (Arith.Ccompare d, Eq d,
      Mapping.Mapping_impl d) => Lts_impl a b c d e ->
                                   d -> Formula (Term a (b, c));
assertion_of pi = Map_Of.map_of_default (Conjunction []) (assertion_impl pi);

lts_of ::
  forall a b c d e.
    (Arith.Ccompare a, Eq a, Arith.Ccompare b, Eq b, Arith.Ccompare c, Eq c,
      Arith.Ceq d, Arith.Ccompare d, Eq d, Mapping.Mapping_impl d,
      Arith.Set_impl d, Arith.Ceq e, Arith.Ccompare e,
      Arith.Set_impl e) => Lts_impl a b c d e -> Lts_ext a b c d ();
lts_of pi =
  Lts_ext (Arith.set (initiala pi))
    (Arith.image snd (Arith.set (transitions_impl pi))) (assertion_of pi) ();

source :: forall a b c d. Transition_rule a b c d -> d;
source (Transition l uu uv) = l;

target :: forall a b c d. Transition_rule a b c d -> d;
target (Transition uu r uv) = r;

subst :: forall a b. (Eq a) => a -> Term b a -> a -> Term b a;
subst x t = Fun.fun_upd Var x t;

lhs :: (Arith.Nat, Linear_poly) -> Arith.Nat;
lhs (l, r) = l;

rhs :: (Arith.Nat, Linear_poly) -> Linear_poly;
rhs (l, r) = r;

ground :: forall a b. Term a b -> Bool;
ground (Var x) = False;
ground (Fun f ts) = all ground ts;

insert_vars_term :: forall a b. (Eq b) => Term a b -> [b] -> [b];
insert_vars_term (Var x) xs = Arith.inserta x xs;
insert_vars_term (Fun f ts) xs = Arith.foldr insert_vars_term ts xs;

is_Var :: forall a b. Term a b -> Bool;
is_Var (Var x1) = True;
is_Var (Fun x21 x22) = False;

wf_rule :: forall a b. (Eq b) => (Term a b, Term a b) -> Bool;
wf_rule r =
  not (is_Var (fst r)) &&
    all (Arith.membera (insert_vars_term (fst r) []))
      (insert_vars_term (snd r) []);

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

add_vars_term :: forall a b. Term a b -> [b] -> [b];
add_vars_term (Var x) xs = x : xs;
add_vars_term (Fun uu ts) xs = Arith.foldr add_vars_term ts xs;

vars_term_list :: forall a b. Term a b -> [b];
vars_term_list t = add_vars_term t [];

vars_term ::
  forall a b.
    (Arith.Ceq b, Arith.Ccompare b,
      Arith.Set_impl b) => Term a b -> Arith.Set b;
vars_term t = Arith.set (vars_term_list t);

vars_rule ::
  forall a b.
    (Arith.Ceq b, Arith.Ccompare b,
      Arith.Set_impl b) => (Term a b, Term a b) -> Arith.Set b;
vars_rule r = Arith.sup_set (vars_term (fst r)) (vars_term (snd r));

vars_trs ::
  forall a b.
    (Compare.Compare a, Eq a, Arith.Finite_UNIV b, Arith.Cenum b, Arith.Ceq b,
      Arith.Cproper_interval b, Compare.Compare b, Eq b,
      Arith.Set_impl b) => Arith.Set (Term a b, Term a b) -> Arith.Set b;
vars_trs r = Complete_Lattices.sup_set (Arith.image vars_rule r);

lvars :: [(Arith.Nat, Linear_poly)] -> Arith.Set Arith.Nat;
lvars t = Arith.set (map lhs t);

constraint_to_qdelta_constraint :: Constraint -> [Ns_constraint QDelta.QDelta];
constraint_to_qdelta_constraint (LT l r) =
  [LEQ_ns l (QDelta.QDelta r (Rat.uminus_rat Rat.one_rat))];
constraint_to_qdelta_constraint (GT l r) =
  [GEQ_ns l (QDelta.QDelta r Rat.one_rat)];
constraint_to_qdelta_constraint (LEQ l r) =
  [LEQ_ns l (QDelta.QDelta r Rat.zero_rat)];
constraint_to_qdelta_constraint (GEQ l r) =
  [GEQ_ns l (QDelta.QDelta r Rat.zero_rat)];
constraint_to_qdelta_constraint (EQ l r) =
  [LEQ_ns l (QDelta.QDelta r Rat.zero_rat),
    GEQ_ns l (QDelta.QDelta r Rat.zero_rat)];

i_constraint_to_qdelta_constraint ::
  forall a. (a, Constraint) -> [(a, Ns_constraint QDelta.QDelta)];
i_constraint_to_qdelta_constraint (i, c) =
  map (\ a -> (i, a)) (constraint_to_qdelta_constraint c);

to_ns :: forall a. [(a, Constraint)] -> [(a, Ns_constraint QDelta.QDelta)];
to_ns l = concatMap i_constraint_to_qdelta_constraint l;

funas_term ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a,
      Arith.Set_impl a) => Term a b -> Arith.Set (a, Arith.Nat);
funas_term (Var uu) = Arith.bot_set;
funas_term (Fun f ts) =
  Arith.sup_set (Arith.insert (f, Arith.size_list ts) Arith.bot_set)
    (Arith.foldr (Arith.sup_set . funas_term) ts Arith.bot_set);

funas_rule ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a,
      Arith.Set_impl a) => (Term a b, Term a b) -> Arith.Set (a, Arith.Nat);
funas_rule r = Arith.sup_set (funas_term (fst r)) (funas_term (snd r));

funas_trs ::
  forall a b.
    (Arith.Finite_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Compare.Compare a, Eq a, Arith.Set_impl a, Compare.Compare b,
      Eq b) => Arith.Set (Term a b, Term a b) -> Arith.Set (a, Arith.Nat);
funas_trs r = Complete_Lattices.sup_set (Arith.image funas_rule r);

decompose ::
  forall a b c. (Eq a) => Term a b -> Term a c -> Maybe [(Term a b, Term a c)];
decompose s t =
  (case (s, t) of {
    (Var _, _) -> Nothing;
    (Fun _ _, Var _) -> Nothing;
    (Fun f ss, Fun g ts) ->
      (if f == g then Option_Monad.zip_option ss ts else Nothing);
  });

match_term_list_code ::
  forall a b c.
    (Eq a, Arith.Ccompare b, Eq b,
      Eq c) => [(Term a b, Term a c)] ->
                 Mapping.Mapping b (Term a c) ->
                   Maybe (Mapping.Mapping b (Term a c));
match_term_list_code [] sigma = Just sigma;
match_term_list_code ((Var x, t) : p) sigma =
  (if Arith.is_none (Mapping.lookup sigma x) || Mapping.lookup sigma x == Just t
    then match_term_list_code p (Mapping.update x t sigma) else Nothing);
match_term_list_code ((Fun f ss, Fun g ts) : p) sigma =
  (case decompose (Fun f ss) (Fun g ts) of {
    Nothing -> Nothing;
    Just us -> match_term_list_code (us ++ p) sigma;
  });
match_term_list_code ((Fun f ss, Var x) : p) sigma = Nothing;

match_list ::
  forall a b c.
    (Arith.Ccompare a, Eq a, Mapping.Mapping_impl a, Eq b,
      Eq c) => (a -> Term b c) ->
                 [(Term b a, Term b c)] -> Maybe (a -> Term b c);
match_list d p =
  Arith.map_option (Abstract_Matching.subst_of_map d . Mapping.lookup)
    (match_term_list_code p Mapping.empty);

match ::
  forall a b.
    (Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => Term a b -> Term a b -> Maybe (b -> Term a b);
match t l = match_list Var [(l, t)];

b_i_l :: forall a b. State a b -> Mapping.Mapping Arith.Nat (a, b);
b_i_l (State x1 x2 x3 x4 x5 x6) = x2;

indexl :: forall a b. State a b -> Arith.Nat -> a;
indexl s = (fst . Arith.the) . Mapping.lookup (b_i_l s);

b_i_u :: forall a b. State a b -> Mapping.Mapping Arith.Nat (a, b);
b_i_u (State x1 x2 x3 x4 x5 x6) = x3;

indexu :: forall a b. State a b -> Arith.Nat -> a;
indexu s = (fst . Arith.the) . Mapping.lookup (b_i_u s);

eval_term :: forall a b c. (a -> [b] -> b) -> Term a c -> (c -> b) -> b;
eval_term i (Var x) alpha = alpha x;
eval_term i (Fun f ss) alpha = i f (map (\ s -> eval_term i s alpha) ss);

args :: forall a b. Term a b -> [Term a b];
args (Var x1) = [];
args (Fun x21 x22) = x22;

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

initial :: forall a b c d e. Lts_ext a b c d e -> Arith.Set d;
initial (Lts_ext initial transition_rules assertion more) = initial;

untrans_var :: forall a. Trans_var a -> a;
untrans_var (Pre x) = x;
untrans_var (Post x) = x;
untrans_var (Intermediate x) = x;

boundsl :: forall a b. State a b -> Arith.Nat -> Maybe b;
boundsl s = Arith.map_option snd . Mapping.lookup (b_i_l s);

boundsu :: forall a b. State a b -> Arith.Nat -> Maybe b;
boundsu s = Arith.map_option snd . Mapping.lookup (b_i_u s);

ordered_keys ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Eq a, Quasi_Order.Linorder a,
      Arith.Set_impl a, Arith.Ceq b, Arith.Ccompare b,
      Arith.Set_impl b) => Finite_Map.Fmap a b -> [a];
ordered_keys m = Arith.sorted_list_of_set (FSet.fset (Finite_Map.fmdom m));

vars_list :: Linear_poly -> [Arith.Nat];
vars_list lp = ordered_keys (linear_poly_map lp);

valuate ::
  forall a.
    (Simplex_Algebra.Rational_vector a) => Linear_poly -> (Arith.Nat -> a) -> a;
valuate lp val =
  let {
    lpm = linear_poly_map lp;
  } in Groups_List.sum_list
         (map (\ x ->
                Simplex_Algebra.scaleRat (Arith.the (Finite_Map.fmlookup lpm x))
                  (val x))
           (vars_list lp));

delta_0_val ::
  Ns_constraint QDelta.QDelta -> (Arith.Nat -> QDelta.QDelta) -> Rat.Rat;
delta_0_val (LEQ_ns lll rrr) vl = QDelta.delta_0 (valuate lll vl) rrr;
delta_0_val (GEQ_ns lll rrr) vl = QDelta.delta_0 rrr (valuate lll vl);

delta_0_val_min ::
  [Ns_constraint QDelta.QDelta] -> (Arith.Nat -> QDelta.QDelta) -> Rat.Rat;
delta_0_val_min [] vl = Rat.one_rat;
delta_0_val_min (h : t) vl =
  Quasi_Order.min (delta_0_val_min t vl) (delta_0_val h vl);

map2fun ::
  forall a. (Arith.Zero a) => Mapping.Mapping Arith.Nat a -> Arith.Nat -> a;
map2fun v = (\ x -> (case Mapping.lookup v x of {
                      Nothing -> Arith.zero;
                      Just y -> y;
                    }));

from_ns ::
  Mapping.Mapping Arith.Nat QDelta.QDelta ->
    [Ns_constraint QDelta.QDelta] -> Mapping.Mapping Arith.Nat Rat.Rat;
from_ns vl cs =
  let {
    delta = delta_0_val_min cs (map2fun vl);
  } in Mapping.tabulate (Arith.remdups (concatMap vars_list (map poly cs)))
         (\ var -> QDelta.val (map2fun vl var) delta);

uBI_upd ::
  forall a b.
    (Quasi_Order.Linorder b) => Direction a b ->
                                  (Mapping.Mapping Arith.Nat (a, b) ->
                                    Mapping.Mapping Arith.Nat (a, b)) ->
                                    State a b -> State a b;
uBI_upd (Direction x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) = x8;

update_B_I ::
  forall a b c d e.
    (Arith.Ccompare a,
      Eq a) => ((Mapping.Mapping a (b, c) -> Mapping.Mapping a (b, c)) ->
                 d -> e) ->
                 b -> a -> c -> d -> e;
update_B_I field_update i x c s = field_update (Mapping.update x (i, c)) s;

lt :: forall a b. (Quasi_Order.Linorder b) => Direction a b -> b -> b -> Bool;
lt (Direction x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) = x1;

ub :: forall a b.
        (Quasi_Order.Linorder b) => Direction a b ->
                                      State a b -> Arith.Nat -> Maybe b;
ub (Direction x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) = x5;

li :: forall a b.
        (Quasi_Order.Linorder b) => Direction a b ->
                                      State a b -> Arith.Nat -> a;
li (Direction x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) = x6;

lb :: forall a b.
        (Quasi_Order.Linorder b) => Direction a b ->
                                      State a b -> Arith.Nat -> Maybe b;
lb (Direction x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) = x4;

v_update :: forall a b. Mapping.Mapping Arith.Nat a -> State b a -> State b a;
v_update v (State t bil biu v_old u uc) = State t bil biu v u uc;

v :: forall a b. State a b -> Mapping.Mapping Arith.Nat b;
v (State x1 x2 x3 x4 x5 x6) = x4;

t :: forall a b. State a b -> [(Arith.Nat, Linear_poly)];
t (State x1 x2 x3 x4 x5 x6) = x1;

get_var_coeff :: Finite_Map.Fmap Arith.Nat Rat.Rat -> Arith.Nat -> Rat.Rat;
get_var_coeff lp v = (case Finite_Map.fmlookup lp v of {
                       Nothing -> Rat.zero_rat;
                       Just c -> c;
                     });

coeff :: Linear_poly -> Arith.Nat -> Rat.Rat;
coeff lp = get_var_coeff (linear_poly_map lp);

rhs_eq_val ::
  forall a.
    (Arith.Minus a, Arith.Plus a, Arith.Zero a,
      Simplex_Algebra.ScaleRat a) => Mapping.Mapping Arith.Nat a ->
                                       Arith.Nat ->
 a -> (Arith.Nat, Linear_poly) -> a;
rhs_eq_val v x_i c e =
  let {
    x_j = lhs e;
    a_i_j = coeff (rhs e) x_i;
  } in Arith.plus (map2fun v x_j)
         (Simplex_Algebra.scaleRat a_i_j (Arith.minusa c (map2fun v x_i)));

update_code ::
  forall a b.
    (Simplex_Algebra.Lrv a) => Arith.Nat -> a -> State b a -> State b a;
update_code x c s =
  v_update
    (Mapping.update x c
      (Arith.foldl
        (\ va e -> Mapping.update (lhs e) (rhs_eq_val (v s) x c e) va) (v s)
        (t s)))
    s;

set_unsat :: forall a b. (Eq a) => [a] -> State a b -> State a b;
set_unsat i (State t bil biu v u uc) =
  State t bil biu v True (Just (Arith.remdups i));

assert_bound_codea ::
  forall a b.
    (Eq a, Eq b,
      Simplex_Algebra.Lrv b) => Direction a b ->
                                  a -> Arith.Nat -> b -> State a b -> State a b;
assert_bound_codea dir i x c s =
  (if geub (lt dir) c (ub dir s x) then s
    else let {
           sa = update_B_I (uBI_upd dir) i x c s;
         } in (if ltlb (lt dir) c (lb dir s x) then set_unsat [i, li dir s x] sa
                else (if not (Arith.member x (lvars (t sa))) &&
                           lt dir c (map2fun (v s) x)
                       then update_code x c sa else sa)));

b_i_u_update ::
  forall a b.
    (Mapping.Mapping Arith.Nat (a, b) -> Mapping.Mapping Arith.Nat (a, b)) ->
      State a b -> State a b;
b_i_u_update up (State t bil biu v u uc) = State t bil (up biu) v u uc;

positive :: forall a b. (Quasi_Order.Linorder b) => Direction a b;
positive =
  Direction Quasi_Order.less b_i_l b_i_u boundsl boundsu indexl indexu
    b_i_u_update Leq Geq Rat.less_eq_rat;

b_i_l_update ::
  forall a b.
    (Mapping.Mapping Arith.Nat (a, b) -> Mapping.Mapping Arith.Nat (a, b)) ->
      State a b -> State a b;
b_i_l_update up (State t bil biu v u uc) = State t (up bil) biu v u uc;

negative :: forall a b. (Quasi_Order.Linorder b) => Direction a b;
negative =
  Direction (\ x y -> Quasi_Order.less y x) b_i_u b_i_l boundsu boundsl indexu
    indexl b_i_l_update Geq Leq (\ x y -> Rat.less_eq_rat y x);

assert_bound_code ::
  forall a b.
    (Eq a, Eq b,
      Simplex_Algebra.Lrv b) => (a, Atom b) -> State a b -> State a b;
assert_bound_code (i, Leq x c) s = assert_bound_codea positive i x c s;
assert_bound_code (i, Geq x c) s = assert_bound_codea negative i x c s;

u :: forall a b. State a b -> Bool;
u (State x1 x2 x3 x4 x5 x6) = x5;

assert_bound_loop_code ::
  forall a b.
    (Eq a, Eq b,
      Simplex_Algebra.Lrv b) => [(a, Atom b)] -> State a b -> State a b;
assert_bound_loop_code ats s =
  Arith.foldl (\ sa a -> (if u sa then sa else assert_bound_code a sa)) s ats;

init_state ::
  forall a b. (Arith.Zero b) => [(Arith.Nat, Linear_poly)] -> State a b;
init_state t =
  State t
    (Mapping.mapping_empty (Phantom_Type.of_phantom Mapping.mapping_impl_nat))
    (Mapping.mapping_empty (Phantom_Type.of_phantom Mapping.mapping_impl_nat))
    (Mapping.tabulate
      (Arith.remdups (map lhs t ++ concatMap (vars_list . rhs) t))
      (\ _ -> Arith.zero))
    False Nothing;

le_ubound :: forall a. (Eq a, Quasi_Order.Linorder a) => a -> Maybe a -> Bool;
le_ubound c b = leub Quasi_Order.less c b;

ge_lbound :: forall a. (Eq a, Quasi_Order.Linorder a) => a -> Maybe a -> Bool;
ge_lbound c b = gelb Quasi_Order.less c b;

in_bounds ::
  forall a b.
    (Eq b,
      Quasi_Order.Linorder b) => a -> (a -> b) ->
(a -> Maybe b, a -> Maybe b) -> Bool;
in_bounds x v (lb, ub) = ge_lbound (v x) (lb x) && le_ubound (v x) (ub x);

min_lvar_not_in_bounds ::
  forall a b.
    (Arith.Zero b, Eq b,
      Quasi_Order.Linorder b) => State a b -> Maybe Arith.Nat;
min_lvar_not_in_bounds s =
  Simplex_Auxiliary.min_satisfying
    (\ x -> not (in_bounds x (map2fun (v s)) (boundsl s, boundsu s)))
    (map lhs (t s));

scale ::
  Rat.Rat ->
    Finite_Map.Fmap Arith.Nat Rat.Rat -> Finite_Map.Fmap Arith.Nat Rat.Rat;
scale r lp =
  (if Rat.equal_rat r Rat.zero_rat then Finite_Map.fmempty
    else Finite_Map.fmmap (Rat.times_rat r) lp);

scaleRat_linear_poly :: Rat.Rat -> Linear_poly -> Linear_poly;
scaleRat_linear_poly r p = LinearPoly (scale r (linear_poly_map p));

uminus_linear_poly :: Linear_poly -> Linear_poly;
uminus_linear_poly lp = scaleRat_linear_poly (Rat.uminus_rat Rat.one_rat) lp;

set_var_coeff ::
  Arith.Nat ->
    Rat.Rat ->
      Finite_Map.Fmap Arith.Nat Rat.Rat -> Finite_Map.Fmap Arith.Nat Rat.Rat;
set_var_coeff v c lp =
  (if Rat.equal_rat c Rat.zero_rat then Finite_Map.fmdrop v lp
    else Finite_Map.fmupd v c lp);

add_monom ::
  Rat.Rat ->
    Arith.Nat ->
      Finite_Map.Fmap Arith.Nat Rat.Rat -> Finite_Map.Fmap Arith.Nat Rat.Rat;
add_monom c v lp = set_var_coeff v (Rat.plus_rat c (get_var_coeff lp v)) lp;

add ::
  Finite_Map.Fmap Arith.Nat Rat.Rat ->
    Finite_Map.Fmap Arith.Nat Rat.Rat -> Finite_Map.Fmap Arith.Nat Rat.Rat;
add lp1 lp2 =
  Arith.foldl (\ lp v -> add_monom (get_var_coeff lp1 v) v lp) lp2
    (ordered_keys lp1);

plus_linear_poly :: Linear_poly -> Linear_poly -> Linear_poly;
plus_linear_poly p1 p2 =
  LinearPoly (add (linear_poly_map p1) (linear_poly_map p2));

minus_linear_poly :: Linear_poly -> Linear_poly -> Linear_poly;
minus_linear_poly lp1 lp2 = plus_linear_poly lp1 (uminus_linear_poly lp2);

var :: Arith.Nat -> Linear_poly;
var x = LinearPoly (set_var_coeff x Rat.one_rat Finite_Map.fmempty);

subst_var :: Arith.Nat -> Linear_poly -> Linear_poly -> Linear_poly;
subst_var v lpa lp =
  minus_linear_poly
    (plus_linear_poly lp (scaleRat_linear_poly (coeff lp v) lpa))
    (scaleRat_linear_poly (coeff lp v) (var v));

subst_var_eq_code ::
  Arith.Nat ->
    Linear_poly -> (Arith.Nat, Linear_poly) -> (Arith.Nat, Linear_poly);
subst_var_eq_code v lp eq = (lhs eq, subst_var v lp (rhs eq));

eq_idx_for_lvar_aux ::
  [(Arith.Nat, Linear_poly)] -> Arith.Nat -> Arith.Nat -> Arith.Nat;
eq_idx_for_lvar_aux [] x i = i;
eq_idx_for_lvar_aux (eq : t) x i =
  (if Arith.equal_nat (lhs eq) x then i
    else eq_idx_for_lvar_aux t x (Arith.plus_nat i Arith.one_nat));

eq_idx_for_lvar :: [(Arith.Nat, Linear_poly)] -> Arith.Nat -> Arith.Nat;
eq_idx_for_lvar t x = eq_idx_for_lvar_aux t x Arith.zero_nat;

eq_for_lvar_code ::
  [(Arith.Nat, Linear_poly)] -> Arith.Nat -> (Arith.Nat, Linear_poly);
eq_for_lvar_code t v = Arith.nth t (eq_idx_for_lvar t v);

pivot_eq :: (Arith.Nat, Linear_poly) -> Arith.Nat -> (Arith.Nat, Linear_poly);
pivot_eq e y =
  let {
    cy = coeff (rhs e) y;
  } in (y, plus_linear_poly
             (scaleRat_linear_poly
               (Rat.divide_rat (Rat.uminus_rat Rat.one_rat) cy)
               (minus_linear_poly (rhs e) (scaleRat_linear_poly cy (var y))))
             (scaleRat_linear_poly (Rat.divide_rat Rat.one_rat cy)
               (var (lhs e))));

pivot_tableau_code ::
  Arith.Nat ->
    Arith.Nat -> [(Arith.Nat, Linear_poly)] -> [(Arith.Nat, Linear_poly)];
pivot_tableau_code x_i x_j t =
  let {
    eq = eq_for_lvar_code t x_i;
    eqa = pivot_eq eq x_j;
  } in map (\ e ->
             (if Arith.equal_nat (lhs e) (lhs eq) then eqa
               else subst_var_eq_code x_j (rhs eqa) e))
         t;

t_update :: forall a b. [(Arith.Nat, Linear_poly)] -> State a b -> State a b;
t_update t (State t_old bil biu v u uc) = State t bil biu v u uc;

pivot_code ::
  forall a b.
    (Simplex_Algebra.Lrv b) => Arith.Nat -> Arith.Nat -> State a b -> State a b;
pivot_code x_i x_j s = t_update (pivot_tableau_code x_i x_j (t s)) s;

pivot_and_update_code ::
  forall a b.
    (Simplex_Algebra.Lrv a) => Arith.Nat ->
                                 Arith.Nat -> a -> State b a -> State b a;
pivot_and_update_code x_i x_j c s = update_code x_i c (pivot_code x_i x_j s);

ui :: forall a b.
        (Quasi_Order.Linorder b) => Direction a b ->
                                      State a b -> Arith.Nat -> a;
ui (Direction x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) = x7;

unsat_indices ::
  forall a b.
    (Eq a,
      Quasi_Order.Linorder b) => Direction a b ->
                                   State a b ->
                                     [Arith.Nat] ->
                                       (Arith.Nat, Linear_poly) -> [a];
unsat_indices dir s vs eq =
  let {
    r = rhs eq;
    lia = li dir s;
    uia = ui dir s;
  } in Arith.remdups
         (lia (lhs eq) :
           map (\ x ->
                 (if Rat.less_rat (coeff r x) Rat.zero_rat then lia x
                   else uia x))
             vs);

min_rvar_incdec_eq ::
  forall a b.
    (Eq a,
      Simplex_Algebra.Lrv b) => Direction a b ->
                                  State a b ->
                                    (Arith.Nat, Linear_poly) ->
                                      Sum_Type.Sum [a] Arith.Nat;
min_rvar_incdec_eq dir s eq =
  let {
    rvars = vars_list (rhs eq);
  } in (case Simplex_Auxiliary.min_satisfying
               (\ x ->
                 Rat.less_rat Rat.zero_rat (coeff (rhs eq) x) &&
                   ltub (lt dir) (map2fun (v s) x) (ub dir s x) ||
                   Rat.less_rat (coeff (rhs eq) x) Rat.zero_rat &&
                     gtlb (lt dir) (map2fun (v s) x) (lb dir s x))
               rvars
         of {
         Nothing -> Sum_Type.Inl (unsat_indices dir s rvars eq);
         Just a -> Sum_Type.Inr a;
       });

check_codea ::
  forall a b.
    (Eq a,
      Simplex_Algebra.Lrv b) => Direction a b ->
                                  Arith.Nat -> State a b -> State a b;
check_codea dir x_i s =
  let {
    l_i = Arith.the (lb dir s x_i);
  } in (case min_rvar_incdec_eq dir s (eq_for_lvar_code (t s) x_i) of {
         Sum_Type.Inl i -> set_unsat i s;
         Sum_Type.Inr x_j -> pivot_and_update_code x_i x_j l_i s;
       });

lt_lbound :: forall a. (Quasi_Order.Linorder a) => a -> Maybe a -> Bool;
lt_lbound c b = ltlb Quasi_Order.less c b;

check_code ::
  forall a b. (Eq a, Eq b, Simplex_Algebra.Lrv b) => State a b -> State a b;
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
    (Eq a, Eq b,
      Simplex_Algebra.Lrv b) => [(Arith.Nat, Linear_poly)] ->
                                  [(a, Atom b)] -> State a b;
assert_all_state_code t ats =
  check_code (assert_bound_loop_code ats (init_state t));

u_c :: forall a b. State a b -> Maybe [a];
u_c (State x1 x2 x3 x4 x5 x6) = x6;

assert_all_code ::
  forall a b.
    (Eq a, Eq b,
      Simplex_Algebra.Lrv b) => [(Arith.Nat, Linear_poly)] ->
                                  [(a, Atom b)] ->
                                    Sum_Type.Sum [a]
                                      (Mapping.Mapping Arith.Nat b);
assert_all_code t asa =
  let {
    s = assert_all_state_code t asa;
  } in (if u s then Sum_Type.Inl (Arith.the (u_c s)) else Sum_Type.Inr (v s));

max_var :: Linear_poly -> Arith.Nat;
max_var lp =
  let {
    vl = vars_list lp;
  } in (if null vl then Arith.zero_nat
         else Arith.foldl Quasi_Order.max (Arith.hda vl) (Arith.tla vl));

normalize_ns_constraint ::
  forall a. (Simplex_Algebra.Lrv a) => Ns_constraint a -> Ns_constraint a;
normalize_ns_constraint (LEQ_ns l r) =
  let {
    v = max_var l;
    c = coeff l v;
  } in (if Rat.equal_rat c Rat.zero_rat then LEQ_ns l r
         else let {
                ic = Rat.inverse_rat c;
              } in (if Rat.less_rat c Rat.zero_rat
                     then GEQ_ns (scaleRat_linear_poly ic l)
                            (Simplex_Algebra.scaleRat ic r)
                     else LEQ_ns (scaleRat_linear_poly ic l)
                            (Simplex_Algebra.scaleRat ic r)));
normalize_ns_constraint (GEQ_ns l r) =
  let {
    v = max_var l;
    c = coeff l v;
  } in (if Rat.equal_rat c Rat.zero_rat then GEQ_ns l r
         else let {
                ic = Rat.inverse_rat c;
              } in (if Rat.less_rat c Rat.zero_rat
                     then LEQ_ns (scaleRat_linear_poly ic l)
                            (Simplex_Algebra.scaleRat ic r)
                     else GEQ_ns (scaleRat_linear_poly ic l)
                            (Simplex_Algebra.scaleRat ic r)));

pivot_tableau_eq ::
  [(Arith.Nat, Linear_poly)] ->
    (Arith.Nat, Linear_poly) ->
      [(Arith.Nat, Linear_poly)] ->
        Arith.Nat ->
          ([(Arith.Nat, Linear_poly)],
            ((Arith.Nat, Linear_poly), [(Arith.Nat, Linear_poly)]));
pivot_tableau_eq t1 eq t2 x = let {
                                eqa = pivot_eq eq x;
                                m = map (subst_var_eq_code x (rhs eqa));
                              } in (m t1, (eqa, m t2));

preprocess_opt ::
  forall a.
    (Simplex_Algebra.Lrv a) => Arith.Set Arith.Nat ->
                                 [(Arith.Nat, Linear_poly)] ->
                                   [(Arith.Nat, Linear_poly)] ->
                                     ([(Arith.Nat, Linear_poly)],
                                       Mapping.Mapping Arith.Nat a ->
 Mapping.Mapping Arith.Nat a);
preprocess_opt x t1 [] = (t1, id);
preprocess_opt xa t1 ((x, p) : t2) =
  (if not (Arith.member x xa)
    then (case preprocess_opt xa t1 t2 of {
           (t, tv) ->
             (t, (\ v -> Mapping.update x (valuate p (map2fun v)) v) . tv);
         })
    else (case Arith.find (\ xb -> not (Arith.member xb xa)) (vars_list p) of {
           Nothing -> preprocess_opt xa ((x, p) : t1) t2;
           Just y ->
             (case pivot_tableau_eq t1 (x, p) t2 y of {
               (tt1, ((z, q), tt2)) ->
                 (case preprocess_opt xa tt1 tt2 of {
                   (t, tv) ->
                     (t, (\ v -> Mapping.update z (valuate q (map2fun v)) v) .
                           tv);
                 });
             });
         }));

atom_var :: forall a. Atom a -> Arith.Nat;
atom_var (Leq var a) = var;
atom_var (Geq var a) = var;

preprocess_part_2 ::
  forall a b c.
    (Arith.Ceq a, Arith.Ccompare a, Arith.Set_impl a, Arith.Ccompare b, Eq b,
      Simplex_Algebra.Lrv c) => [(a, Atom b)] ->
                                  [(Arith.Nat, Linear_poly)] ->
                                    ([(Arith.Nat, Linear_poly)],
                                      Mapping.Mapping Arith.Nat c ->
Mapping.Mapping Arith.Nat c);
preprocess_part_2 asa t =
  preprocess_opt (Arith.image atom_var (Arith.image snd (Arith.set asa))) [] t;

start_fresh_variable ::
  forall a. [(a, Ns_constraint QDelta.QDelta)] -> Arith.Nat;
start_fresh_variable [] = Arith.zero_nat;
start_fresh_variable ((i, h) : t) =
  Quasi_Order.max (Arith.plus_nat (max_var (poly h)) Arith.one_nat)
    (start_fresh_variable t);

unsatIndices :: forall a. Istate a -> [a];
unsatIndices (IState x1 x2 x3 x4 x5) = x5;

tableau :: forall a. Istate a -> [(Arith.Nat, Linear_poly)];
tableau (IState x1 x2 x3 x4 x5) = x2;

atoms :: forall a. Istate a -> [(a, Atom QDelta.QDelta)];
atoms (IState x1 x2 x3 x4 x5) = x3;

zero :: Finite_Map.Fmap Arith.Nat Rat.Rat;
zero = Finite_Map.fmempty;

zero_linear_poly :: Linear_poly;
zero_linear_poly = LinearPoly zero;

qdelta_constraint_to_atom ::
  Ns_constraint QDelta.QDelta -> Arith.Nat -> Atom QDelta.QDelta;
qdelta_constraint_to_atom (LEQ_ns l r) v = Leq v r;
qdelta_constraint_to_atom (GEQ_ns l r) v = Geq v r;

firstFreshVariable :: forall a. Istate a -> Arith.Nat;
firstFreshVariable (IState x1 x2 x3 x4 x5) = x1;

is_monom :: Linear_poly -> Bool;
is_monom l = Arith.equal_nat (Arith.size_list (vars_list l)) Arith.one_nat;

poly_Mapping :: forall a. Istate a -> Linear_poly -> Maybe Arith.Nat;
poly_Mapping (IState x1 x2 x3 x4 x5) = x4;

linear_poly_to_eq :: Linear_poly -> Arith.Nat -> (Arith.Nat, Linear_poly);
linear_poly_to_eq p v = (v, p);

zero_satisfies :: forall a. (Simplex_Algebra.Lrv a) => Ns_constraint a -> Bool;
zero_satisfies (LEQ_ns l r) = Quasi_Order.less_eq Arith.zero r;
zero_satisfies (GEQ_ns l r) = Quasi_Order.less_eq r Arith.zero;

monom_var :: Linear_poly -> Arith.Nat;
monom_var l = max_var l;

monom_coeff :: Linear_poly -> Rat.Rat;
monom_coeff l = coeff l (monom_var l);

monom_to_atom :: Ns_constraint QDelta.QDelta -> Atom QDelta.QDelta;
monom_to_atom (LEQ_ns l r) =
  (if Rat.less_rat (monom_coeff l) Rat.zero_rat
    then Geq (monom_var l)
           (QDelta.scaleRat_QDelta (Rat.inverse_rat (monom_coeff l)) r)
    else Leq (monom_var l)
           (QDelta.scaleRat_QDelta (Rat.inverse_rat (monom_coeff l)) r));
monom_to_atom (GEQ_ns l r) =
  (if Rat.less_rat (monom_coeff l) Rat.zero_rat
    then Leq (monom_var l)
           (QDelta.scaleRat_QDelta (Rat.inverse_rat (monom_coeff l)) r)
    else Geq (monom_var l)
           (QDelta.scaleRat_QDelta (Rat.inverse_rat (monom_coeff l)) r));

preprocessa ::
  forall a. [(a, Ns_constraint QDelta.QDelta)] -> Arith.Nat -> Istate a;
preprocessa [] v = IState v [] [] (\ _ -> Nothing) [];
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
                         IState (Arith.plus_nat va Arith.one_nat)
                           (linear_poly_to_eq p va : ta)
                           ((i, qdelta_constraint_to_atom h va) : a)
                           (Fun.fun_upd m p (Just va)) u;
                       Just vaa ->
                         IState va ta ((i, qdelta_constraint_to_atom h vaa) : a)
                           m u;
                     })));

preprocess_part_1 ::
  forall a.
    [(a, Ns_constraint QDelta.QDelta)] ->
      ([(Arith.Nat, Linear_poly)], ([(a, Atom QDelta.QDelta)], [a]));
preprocess_part_1 l = let {
                        start = start_fresh_variable l;
                        is = preprocessa l start;
                      } in (tableau is, (atoms is, unsatIndices is));

preprocess ::
  forall a.
    (Arith.Ceq a, Arith.Ccompare a,
      Arith.Set_impl a) => [(a, Ns_constraint QDelta.QDelta)] ->
                             ([(Arith.Nat, Linear_poly)],
                               ([(a, Atom QDelta.QDelta)],
                                 (Mapping.Mapping Arith.Nat QDelta.QDelta ->
                                    Mapping.Mapping Arith.Nat QDelta.QDelta,
                                   [a])));
preprocess l =
  (case preprocess_part_1 (map (Arith.map_prod id normalize_ns_constraint) l) of
    {
    (t, (asa, ui)) -> (case preprocess_part_2 asa t of {
                        (ta, tv) -> (ta, (asa, (tv, ui)));
                      });
  });

solve_exec_ns_code ::
  forall a.
    (Arith.Ceq a, Arith.Ccompare a, Eq a,
      Arith.Set_impl a) => [(a, Ns_constraint QDelta.QDelta)] ->
                             Sum_Type.Sum [a]
                               (Mapping.Mapping Arith.Nat QDelta.QDelta);
solve_exec_ns_code s =
  (case preprocess s of {
    (t, (asa, (trans_v, []))) -> (case assert_all_code t asa of {
                                   Sum_Type.Inl a -> Sum_Type.Inl a;
                                   Sum_Type.Inr v -> Sum_Type.Inr (trans_v v);
                                 });
    (_, (_, (_, i : _))) -> Sum_Type.Inl [i];
  });

solve_exec_code ::
  forall a.
    (Arith.Ceq a, Arith.Ccompare a, Eq a,
      Arith.Set_impl a) => [(a, Constraint)] ->
                             Sum_Type.Sum [a]
                               (Mapping.Mapping Arith.Nat Rat.Rat);
solve_exec_code cs =
  let {
    csa = to_ns cs;
  } in (case solve_exec_ns_code csa of {
         Sum_Type.Inl a -> Sum_Type.Inl a;
         Sum_Type.Inr v -> Sum_Type.Inr (from_ns v (map snd csa));
       });

simplex_index ::
  forall a.
    (Arith.Ceq a, Arith.Ccompare a, Eq a,
      Arith.Set_impl a) => [(a, Constraint)] ->
                             Sum_Type.Sum [a]
                               (Mapping.Mapping Arith.Nat Rat.Rat);
simplex_index = solve_exec_code;

simplex ::
  [Constraint] -> Sum_Type.Sum [Arith.Nat] (Mapping.Mapping Arith.Nat Rat.Rat);
simplex cs =
  simplex_index (zip (Arith.upt Arith.zero_nat (Arith.size_list cs)) cs);

eval_subst ::
  forall a b c d. (a -> [b] -> b) -> (c -> Term a d) -> (d -> b) -> c -> b;
eval_subst i theta alpha = (\ x -> eval_term i (theta x) alpha);

subst_of :: forall a b. (Eq a) => [(a, Term b a)] -> a -> Term b a;
subst_of ss =
  Arith.foldr (\ (x, t) sigma -> eval_subst Fun sigma (subst x t)) ss Var;

contains_var_term :: forall a b. (Eq a) => a -> Term b a -> Bool;
contains_var_term x (Var y) = x == y;
contains_var_term x (Fun uu ts) = any (contains_var_term x) ts;

subst_list ::
  forall a b.
    (a -> Term b a) -> [(Term b a, Term b a)] -> [(Term b a, Term b a)];
subst_list sigma ys =
  map (\ p -> (eval_term Fun (fst p) sigma, eval_term Fun (snd p) sigma)) ys;

unify ::
  forall a b.
    (Eq a,
      Eq b) => [(Term a b, Term a b)] ->
                 [(b, Term a b)] -> Maybe [(b, Term a b)];
unify [] bs = Just bs;
unify ((Fun f ss, Fun g ts) : e) bs =
  (case decompose (Fun f ss) (Fun g ts) of {
    Nothing -> Nothing;
    Just us -> unify (us ++ e) bs;
  });
unify ((Var x, t) : e) bs =
  (if equal_term t (Var x) then unify e bs
    else (if contains_var_term x t then Nothing
           else unify (subst_list (subst x t) e) ((x, t) : bs)));
unify ((Fun v va, Var x) : e) bs =
  (if contains_var_term x (Fun v va) then Nothing
    else unify (subst_list (subst x (Fun v va)) e) ((x, Fun v va) : bs));

mgu ::
  forall a b. (Eq a, Eq b) => Term a b -> Term a b -> Maybe (b -> Term a b);
mgu s t = (case unify [(s, t)] [] of {
            Nothing -> Nothing;
            Just res -> Just (subst_of res);
          });

form_not :: forall a. Formula a -> Formula a;
form_not (Atom a) = NegAtom a;
form_not (NegAtom a) = Atom a;
form_not (Conjunction phi_s) = Disjunction (map form_not phi_s);
form_not (Disjunction phi_s) = Conjunction (map form_not phi_s);

get_Atom :: forall a. Formula a -> a;
get_Atom (Atom a) = a;
get_Atom (NegAtom a) = a;

matches ::
  forall a b c.
    (Eq a, Eq b, Arith.Ccompare c, Eq c,
      Mapping.Mapping_impl c) => Term a b -> Term a c -> Bool;
matches t p = (case match_list (\ _ -> t) [(p, t)] of {
                Nothing -> False;
                Just _ -> True;
              });

rrewrite ::
  forall a b.
    (Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => [(Term a b, Term a b)] ->
                                   Term a b -> [Term a b];
rrewrite r s =
  concatMap (\ (l, ra) -> (case match s l of {
                            Nothing -> [];
                            Just sigma -> [eval_term Fun ra sigma];
                          }))
    r;

rewrite ::
  forall a b.
    (Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => [(Term a b, Term a b)] ->
                                   Term a b -> [Term a b];
rewrite r s =
  rrewrite r s ++
    (case s of {
      Var _ -> [];
      Fun f ss ->
        concatMap
          (\ (i, si) ->
            map (\ ti -> Fun f (Arith.list_update ss i ti)) (rewrite r si))
          (zip (Arith.upt Arith.zero_nat (Arith.size_list ss)) ss);
    });

assertion ::
  forall a b c d e. Lts_ext a b c d e -> d -> Formula (Term a (b, c));
assertion (Lts_ext initial transition_rules assertion more) = assertion;

transition_of ::
  forall a b c d e.
    (Arith.Ccompare e, Eq e, Mapping.Mapping_impl e,
      Shows_Literal.Showl e) => Lts_impl a b c d e ->
                                  e -> Transition_rule a b c d;
transition_of pi =
  Map_Of.map_of_total
    (\ a ->
      ((Shows_Literal.showsl_lit "access to non-existing transition " .
         Shows_Literal.showsl a) .
        Shows_Literal.showsl_lit "\navailable transitions:\n") .
        Shows_Literal.showsl_list (map fst (transitions_impl pi)))
    (transitions_impl pi);

the_Var :: forall a b. Term a b -> b;
the_Var (Var x1) = x1;

vars_term_ms :: forall a b. (Eq b) => Term a b -> Multiset.Multiset b;
vars_term_ms (Var x) = Multiset.add_mset x Multiset.zero_multiset;
vars_term_ms (Fun f ts) =
  Multiset.sum_mset (Multiset.mset (map vars_term_ms ts));

in_poss :: forall a b. [Arith.Nat] -> Term a b -> Bool;
in_poss [] uu = True;
in_poss (i : p) (Fun f ts) =
  Arith.less_nat i (Arith.size_list ts) && in_poss p (Arith.nth ts i);
in_poss (i : p) (Var uv) = False;

subt_at :: forall a b. Term a b -> [Arith.Nat] -> Term a b;
subt_at s [] = s;
subt_at (Fun f ss) (i : p) = subt_at (Arith.nth ss i) p;

add_funs_term :: forall a b. Term a b -> [a] -> [a];
add_funs_term (Var uu) fs = fs;
add_funs_term (Fun f ts) fs = f : Arith.foldr add_funs_term ts fs;

add_funs_rule :: forall a b. (Term a b, Term a b) -> [a] -> [a];
add_funs_rule r fs = add_funs_term (fst r) (add_funs_term (snd r) fs);

funs_trs_list :: forall a b. [(Term a b, Term a b)] -> [a];
funs_trs_list trs = Arith.foldr add_funs_rule trs [];

instance_rule ::
  forall a b c.
    (Eq a, Eq b, Arith.Ccompare c, Eq c,
      Mapping.Mapping_impl c) => (Term a b, Term a b) ->
                                   (Term a c, Term a c) -> Bool;
instance_rule lr st =
  not (Arith.is_none
        (match_list (\ _ -> fst lr) [(fst st, fst lr), (snd st, snd lr)]));

map_term :: forall a b c d. (a -> b) -> (c -> d) -> Term a c -> Term b d;
map_term f1 f2 (Var x1) = Var (f2 x1);
map_term f1 f2 (Fun x21 x22) = Fun (f1 x21) (map (map_term f1 f2) x22);

map_funs_rule ::
  forall a b c. (a -> b) -> (Term a c, Term a c) -> (Term b c, Term b c);
map_funs_rule fg lr =
  (map_term fg (\ x -> x) (fst lr), map_term fg (\ x -> x) (snd lr));

add_vars_rule :: forall a b. (Term a b, Term a b) -> [b] -> [b];
add_vars_rule r xs = add_vars_term (fst r) (add_vars_term (snd r) xs);

vars_trs_list :: forall a b. [(Term a b, Term a b)] -> [b];
vars_trs_list trs = Arith.foldr add_vars_rule trs [];

is_root_step ::
  forall a b.
    (Compare.Compare a, Eq a, Arith.Ccompare b, Compare.Compare b, Eq b,
      Mapping.Mapping_impl b) => Arith.Set (Term a b, Term a b) ->
                                   Term a b -> Term a b -> Bool;
is_root_step r s t =
  Arith.bex r (\ (l, ra) -> (case match_list Var [(l, s), (ra, t)] of {
                              Nothing -> False;
                              Just _ -> True;
                            }));

is_rstep ::
  forall a b.
    (Compare.Compare a, Eq a, Arith.Ccompare b, Compare.Compare b, Eq b,
      Mapping.Mapping_impl b) => Arith.Set (Term a b, Term a b) ->
                                   Term a b -> Term a b -> Bool;
is_rstep r (Fun f ts) (Fun g ss) =
  f == g &&
    Arith.equal_nat (Arith.size_list ts) (Arith.size_list ss) &&
      any (\ i ->
            ss == Arith.list_update ts i (Arith.nth ss i) &&
              is_rstep r (Arith.nth ts i) (Arith.nth ss i))
        (Arith.upt Arith.zero_nat (Arith.size_list ss)) ||
    is_root_step r (Fun f ts) (Fun g ss);
is_rstep r (Var v) t = is_root_step r (Var v) t;
is_rstep r s (Var v) = is_root_step r s (Var v);

term_map ::
  forall a b.
    (Compare.Compare_order a) => [Term a b] -> (a, Arith.Nat) -> [Term a b];
term_map ts =
  Option_Util.fun_of_map
    (RBT.lookup (RBT_Map_Set_Extension.elem_list_to_rm (Arith.the . root) ts))
    [];

nodes_lts_impl :: forall a b c d e. (Eq d) => Lts_impl a b c d e -> [d];
nodes_lts_impl pi =
  Arith.remdups
    (map (source . snd) (transitions_impl pi) ++
      map (target . snd) (transitions_impl pi));

rec_term ::
  forall a b c. (a -> b) -> (c -> [(Term c a, b)] -> b) -> Term c a -> b;
rec_term f1 f2 (Var x1) = f1 x1;
rec_term f1 f2 (Fun x21 x22) =
  f2 x21 (map (\ term -> (term, rec_term f1 f2 term)) x22);

mk_subst ::
  forall a b c. (Eq a) => (a -> Term b c) -> [(a, Term b c)] -> a -> Term b c;
mk_subst d xts = (\ x -> (case Map.map_of xts x of {
                           Nothing -> d x;
                           Just t -> t;
                         }));

mk_subst_domain ::
  forall a b. (Eq a, Eq b) => [(a, Term b a)] -> [(a, Term b a)];
mk_subst_domain sigma =
  let {
    tau = mk_subst Var sigma;
  } in filter (\ (x, t) -> not (equal_term (Var x) t))
         (map (\ x -> (x, tau x)) (Arith.remdups (map fst sigma)));

subst_eq ::
  forall a b.
    (Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a, Compare.Compare a, Eq a,
      Arith.Set_impl a, Compare.Compare b,
      Eq b) => [(a, Term b a)] -> [(a, Term b a)] -> Bool;
subst_eq sigma tau = let {
                       sigmaa = mk_subst_domain sigma;
                       taua = mk_subst_domain tau;
                     } in Arith.set_eq (Arith.set sigmaa) (Arith.set taua);

hole_pos :: forall a b. Actxt a b -> [Arith.Nat];
hole_pos Hole = [];
hole_pos (More f ss d ts) = Arith.size_list ss : hole_pos d;

var_poss :: forall a b. Term a b -> Arith.Set [Arith.Nat];
var_poss (Var x) =
  Arith.insert []
    (Arith.set_empty (Phantom_Type.of_phantom Arith.set_impl_list));
var_poss (Fun f ts) =
  Complete_Lattices.sup_set
    (Arith.image (\ i -> Arith.image (\ a -> i : a) (var_poss (Arith.nth ts i)))
      (Set_Interval.atLeastLessThan Arith.zero_nat (Arith.size_list ts)));

add_funas_term :: forall a b. Term a b -> [(a, Arith.Nat)] -> [(a, Arith.Nat)];
add_funas_term (Var uu) fs = fs;
add_funas_term (Fun f ts) fs =
  (f, Arith.size_list ts) : Arith.foldr add_funas_term ts fs;

add_funas_rule ::
  forall a b. (Term a b, Term a b) -> [(a, Arith.Nat)] -> [(a, Arith.Nat)];
add_funas_rule r fs = add_funas_term (fst r) (add_funas_term (snd r) fs);

funas_trs_list :: forall a b. [(Term a b, Term a b)] -> [(a, Arith.Nat)];
funas_trs_list trs = Arith.foldr add_funas_rule trs [];

funs_rule_list :: forall a b. (Term a b, Term a b) -> [a];
funs_rule_list r = add_funs_rule r [];

vars_rule_list :: forall a b. (Term a b, Term a b) -> [b];
vars_rule_list r = add_vars_rule r [];

supteq_list :: forall a b. Term a b -> [Term a b];
supteq_list (Var x) = [Var x];
supteq_list (Fun f ts) = Fun f ts : concatMap supteq_list ts;

is_NF_main ::
  forall a b.
    (Compare.Compare_order a, Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => Bool ->
                                   Bool ->
                                     ((a, Arith.Nat) -> [Term a b]) ->
                                       Term a b -> Bool;
is_NF_main var_cond r_empty m =
  (if var_cond then (\ _ -> False)
    else (if r_empty then (\ _ -> True)
           else (\ t ->
                  all (\ u ->
                        (if not (is_Var u)
                          then all (\ l -> not (matches u l))
                                 (m (Arith.the (root u)))
                          else True))
                    (supteq_list t))));

is_NF_trs ::
  forall a b c.
    (Compare.Compare_order a, Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => [(Term a b, c)] -> Term a b -> Bool;
is_NF_trs r =
  is_NF_main (any (\ ra -> is_Var (fst ra)) r) (null r) (term_map (map fst r));

mgu_var_disjoint_generic ::
  forall a b c d.
    (Eq b,
      Eq d) => (a -> b) ->
                 (c -> b) ->
                   Term d a -> Term d c -> Maybe (a -> Term d b, c -> Term d b);
mgu_var_disjoint_generic vu wu s t =
  (case mgu (map_term (\ x -> x) vu s) (map_term (\ x -> x) wu t) of {
    Nothing -> Nothing;
    Just gamma -> Just (gamma . vu, gamma . wu);
  });

mgu_vd ::
  forall a b.
    (Fresh.Infinite a, Eq a,
      Eq b) => Renaming2.Renaming2 a ->
                 Term b a -> Term b a -> Maybe (a -> Term b a, a -> Term b a);
mgu_vd r =
  mgu_var_disjoint_generic (Renaming2.rename_1 r) (Renaming2.rename_2 r);

rep_afs ::
  forall a. Afs a -> ((a, Arith.Nat) -> Af_entry, Arith.Set (a, Arith.Nat));
rep_afs (Abs_afs x) = x;

afs :: forall a. Afs a -> (a, Arith.Nat) -> Af_entry;
afs xa = fst (rep_afs xa);

poss_list :: forall a b. Term a b -> [[Arith.Nat]];
poss_list (Var x) = [[]];
poss_list (Fun f ss) =
  [] : concatMap (\ (i, a) -> map (\ aa -> i : aa) a)
         (zip (Arith.upt Arith.zero_nat (Arith.size_list ss))
           (map poss_list ss));

supt_impl :: forall a b. (Eq a, Eq b) => Term a b -> Term a b -> Bool;
supt_impl (Var x) t = False;
supt_impl (Fun f ss) t = Arith.membera ss t || any (\ s -> supt_impl s t) ss;

supt_list :: forall a b. Term a b -> [Term a b];
supt_list (Var x) = [];
supt_list (Fun f ts) = concatMap supteq_list ts;

r_sym :: forall a b. Ta_rule a b -> (b, Arith.Nat);
r_sym (TA_rule f qs q) = (f, Arith.size_list qs);

funas_rule_list :: forall a b. (Term a b, Term a b) -> [(a, Arith.Nat)];
funas_rule_list r = add_funas_rule r [];

showsl_rulea ::
  forall a b.
    (a -> String -> String) ->
      (b -> String -> String) ->
        String -> (Term a b, Term a b) -> String -> String;
showsl_rulea fun var arr (l, r) =
  (showsl_term fun var l . Shows_Literal.showsl_literal arr) .
    showsl_term fun var r;

showsl_rulesa ::
  forall a b.
    (a -> String -> String) ->
      (b -> String -> String) ->
        String -> [(Term a b, Term a b)] -> String -> String;
showsl_rulesa fun var arr trs =
  Shows_Literal.showsl_list_gen (showsl_rulea fun var arr) "" "" "\n" "" trs .
    Shows_Literal.showsl_literal "\n";

showsl_trsa ::
  forall a b.
    (a -> String -> String) ->
      (b -> String -> String) ->
        String -> String -> [(Term a b, Term a b)] -> String -> String;
showsl_trsa fun var name arr r =
  (Shows_Literal.showsl_literal name . Shows_Literal.showsl_literal "\n\n") .
    showsl_rulesa fun var arr r;

showsl_trs ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => [(Term a b, Term a b)] -> String -> String;
showsl_trs =
  showsl_trsa Shows_Literal.showsl Shows_Literal.showsl "rewrite system:"
    " -> ";

match_lista ::
  forall a b. (Eq a) => [(Gctxt a b, Term a b)] -> Maybe [(Gctxt a b, b)];
match_lista [] = Just [];
match_lista ((GCHole, t) : ps) = match_lista ps;
match_lista ((GCFun f ss, Fun g ts) : ps) =
  Arith.bind (Option_Monad.guard (f == g))
    (\ _ ->
      Arith.bind (Option_Monad.zip_option ss ts)
        (\ psa -> match_lista (psa ++ ps)));
match_lista ((GCFun f ss, Var x) : ps) =
  Arith.bind (match_lista ps) (\ psa -> Just ((GCFun f ss, x) : psa));

merge_lists ::
  forall a b. (Eq a) => [Gctxt a b] -> [Gctxt a b] -> Maybe [Gctxt a b];
merge_lists [] [] = Just [];
merge_lists (GCHole : cs) (d : ds) =
  Arith.bind (merge_lists cs ds) (\ es -> Just (d : es));
merge_lists (c : cs) (GCHole : ds) =
  Arith.bind (merge_lists cs ds) (\ es -> Just (c : es));
merge_lists (GCFun f ss : cs) (GCFun g ts : ds) =
  Arith.bind (Option_Monad.guard (f == g))
    (\ _ ->
      Arith.bind (merge_lists ss ts)
        (\ us ->
          Arith.bind (merge_lists cs ds) (\ es -> Just (GCFun f us : es))));
merge_lists [] (d : ds) = Nothing;
merge_lists (c : cs) [] = Nothing;

merge :: forall a b. (Eq a) => Gctxt a b -> Gctxt a b -> Maybe (Gctxt a b);
merge c d =
  Arith.bind (merge_lists [c] [d]) (\ es -> Just (Arith.nth es Arith.zero_nat));

merge_var ::
  forall a b.
    (Eq a,
      Eq b) => a -> Gctxt b a ->
                      [(Gctxt b a, a)] ->
                        Maybe ((Gctxt b a, a), [(Gctxt b a, a)]);
merge_var x c [] = Just ((c, x), []);
merge_var x c ((d, y) : ps) =
  (if x == y then Arith.bind (merge c d) (\ e -> merge_var x e ps)
    else Arith.bind (merge_var x c ps) (\ (b, psa) -> Just (b, (d, y) : psa)));

merge_all ::
  forall a b. (Eq a, Eq b) => [(Gctxt a b, b)] -> Maybe [(Gctxt a b, b)];
merge_all [] = Just [];
merge_all ((c, x) : ps) =
  Arith.bind (merge_var x c ps)
    (\ (cx, psa) -> Arith.bind (merge_all psa) (\ psb -> Just (cx : psb)));

matchb ::
  forall a b. (Eq a, Eq b) => (Gctxt a b, Term a b) -> Maybe [(Gctxt a b, b)];
matchb (c, t) = Arith.bind (match_lista [(c, t)]) merge_all;

matcha :: forall a b. (Eq a, Eq b) => Gctxt a b -> Term a b -> Bool;
matcha c t = not (Arith.is_none (matchb (c, t)));

succ_transitions ::
  forall a b c d e.
    (Eq d) => Lts_impl a b c d e -> d -> [Transition_rule a b c d];
succ_transitions (Lts_Impl i ts lc) l =
  concatMap (\ (_, tau) -> (if source tau == l then [tau] else [])) ts;

check_supt ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => Term a b ->
                                  Term a b ->
                                    Sum_Type.Sum (String -> String) ();
check_supt s t =
  Check_Monad.check (supt_impl s t)
    ((showsl_terma t .
       Shows_Literal.showsl_literal " is not a proper subterm of ") .
      showsl_terma s);

r_lhs_states :: forall a b. Ta_rule a b -> [a];
r_lhs_states (TA_rule x1 x2 x3) = x2;

r_rhs :: forall a b. Ta_rule a b -> a;
r_rhs (TA_rule x1 x2 x3) = x3;

ta_rules :: forall a b c. Ta_ext a b c -> Arith.Set (Ta_rule a b);
ta_rules (Ta_ext ta_final ta_rules ta_eps more) = ta_rules;

ta_eps :: forall a b c. Ta_ext a b c -> Arith.Set (a, a);
ta_eps (Ta_ext ta_final ta_rules ta_eps more) = ta_eps;

ta_res ::
  forall a b.
    (Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a, Eq a, Arith.Set_impl a,
      Arith.Ccompare b, Eq b) => Ta_ext a b () -> Term b a -> Arith.Set a;
ta_res ta (Var q) =
  let {
    a = Arith.insert q Arith.bot_set;
  } in Arith.sup_set a (Abstract_Rewriting_Impl.compute_trancl a (ta_eps ta));
ta_res ta (Fun f ts) =
  let {
    qs = map (ta_res ta) ts;
    g = (f, Arith.size_list ts);
    a = Arith.image r_rhs
          (Arith.filtera
            (\ r ->
              r_sym r == g &&
                all (\ qq -> Arith.member (snd qq) (fst qq))
                  (zip qs (r_lhs_states r)))
            (ta_rules ta));
  } in Arith.sup_set a (Abstract_Rewriting_Impl.compute_trancl a (ta_eps ta));

eq_rule_mod_vars ::
  forall a b.
    (Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => (Term a b, Term a b) ->
                                   (Term a b, Term a b) -> Bool;
eq_rule_mod_vars lr st = instance_rule lr st && instance_rule st lr;

is_NF_terms ::
  forall a b.
    (Compare.Compare_order a, Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => [Term a b] -> Term a b -> Bool;
is_NF_terms q = is_NF_main (any is_Var q) (null q) (term_map q);

showsl_rule ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => (Term a b, Term a b) -> String -> String;
showsl_rule = showsl_rulea Shows_Literal.showsl Shows_Literal.showsl " -> ";

diff_by_label ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a) => [(a, b)] -> Arith.Set a -> [(a, b)];
diff_by_label pairs l = filter (\ v -> not (Arith.member (fst v) l)) pairs;

linear_term_impl ::
  forall a b.
    (Arith.Ceq a,
      Arith.Ccompare a) => Arith.Set a -> Term b a -> Maybe (Arith.Set a);
linear_term_impl xs (Var x) =
  (if Arith.member x xs then Nothing else Just (Arith.insert x xs));
linear_term_impl xs (Fun uu []) = Just xs;
linear_term_impl xs (Fun f (t : ts)) =
  (case linear_term_impl xs t of {
    Nothing -> Nothing;
    Just ys -> linear_term_impl ys (Fun f ts);
  });

linear_term ::
  forall a b.
    (Arith.Ceq b, Arith.Ccompare b, Arith.Set_impl b) => Term a b -> Bool;
linear_term t = not (Arith.is_none (linear_term_impl Arith.bot_set t));

ta_final :: forall a b c. Ta_ext a b c -> Arith.Set a;
ta_final (Ta_ext ta_final ta_rules ta_eps more) = ta_final;

r_states ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a,
      Arith.Set_impl a) => Ta_rule a b -> Arith.Set a;
r_states =
  (\ ta_rule ->
    Arith.insert (r_rhs ta_rule) (Arith.set (r_lhs_states ta_rule)));

ta_states ::
  forall a b.
    (Arith.Finite_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Eq a, Arith.Set_impl a, Arith.Ccompare b,
      Eq b) => Ta_ext a b () -> Arith.Set a;
ta_states ta =
  Arith.sup_set
    (Arith.sup_set
      (Complete_Lattices.sup_set (Arith.image r_states (ta_rules ta)))
      (Complete_Lattices.sup_set
        (Arith.image
          (\ (q, qa) -> Arith.insert q (Arith.insert qa Arith.bot_set))
          (ta_eps ta))))
    (ta_final ta);

ta_syms ::
  forall a b.
    (Arith.Ccompare a, Eq a, Arith.Ceq b, Arith.Ccompare b, Eq b,
      Arith.Set_impl b) => Ta_ext a b () -> Arith.Set (b, Arith.Nat);
ta_syms ta = Arith.image r_sym (ta_rules ta);

prod_ta ::
  forall a b c.
    (Arith.Finite_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Eq a, Arith.Set_impl a, Arith.Ceq b, Arith.Ccompare b, Eq b,
      Arith.Set_impl b, Arith.Finite_UNIV c, Arith.Cenum c, Arith.Ceq c,
      Arith.Cproper_interval c, Eq c,
      Arith.Set_impl c) => Ta_ext a b () ->
                             Ta_ext c b () ->
                               Arith.Set (a, c) -> Ta_ext (a, c) b ();
prod_ta tA1 tA2 f =
  Ta_ext f
    (Arith.image
      (\ (TA_rule fa qs1 q1, TA_rule _ qs2 q2) ->
        TA_rule fa (zip qs1 qs2) (q1, q2))
      (Complete_Lattices.sup_set
        (Arith.image
          (\ fa ->
            Arith.productc (Arith.filtera (\ r -> r_sym r == fa) (ta_rules tA1))
              (Arith.filtera (\ r -> r_sym r == fa) (ta_rules tA2)))
          (ta_syms tA1))))
    (Arith.sup_set
      (Arith.image (\ (a, b) -> (case a of {
                                  (q, qa) -> (\ p -> ((q, p), (qa, p)));
                                })
                                  b)
        (Arith.productc (ta_eps tA1) (ta_states tA2)))
      (Arith.image (\ (p, (q, qa)) -> ((p, q), (p, qa)))
        (Arith.productc (ta_states tA1) (ta_eps tA2))))
    ();

productive_relation ::
  forall a b.
    (Arith.Finite_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Eq a, Arith.Set_impl a, Arith.Ccompare b,
      Eq b) => Ta_ext a b () -> Arith.Set (a, a);
productive_relation ta =
  Arith.sup_set (Arith.image (\ (a, b) -> (b, a)) (ta_eps ta))
    (Complete_Lattices.sup_set
      (Arith.image
        (\ r -> Arith.image (\ a -> (r_rhs r, a)) (Arith.set (r_lhs_states r)))
        (ta_rules ta)));

ta_productive ::
  forall a b.
    (Arith.Finite_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Eq a, Arith.Set_impl a, Arith.Ccompare b,
      Eq b) => Ta_ext a b () -> Arith.Set a;
ta_productive ta =
  let {
    a = ta_final ta;
  } in Arith.sup_set a
         (Abstract_Rewriting_Impl.compute_trancl a (productive_relation ta));

reduced_TA ::
  forall a b c.
    (Arith.Ccompare a, Eq a, Arith.Ceq b, Arith.Ccompare b, Eq b,
      Arith.Set_impl b) => a -> Ta_ext b a c -> Arith.Set b -> Ta_ext b a ();
reduced_TA f ta q =
  Ta_ext Arith.bot_set
    (Arith.sup_set
      (Arith.image
        (\ (TA_rule fa qs a) ->
          TA_rule fa (filter (\ qa -> not (Arith.member qa q)) qs) a)
        (Arith.filtera (\ r -> not (Arith.member (r_rhs r) q)) (ta_rules ta)))
      (Arith.image (\ p -> TA_rule f [] (snd p))
        (Arith.filtera
          (\ p -> Arith.member (fst p) q && not (Arith.member (snd p) q))
          (ta_eps ta))))
    (Arith.filtera
      (\ p -> not (Arith.member (fst p) q) && not (Arith.member (snd p) q))
      (ta_eps ta))
    ();

new_reach ::
  forall a b c.
    (Arith.Ceq a, Arith.Ccompare a, Eq a, Arith.Set_impl a, Arith.Ccompare b,
      Eq b) => Ta_ext a b c -> Arith.Set a;
new_reach ta =
  Arith.image r_rhs
    (Arith.filtera (\ r -> null (r_lhs_states r)) (ta_rules ta));

ta_reachable ::
  forall a b.
    (Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a, Eq a, Arith.Set_impl a,
      Arith.Ccompare b, HOL.Default b, Eq b) => Ta_ext a b () -> Arith.Set a;
ta_reachable ta =
  let {
    q = new_reach ta;
  } in (if Arith.less_eq_set q Arith.bot_set then Arith.bot_set
         else Arith.sup_set q (ta_reachable (reduced_TA HOL.defaulta ta q)));

ta_restrict ::
  forall a b c.
    (Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a, Eq a, Arith.Set_impl a,
      Arith.Ccompare b, Eq b) => Ta_ext a b c -> Arith.Set a -> Ta_ext a b ();
ta_restrict ta q =
  Ta_ext (Arith.inf_set (ta_final ta) q)
    (Arith.filtera (\ r -> Arith.less_eq_set (r_states r) q) (ta_rules ta))
    (Arith.inf_set (ta_eps ta) (Arith.productc q q)) ();

trim_ta ::
  forall a b.
    (Arith.Finite_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Eq a, Arith.Set_impl a, Arith.Ccompare b, HOL.Default b,
      Eq b) => Ta_ext a b () -> Ta_ext a b ();
trim_ta ta =
  ta_restrict (ta_restrict ta (ta_reachable ta))
    (ta_productive (ta_restrict ta (ta_reachable ta)));

check_varcond_no_Var_lhs ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => [(Term a b, Term a b)] ->
                                  Sum_Type.Sum (String -> String) ();
check_varcond_no_Var_lhs =
  (\ xs ->
    Error_Monad.catch_error
      (Error_Monad.forallM
        (\ rule ->
          Check_Monad.check (not (is_Var (fst rule)))
            ((Shows_Literal.showsl_literal "variable left-hand side in rule " .
               showsl_rule rule) .
              Shows_Literal.showsl_literal "\n"))
        xs)
      (\ x -> Sum_Type.Inl (snd x)));

check_varcond_subset ::
  forall a b.
    (Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => [(Term a b, Term a b)] ->
                                  Sum_Type.Sum (String -> String) ();
check_varcond_subset r =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ rule ->
        Error_Monad.catch_error
          (Check_Monad.check_subseteq (insert_vars_term (snd rule) [])
            (insert_vars_term (fst rule) []))
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
      Shows_Literal.Showl b) => [(Term a b, Term a b)] ->
                                  Sum_Type.Sum (String -> String) ();
check_wf_trs r =
  Error_Monad.catch_error
    (Error_Monad.bind (check_varcond_no_Var_lhs r)
      (\ _ -> check_varcond_subset r))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_literal "the TRS is not well-formed\n" . x));

defined_list :: forall a b. [(Term a b, Term a b)] -> [(a, Arith.Nat)];
defined_list r =
  concatMap (\ (l, _) -> (if not (is_Var l) then [Arith.the (root l)] else []))
    r;

showsl_rules ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => [(Term a b, Term a b)] -> String -> String;
showsl_rules = showsl_rulesa Shows_Literal.showsl Shows_Literal.showsl " -> ";

afs_sym :: forall a. Afs a -> (a, Arith.Nat) -> [(Filtered a, Arith.Nat)];
afs_sym af (f, n) = (case afs af (f, n) of {
                      Collapse _ -> [];
                      AFList is -> [(FPair f n, Arith.size_list is)];
                    });

afs_sig :: forall a. Afs a -> [(a, Arith.Nat)] -> [(Filtered a, Arith.Nat)];
afs_sig af = concatMap (afs_sym af);

af_sig :: forall a. Afs a -> [(a, Arith.Nat)] -> [(a, Arith.Nat)];
af_sig af = map (Arith.map_prod filtered_fun id) . afs_sig af;

rep_x_compare_order_x_x_f_afs_option_x_x_nat_x_compare_order_x_x_f_prod_set_af_entry_nat_x_compare_order_x_x_f_prod_fun_prod_option ::
  forall a.
    (Compare.Compare_order a) => X_compare_order_x_x_f_afs_option_x_x_nat_x_compare_order_x_x_f_prod_set_af_entry_nat_x_compare_order_x_x_f_prod_fun_prod_option
                                   a ->
                                   Maybe ((a, Arith.Nat) -> Af_entry,
   Arith.Set (a, Arith.Nat));
rep_x_compare_order_x_x_f_afs_option_x_x_nat_x_compare_order_x_x_f_prod_set_af_entry_nat_x_compare_order_x_x_f_prod_fun_prod_option
  (Abs_x_compare_order_x_x_f_afs_option_x_x_nat_x_compare_order_x_x_f_prod_set_af_entry_nat_x_compare_order_x_x_f_prod_fun_prod_option
    x)
  = x;

sel21 ::
  forall a.
    (Compare.Compare_order a) => X_compare_order_x_x_f_afs_option_x_x_nat_x_compare_order_x_x_f_prod_set_af_entry_nat_x_compare_order_x_x_f_prod_fun_prod_option
                                   a ->
                                   Afs a;
sel21 xa =
  Abs_afs
    (case rep_x_compare_order_x_x_f_afs_option_x_x_nat_x_compare_order_x_x_f_prod_set_af_entry_nat_x_compare_order_x_x_f_prod_fun_prod_option
            xa
      of {
      Nothing -> rep_afs (error "undefined");
      Just x2 -> x2;
    });

dis1 ::
  forall a.
    (Compare.Compare_order a) => X_compare_order_x_x_f_afs_option_x_x_nat_x_compare_order_x_x_f_prod_set_af_entry_nat_x_compare_order_x_x_f_prod_fun_prod_option
                                   a ->
                                   Bool;
dis1 xa =
  (case rep_x_compare_order_x_x_f_afs_option_x_x_nat_x_compare_order_x_x_f_prod_set_af_entry_nat_x_compare_order_x_x_f_prod_fun_prod_option
          xa
    of {
    Nothing -> True;
    Just _ -> False;
  });

rep_isom ::
  forall a.
    (Compare.Compare_order a) => X_compare_order_x_x_f_afs_option_x_x_nat_x_compare_order_x_x_f_prod_set_af_entry_nat_x_compare_order_x_x_f_prod_fun_prod_option
                                   a ->
                                   Maybe (Afs a);
rep_isom x = (if dis1 x then Nothing else Just (sel21 x));

default_af_entry :: Arith.Nat -> Af_entry;
default_af_entry n = AFList (Arith.upt Arith.zero_nat n);

wf_af_entry :: Arith.Nat -> Af_entry -> Bool;
wf_af_entry n (Collapse i) = Arith.less_nat i n;
wf_af_entry n (AFList is) = all (\ i -> Arith.less_nat i n) is;

afs_of_aux ::
  forall a.
    (Arith.Ceq a, Arith.Ccompare a, Compare.Compare_order a,
      Arith.Set_impl a) => [((a, Arith.Nat), Af_entry)] ->
                             X_compare_order_x_x_f_afs_option_x_x_nat_x_compare_order_x_x_f_prod_set_af_entry_nat_x_compare_order_x_x_f_prod_fun_prod_option
                               a;
afs_of_aux xa =
  Abs_x_compare_order_x_x_f_afs_option_x_x_nat_x_compare_order_x_x_f_prod_set_af_entry_nat_x_compare_order_x_x_f_prod_fun_prod_option
    (if all (\ ((_, n), e) -> wf_af_entry n e) xa
      then Just (Map_Choice.fun_of_map_fun (Map_Choice.ceta_map_of xa)
                   (\ fn -> default_af_entry (snd fn)),
                  Arith.set (map fst xa))
      else Nothing);

afs_of ::
  forall a.
    (Arith.Ceq a, Arith.Ccompare a, Compare.Compare_order a,
      Arith.Set_impl a) => [((a, Arith.Nat), Af_entry)] -> Maybe (Afs a);
afs_of x = rep_isom (afs_of_aux x);

has_type ::
  forall a b c. (Eq b) => (a -> ([b], b)) -> Term a (c, b) -> b -> Bool;
has_type type_of_fun (Var v) ty = snd v == ty;
has_type type_of_fun (Fun f es) ty =
  ty == snd (type_of_fun f) &&
    Arith.equal_nat (Arith.size_list es)
      (Arith.size_list (fst (type_of_fun f))) &&
      let {
        d = Arith.minus_nat (Arith.size_list es) Arith.one_nat;
      } in (if Arith.less_nat d (Arith.size_list es)
             then Arith.all_interval
                    (\ i ->
                      has_type type_of_fun (Arith.nth es i)
                        (Arith.nth (fst (type_of_fun f)) i))
                    Arith.zero_nat d
             else True);

is_bool ::
  forall a b c.
    (Arith.Ceq b, Arith.Ccompare b,
      Eq b) => (a -> ([b], b)) -> Arith.Set b -> Term a (c, b) -> Bool;
is_bool type_of_fun bool_types e =
  Arith.bex bool_types (has_type type_of_fun e);

formula :: forall a. (a -> Bool) -> Formula a -> Bool;
formula atom (Atom a) = atom a;
formula atom (NegAtom a) = atom a;
formula atom (Conjunction phi_s) = all (formula atom) phi_s;
formula atom (Disjunction phi_s) = all (formula atom) phi_s;

transition_rule ::
  forall a b c d.
    (Arith.Ceq b, Arith.Ccompare b,
      Eq b) => (a -> ([b], b)) ->
                 Arith.Set b -> Transition_rule a c b d -> Bool;
transition_rule type_of_fun bool_types (Transition l r phi) =
  formula (is_bool type_of_fun bool_types) phi;

check_lts_impl ::
  forall a b c d e.
    (Arith.Ceq b, Arith.Ccompare b,
      Eq b) => (a -> ([b], b)) ->
                 Arith.Set b ->
                   Lts_impl a c b d e -> Sum_Type.Sum (String -> String) ();
check_lts_impl type_of_fun bool_types pi =
  (case pi of {
    Lts_Impl _ ti lc ->
      Error_Monad.bind
        (Error_Monad.catch_error
          (Error_Monad.forallM
            (\ (_, t) ->
              Check_Monad.check (transition_rule type_of_fun bool_types t)
                (Shows_Literal.showsl_lit "ill-formed transition in LTS"))
            ti)
          (\ x -> Sum_Type.Inl (snd x)))
        (\ _ ->
          Error_Monad.catch_error
            (Error_Monad.forallM
              (\ (_, f) ->
                Check_Monad.check (formula (is_bool type_of_fun bool_types) f)
                  (Shows_Literal.showsl_lit
                    "ill-formed location condition in LTS"))
              lc)
            (\ x -> Sum_Type.Inl (snd x)));
  });

check_no_var ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => Term a b -> Sum_Type.Sum (String -> String) ();
check_no_var t =
  Check_Monad.check (not (is_Var t))
    (Shows_Literal.showsl_literal "variable found\n");

check_supteq ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => Term a b ->
                                  Term a b ->
                                    Sum_Type.Sum (String -> String) ();
check_supteq s t =
  Check_Monad.check (equal_term s t || supt_impl s t)
    ((showsl_terma t . Shows_Literal.showsl_literal " is not a subterm of ") .
      showsl_terma s);

funs_term_ms :: forall a b. (Eq a) => Term a b -> Multiset.Multiset a;
funs_term_ms (Var x) = Multiset.zero_multiset;
funs_term_ms (Fun f ts) =
  Multiset.plus_multiset (Multiset.add_mset f Multiset.zero_multiset)
    (Multiset.sum_mset (Multiset.mset (map funs_term_ms ts)));

subt_at_ctxt ::
  forall a b. Actxt a (Term a b) -> [Arith.Nat] -> Actxt a (Term a b);
subt_at_ctxt c [] = c;
subt_at_ctxt (More f bef c aft) (i : p) = subt_at_ctxt c p;

ta_empty ::
  forall a b.
    (Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a, Eq a, Arith.Set_impl a,
      Arith.Ccompare b, HOL.Default b, Eq b) => Ta_ext a b () -> Bool;
ta_empty ta =
  Arith.less_eq_set (Arith.inf_set (ta_reachable ta) (ta_final ta))
    Arith.bot_set;

ta_match ::
  forall a b c.
    (Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a, Eq a, Arith.Set_impl a,
      Arith.Ccompare b, Eq b, Arith.Ceq c,
      Arith.Ccompare c) => Ta_ext a b () ->
                             Arith.Set a ->
                               Term b c -> Arith.Set a -> Arith.Set [(c, a)];
ta_match ta qsig (Var x) q =
  Arith.image (\ qa -> [(x, qa)])
    (Arith.filtera (\ qa -> Arith.member qa qsig)
      (let {
         a = q;
       } in Arith.sup_set a
              (Abstract_Rewriting_Impl.compute_trancl a
                (Relation.converse (ta_eps ta)))));
ta_match ta qsig (Fun f ts) q =
  let {
    n = Arith.size_list ts;
    rls = Arith.filtera
            (\ rule ->
              r_sym rule == (f, n) &&
                Arith.bex
                  (let {
                     a = Arith.insert (r_rhs rule) Arith.bot_set;
                   } in Arith.sup_set a
                          (Abstract_Rewriting_Impl.compute_trancl a
                            (ta_eps ta)))
                  (\ qa -> Arith.member qa q))
            (ta_rules ta);
  } in Complete_Lattices.sup_set
         (Arith.image
           (\ (TA_rule _ qs _) ->
             Arith.image concat
               (Arith.listset
                 (map (\ (tsi, qsi) ->
                        ta_match ta qsig tsi (Arith.insert qsi Arith.bot_set))
                   (zip ts qs))))
           rls);

first_rewrite ::
  forall a b.
    (Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => [(Term a b, Term a b)] ->
                                   Term a b -> Maybe (Term a b);
first_rewrite r s = (case rewrite r s of {
                      [] -> Nothing;
                      t : _ -> Just t;
                    });

compute_rstep_NF ::
  forall a b.
    (Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => [(Term a b, Term a b)] ->
                                   Term a b -> Maybe (Term a b);
compute_rstep_NF r s = Abstract_Rewriting_Impl.compute_NF (first_rewrite r) s;

check_join_NF ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => [(Term a b, Term a b)] ->
                                  Term a b ->
                                    Term a b ->
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
      Check_Monad.check (equal_term sa ta)
        (((((((Shows_Literal.showsl_literal "the normal form " .
                showsl_terma sa) .
               Shows_Literal.showsl_literal " of ") .
              showsl_terma s) .
             Shows_Literal.showsl_literal " differs from\nthe normal form ") .
            showsl_terma ta) .
           Shows_Literal.showsl_literal " of ") .
          showsl_terma t);
  });

reverse_rules :: forall a b. [(Term a b, Term a b)] -> [(Term a b, Term a b)];
reverse_rules rs = map Arith.swap rs;

wf_rules_impl ::
  forall a b. (Eq b) => [(Term a b, Term a b)] -> [(Term a b, Term a b)];
wf_rules_impl r = filter wf_rule r;

apply_af_entry :: forall a b. a -> Af_entry -> [Term a b] -> Term a b;
apply_af_entry uu (Collapse i) ts = Arith.nth ts i;
apply_af_entry f (AFList is) ts = Fun f (map (Arith.nth ts) is);

afs_term :: forall a b. Afs a -> Term a b -> Term (Filtered a) b;
afs_term pi (Fun f ts) =
  let {
    l = Arith.size_list ts;
  } in apply_af_entry (FPair f l) (afs pi (f, l)) (map (afs_term pi) ts);
afs_term pi (Var x) = Var x;

afs_rule ::
  forall a b.
    Afs a -> (Term a b, Term a b) -> (Term (Filtered a) b, Term (Filtered a) b);
afs_rule pi lr = (afs_term pi (fst lr), afs_term pi (snd lr));

af_rule :: forall a b. Afs a -> (Term a b, Term a b) -> (Term a b, Term a b);
af_rule pi = (\ t -> map_funs_rule filtered_fun (afs_rule pi t));

af_term :: forall a b. Afs a -> Term a b -> Term a b;
af_term pi (Fun f ts) =
  apply_af_entry f (afs pi (f, Arith.size_list ts)) (map (af_term pi) ts);
af_term pi (Var x) = Var x;

in_vars_formula :: forall a b. (Eq a) => a -> Formula (Term b a) -> Bool;
in_vars_formula x (Atom a) = Arith.membera (vars_term_list a) x;
in_vars_formula x (NegAtom a) = Arith.membera (vars_term_list a) x;
in_vars_formula x (Conjunction phi_s) = any (in_vars_formula x) phi_s;
in_vars_formula x (Disjunction phi_s) = any (in_vars_formula x) phi_s;

trivial_checker :: forall a. (Eq a) => [Formula a] -> Bool;
trivial_checker lits = (case Arith.partition is_Atom lits of {
                         (asa, nas) -> let {
 pos = map get_Atom asa;
 neg = map get_Atom nas;
                                       } in any (Arith.membera neg) pos;
                       });

subst_compose_impl ::
  forall a b.
    (Eq a, Eq b) => [(a, Term b a)] -> [(a, Term b a)] -> [(a, Term b a)];
subst_compose_impl sigma tau =
  let {
    sigmaa = mk_subst_domain sigma;
    taua = mk_subst_domain tau;
    d_sigma = map fst sigmaa;
  } in map (\ (x, t) -> (x, eval_term Fun t (mk_subst Var taua))) sigmaa ++
         filter (\ (x, _) -> not (Arith.membera d_sigma x)) taua;

commutes_impl ::
  forall a b.
    (Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a, Compare.Compare a, Eq a,
      Arith.Set_impl a, Compare.Compare b,
      Eq b) => [(a, Term b a)] -> [(a, Term b a)] -> Bool;
commutes_impl sigma mu =
  subst_eq (subst_compose_impl sigma mu) (subst_compose_impl mu sigma);

fun_poss_list :: forall a b. Term a b -> [[Arith.Nat]];
fun_poss_list (Var x) = [];
fun_poss_list (Fun f ss) =
  [] : concatMap (\ (i, a) -> map (\ aa -> i : aa) a)
         (zip (Arith.upt Arith.zero_nat (Arith.size_list ss))
           (map fun_poss_list ss));

mk_subst_case ::
  forall a b.
    (Eq a,
      Eq b) => [a] -> (a -> Term b a) -> [(a, Term b a)] -> [(a, Term b a)];
mk_subst_case xs sigma tau =
  subst_compose_impl (map (\ x -> (x, sigma x)) xs) tau;

showsl_actxt ::
  forall a b.
    (a -> String -> String) ->
      (b -> String -> String) -> Actxt a b -> String -> String;
showsl_actxt fun arg Hole = Shows_Literal.showsl_lit "[]";
showsl_actxt fun arg (More f ss1 d ss2) =
  (((fun f . Shows_Literal.showsl_literal "(") .
     Shows_Literal.showsl_list_gen arg "" "" ", " ", " ss1) .
    showsl_actxt fun arg d) .
    Shows_Literal.showsl_list_gen arg ")" ", " ", " ")" ss2;

prc_nat ::
  forall a.
    ((a, Arith.Nat) -> Arith.Nat) ->
      (a, Arith.Nat) -> (a, Arith.Nat) -> (Bool, Bool);
prc_nat pr = (\ f g -> let {
                         pf = pr f;
                         pg = pr g;
                       } in (Arith.less_nat pg pf, Arith.less_eq_nat pg pf));

prl_nat :: forall a. ((a, Arith.Nat) -> Arith.Nat) -> (a, Arith.Nat) -> Bool;
prl_nat pr = (\ f -> Arith.equal_nat (pr f) Arith.zero_nat);

ta_matcha ::
  forall a b c.
    (Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a, Eq a, Arith.Set_impl a,
      Arith.Ccompare b, Eq b, Arith.Ceq c,
      Arith.Ccompare c) => Ta_ext a b () ->
                             Arith.Set a -> Term b c -> Arith.Set [(c, a)];
ta_matcha ta q t = ta_match ta q t q;

adapt_vars :: forall a b c. Term a b -> Term a c;
adapt_vars (Fun f ts) = Fun f (map adapt_vars ts);

ta_member ::
  forall a b c.
    (Arith.Ccompare a, Eq a, Arith.Cenum c, Arith.Ceq c, Arith.Ccompare c, Eq c,
      Arith.Set_impl c) => Term a b -> Ta_ext c a () -> Bool;
ta_member t ta =
  ground t &&
    not (Arith.less_eq_set
          (Arith.inf_set (ta_final ta) (ta_res ta (adapt_vars t)))
          Arith.bot_set);

add_funas_args_term ::
  forall a b. Term a b -> [(a, Arith.Nat)] -> [(a, Arith.Nat)];
add_funas_args_term t fs = Arith.foldr add_funas_term (args t) fs;

add_funas_args_rule ::
  forall a b. (Term a b, Term a b) -> [(a, Arith.Nat)] -> [(a, Arith.Nat)];
add_funas_args_rule r fs =
  add_funas_args_term (fst r) (add_funas_args_term (snd r) fs);

funas_args_trs_list :: forall a b. [(Term a b, Term a b)] -> [(a, Arith.Nat)];
funas_args_trs_list trs = Arith.foldr add_funas_args_rule trs [];

af_check ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => (String -> String) ->
                                  Afs a ->
                                    ((Term a b, Term a b) ->
                                      Sum_Type.Sum (String -> String) ()) ->
                                      (Term a b, Term a b) ->
Sum_Type.Sum (String -> String) ();
af_check r pi g lr =
  let {
    pl = af_term pi (fst lr);
    pr = af_term pi (snd lr);
  } in Error_Monad.catch_error (g (pl, pr))
         (\ x ->
           Sum_Type.Inl
             (((((((((((((((Shows_Literal.showsl_literal "could not orient " .
                             showsl_terma (fst lr)) .
                            Shows_Literal.showsl_literal " ") .
                           r) .
                          Shows_Literal.showsl_literal " ") .
                         showsl_terma (snd lr)) .
                        Shows_Literal.showsl_literal "\npi( ") .
                       showsl_terma (fst lr)) .
                      Shows_Literal.showsl_literal " ) = ") .
                     showsl_terma pl) .
                    Shows_Literal.showsl_literal "\npi( ") .
                   showsl_terma (snd lr)) .
                  Shows_Literal.showsl_literal " ) = ") .
                 showsl_terma pr) .
                Shows_Literal.showsl_literal "\n") .
               x));

af_rules ::
  forall a b. Afs a -> [(Term a b, Term a b)] -> [(Term a b, Term a b)];
af_rules pi r = map (af_rule pi) r;

afs_syms :: forall a. Afs a -> Arith.Set (a, Arith.Nat);
afs_syms xa = snd (rep_afs xa);

mono_af_entry :: Arith.Nat -> Af_entry -> Bool;
mono_af_entry n (Collapse i) = Arith.less_eq_nat n Arith.one_nat;
mono_af_entry n (AFList ids) =
  all (Arith.membera ids) (Arith.upt Arith.zero_nat n);

mono_afs :: forall a. (Arith.Ceq a, Arith.Ccompare a) => Afs a -> Bool;
mono_afs pi =
  Arith.ball (afs_syms pi) (\ (f, n) -> mono_af_entry n (afs pi (f, n)));

get_conjunctions :: forall a. Formula a -> [Formula a];
get_conjunctions (Conjunction phis) = concatMap get_conjunctions phis;
get_conjunctions (Atom v) = [Atom v];
get_conjunctions (NegAtom v) = [NegAtom v];
get_conjunctions (Disjunction v) = [Disjunction v];

get_disjunctions :: forall a. Formula a -> [Formula a];
get_disjunctions (Disjunction phis) = concatMap get_disjunctions phis;
get_disjunctions (Atom v) = [Atom v];
get_disjunctions (NegAtom v) = [NegAtom v];
get_disjunctions (Conjunction v) = [Conjunction v];

pos_gctxt ::
  forall a b.
    (Compare.Compare a, Eq a,
      Compare.Compare b) => Gctxt a b -> Arith.Set [Arith.Nat];
pos_gctxt GCHole =
  Arith.insert []
    (Arith.set_empty (Phantom_Type.of_phantom Arith.set_impl_list));
pos_gctxt (GCFun f cs) =
  Arith.sup_set
    (Arith.insert []
      (Arith.set_empty (Phantom_Type.of_phantom Arith.set_impl_list)))
    (Complete_Lattices.sup_set
      (Arith.image (\ (c, i) -> Arith.image (\ a -> i : a) (pos_gctxt c))
        (Arith.set (zip cs (Arith.upt Arith.zero_nat (Arith.size_list cs))))));

unifiable :: forall a b. (Eq a) => Gctxt a b -> Gctxt a b -> Bool;
unifiable s t = not (Arith.is_none (merge s t));

funs_term_list :: forall a b. Term a b -> [a];
funs_term_list t = add_funs_term t [];

coherent_rule ::
  forall a b.
    (Arith.Finite_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Eq a, Arith.Set_impl a, Arith.Ccompare b,
      Eq b) => Arith.Set (a, a) ->
                 Arith.Set (Ta_rule a b) ->
                   Ta_rule a b -> Arith.Set (a, Maybe a);
coherent_rule rel rules (TA_rule f qs q) =
  Arith.foldr
    (Arith.sup_set .
      (\ i ->
        let {
          qi = Arith.nth qs i;
          qi_s = Arith.image snd (Arith.filtera (\ qq -> fst qq == qi) rel);
          a = Complete_Lattices.sup_set
                (Arith.image
                  (\ qia ->
                    let {
                      qsa = Arith.list_update qs i qia;
                      rls = Arith.filtera
                              (\ (TA_rule g qsaa _) -> g == f && qsaa == qsa)
                              rules;
                    } in (if Arith.less_eq_set rls
                               (Arith.set_empty
                                 (Phantom_Type.of_phantom set_impl_ta_rule))
                           then Arith.insert Nothing Arith.bot_set
                           else Arith.image (Just . r_rhs) rls))
                  qi_s);
        } in Arith.image (\ aa -> (q, aa)) a))
    (Arith.upt Arith.zero_nat (Arith.size_list qs)) Arith.bot_set;

new_states ::
  forall a b.
    (Arith.Finite_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Eq a, Arith.Set_impl a, Arith.Ccompare b,
      Eq b) => Ta_ext a b () -> Arith.Set (a, a) -> Arith.Set (a, Maybe a);
new_states ta rel =
  let {
    rules = ta_rules ta;
  } in Complete_Lattices.sup_set (Arith.image (coherent_rule rel rules) rules);

check_wf_reltrs ::
  forall a b c d.
    (Shows_Literal.Showl a, Eq b, Shows_Literal.Showl b, Shows_Literal.Showl c,
      Eq d,
      Shows_Literal.Showl d) => ([(Term a b, Term a b)],
                                  [(Term c d, Term c d)]) ->
                                  Sum_Type.Sum (String -> String) ();
check_wf_reltrs (r, s) =
  Error_Monad.bind (check_wf_trs r)
    (\ _ -> (if null r then Sum_Type.Inr () else check_varcond_subset s));

reachable_terms ::
  forall a b.
    (Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => [(Term a b, Term a b)] ->
                                   Term a b -> Arith.Nat -> [Term a b];
reachable_terms r s n =
  (if Arith.equal_nat n Arith.zero_nat then [s]
    else let {
           ts = reachable_terms r s (Arith.minus_nat n Arith.one_nat);
         } in Arith.remdups (ts ++ concatMap (rewrite r) ts));

vars :: Linear_poly -> Arith.Set Arith.Nat;
vars lp = FSet.fset (Finite_Map.fmdom (linear_poly_map lp));

afs_check ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => (String -> String) ->
                                  Afs a ->
                                    ((Term (Filtered a) b,
                                       Term (Filtered a) b) ->
                                      Sum_Type.Sum (String -> String) ()) ->
                                      (Term a b, Term a b) ->
Sum_Type.Sum (String -> String) ();
afs_check r pi g lr =
  let {
    pl = afs_term pi (fst lr);
    pr = afs_term pi (snd lr);
  } in Error_Monad.catch_error (g (pl, pr))
         (\ x ->
           Sum_Type.Inl
             (((((((((((((((Shows_Literal.showsl_literal "could not orient " .
                             showsl_terma (fst lr)) .
                            Shows_Literal.showsl_literal " ") .
                           r) .
                          Shows_Literal.showsl_literal " ") .
                         showsl_terma (snd lr)) .
                        Shows_Literal.showsl_literal "\npi( ") .
                       showsl_terma (fst lr)) .
                      Shows_Literal.showsl_literal " ) = ") .
                     showsl_terma pl) .
                    Shows_Literal.showsl_literal "\npi( ") .
                   showsl_terma (snd lr)) .
                  Shows_Literal.showsl_literal " ) = ") .
                 showsl_terma pr) .
                Shows_Literal.showsl_literal "\n") .
               x));

afs_to_af ::
  forall a.
    (Compare.Compare_order a) => Afs a -> (a, Arith.Nat) -> Arith.Set Arith.Nat;
afs_to_af pi fn =
  (case afs pi fn of {
    Collapse j ->
      Arith.insert j
        (Arith.set_empty (Phantom_Type.of_phantom Arith.set_impl_nat));
    AFList a -> Arith.set a;
  });

range_vars_impl :: forall a b. (Eq a, Eq b) => [(a, Term b a)] -> [a];
range_vars_impl sigma = let {
                          a = mk_subst_domain sigma;
                        } in concatMap (vars_term_list . snd) a;

vars_subst_impl :: forall a b. (Eq a, Eq b) => [(a, Term b a)] -> [a];
vars_subst_impl sigma =
  let {
    sigmaa = mk_subst_domain sigma;
  } in map fst sigmaa ++ concatMap (vars_term_list . snd) sigmaa;

funas_term_list :: forall a b. Term a b -> [(a, Arith.Nat)];
funas_term_list (Var uu) = [];
funas_term_list (Fun f ts) =
  (f, Arith.size_list ts) : concatMap funas_term_list ts;

ta_rhs_states ::
  forall a b.
    (Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a, Eq a, Arith.Set_impl a,
      Arith.Ccompare b, Eq b) => Ta_ext a b () -> Arith.Set a;
ta_rhs_states ta =
  let {
    a = Arith.image r_rhs (ta_rules ta);
  } in Arith.sup_set a (Abstract_Rewriting_Impl.compute_trancl a (ta_eps ta));

initial_rel ::
  forall a b c.
    (Arith.Card_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Eq a, Arith.Set_impl a, Arith.Ccompare b, Compare.Compare b, Eq b,
      Arith.Ceq c, Arith.Ccompare c, Compare.Compare c, Eq c,
      Arith.Set_impl c) => Ta_ext a b () ->
                             Arith.Set (Term b c, Term b c) ->
                               Arith.Set (a, Arith.Set a);
initial_rel ta r =
  let {
    rhs = ta_rhs_states ta;
    match = ta_matcha ta rhs;
    analyze_rule =
      (\ (l, ra) ->
        let {
          _ = vars_term l;
        } in Complete_Lattices.sup_set
               (Arith.image
                 (\ sigma ->
                   let {
                     qr = ta_res ta
                            (map_term (\ x -> x) (Util.fun_of sigma) ra);
                   } in Arith.image (\ q -> (q, qr))
                          (ta_res ta
                            (map_term (\ x -> x) (Util.fun_of sigma) l)))
                 (match l)));
  } in Complete_Lattices.sup_set (Arith.image analyze_rule r);

check_linear_trs ::
  forall a b.
    (Shows_Literal.Showl a, Arith.Ceq b, Arith.Ccompare b, Arith.Set_impl b,
      Shows_Literal.Showl b) => [(Term a b, Term a b)] ->
                                  Sum_Type.Sum (String -> String) ();
check_linear_trs r =
  Error_Monad.catch_error
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ x ->
          (if (case x of {
                (l, ra) -> linear_term l && linear_term ra;
              })
            then Sum_Type.Inr () else Sum_Type.Inl x))
        r)
      (\ x -> Sum_Type.Inl (snd x)))
    (\ _ ->
      Sum_Type.Inl
        (showsl_trs r . Shows_Literal.showsl_literal "\nis not linear\n"));

insert_funas_term ::
  forall a b. (Eq a) => Term a b -> [(a, Arith.Nat)] -> [(a, Arith.Nat)];
insert_funas_term (Var x) fs = fs;
insert_funas_term (Fun f ts) fs =
  Arith.inserta (f, Arith.size_list ts) (Arith.foldr insert_funas_term ts fs);

insert_funas_rule ::
  forall a b.
    (Eq a) => (Term a b, Term a b) -> [(a, Arith.Nat)] -> [(a, Arith.Nat)];
insert_funas_rule r fs =
  insert_funas_term (fst r) (insert_funas_term (snd r) fs);

insert_funas_trs ::
  forall a b.
    (Eq a) => [(Term a b, Term a b)] -> [(a, Arith.Nat)] -> [(a, Arith.Nat)];
insert_funas_trs trs = Arith.foldr insert_funas_rule trs;

insert_roots_rule ::
  forall a b.
    (Eq a) => (Term a b, Term a b) -> [(a, Arith.Nat)] -> [(a, Arith.Nat)];
insert_roots_rule r fs =
  Arith.foldr Arith.inserta
    (Option_Util.option_to_list (root (fst r)) ++
      Option_Util.option_to_list (root (snd r)))
    fs;

insert_roots_trs ::
  forall a b.
    (Eq a) => [(Term a b, Term a b)] -> [(a, Arith.Nat)] -> [(a, Arith.Nat)];
insert_roots_trs trs = Arith.foldr insert_roots_rule trs;

insert_vars_rule :: forall a b. (Eq b) => (Term a b, Term a b) -> [b] -> [b];
insert_vars_rule r xs = insert_vars_term (fst r) (insert_vars_term (snd r) xs);

showsl_afs ::
  forall a.
    (Shows_Literal.Showl a) => [((a, Arith.Nat), Af_entry)] -> String -> String;
showsl_afs af =
  Arith.foldr
    (\ (a, b) ->
      (case a of {
        (f, n) ->
          (\ e ->
            (((((Shows_Literal.showsl_literal "pi(" . Shows_Literal.showsl f) .
                 Shows_Literal.showsl_literal "/") .
                Shows_Literal.showsl_nat n) .
               Shows_Literal.showsl_literal ") = ") .
              (case e of {
                Collapse i -> Shows_Literal.showsl_nat (Arith.suc i);
                AFList ids -> Shows_Literal.showsl_list_nat (map Arith.suc ids);
              })) .
              Shows_Literal.showsl_literal "\n");
      })
        b)
    af;

check_funas_term ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Shows_Literal.Showl a,
      Shows_Literal.Showl b) => Arith.Set (a, Arith.Nat) ->
                                  Term a b ->
                                    Sum_Type.Sum (String -> String) ();
check_funas_term fa (Fun f ts) =
  Error_Monad.bind
    (Check_Monad.check (Arith.member (f, Arith.size_list ts) fa)
      (((showsl_terma (Fun f ts) .
          Shows_Literal.showsl_lit "problem: root of subterm  ") .
         Shows_Literal.showsl f) .
        Shows_Literal.showsl_lit " not in signature\n"))
    (\ _ ->
      Error_Monad.catch_error (Error_Monad.forallM (check_funas_term fa) ts)
        (\ x -> Sum_Type.Inl (snd x)));
check_funas_term f (Var uu) = Sum_Type.Inr ();

is_renaming_impl :: forall a b. (Eq a, Eq b) => [(a, Term b a)] -> Bool;
is_renaming_impl sigma = let {
                           sigmaa = map snd (mk_subst_domain sigma);
                         } in all is_Var sigmaa && Arith.distinct sigmaa;

subst_power_impl ::
  forall a b. (Eq a, Eq b) => [(a, Term b a)] -> Arith.Nat -> [(a, Term b a)];
subst_power_impl sigma n =
  (if Arith.equal_nat n Arith.zero_nat then []
    else subst_compose_impl sigma
           (subst_power_impl sigma (Arith.minus_nat n Arith.one_nat)));

ctxt_of_pos_term :: forall a b. [Arith.Nat] -> Term a b -> Actxt a (Term a b);
ctxt_of_pos_term [] t = Hole;
ctxt_of_pos_term (i : ps) (Fun f ts) =
  More f (Arith.take i ts) (ctxt_of_pos_term ps (Arith.nth ts i))
    (Arith.drop (Arith.suc i) ts);

map_funs_term_wa :: forall a b c. ((a, Arith.Nat) -> b) -> Term a c -> Term b c;
map_funs_term_wa fg (Var x) = Var x;
map_funs_term_wa fg (Fun f ts) =
  Fun (fg (f, Arith.size_list ts)) (map (map_funs_term_wa fg) ts);

s :: forall a b c.
       Rel_impl_ext a b c ->
         (Term a b, Term a b) -> Sum_Type.Sum (String -> String) ();
s (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
    co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = s;

rel_impl_s ::
  forall a b.
    Rel_impl_ext a b () ->
      [(Term a b, Term a b)] -> Sum_Type.Sum (String -> String) ();
rel_impl_s ri =
  (\ xs ->
    Error_Monad.catch_error (Error_Monad.forallM (s ri) xs)
      (\ x -> Sum_Type.Inl (snd x)));

intersect_ta ::
  forall a b c.
    (Arith.Finite_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Eq a, Arith.Set_impl a, Arith.Ceq b, Arith.Ccompare b, Eq b,
      Arith.Set_impl b, Arith.Finite_UNIV c, Arith.Cenum c, Arith.Ceq c,
      Arith.Cproper_interval c, Eq c,
      Arith.Set_impl c) => Ta_ext a b () -> Ta_ext c b () -> Ta_ext (a, c) b ();
intersect_ta tA1 tA2 =
  prod_ta tA1 tA2 (Arith.productc (ta_final tA1) (ta_final tA2));

check_CS_subseteq ::
  forall a b.
    (Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => [(Term a b, Term a b)] ->
                                   [(Term a b, Term a b)] ->
                                     Sum_Type.Sum (Term a b, Term a b) ();
check_CS_subseteq r s =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ (l, ra) -> Check_Monad.check (any (instance_rule (l, ra)) s) (l, ra))
      r)
    (\ x -> Sum_Type.Inl (snd x));

map_funs_rules_wa ::
  forall a b c.
    ((a, Arith.Nat) -> b) -> [(Term a c, Term a c)] -> [(Term b c, Term b c)];
map_funs_rules_wa fg r =
  map (\ (l, ra) -> (map_funs_term_wa fg l, map_funs_term_wa fg ra)) r;

afs_with_af ::
  forall a.
    (Compare.Compare_order a) => Afs a ->
                                   ((a, Arith.Nat) -> Arith.Set Arith.Nat) ->
                                     (a, Arith.Nat) -> Arith.Set Arith.Nat;
afs_with_af pia pi fn =
  (case afs pia fn of {
    Collapse j ->
      Arith.insert j
        (Arith.set_empty (Phantom_Type.of_phantom Arith.set_impl_nat));
    AFList ids ->
      (if ids == Arith.upt Arith.zero_nat (snd fn) then pi fn
        else Arith.set ids);
  });

natural :: forall a. Sharp a -> a;
natural (Sharp l) = l;
natural (Flat l) = l;

map_formula :: forall a b. (a -> b) -> Formula a -> Formula b;
map_formula f (Atom x1) = Atom (f x1);
map_formula f (NegAtom x2) = NegAtom (f x2);
map_formula f (Conjunction x3) = Conjunction (map (map_formula f) x3);
map_formula f (Disjunction x4) = Disjunction (map (map_formula f) x4);

hole_poss :: forall a b. Mctxt a b -> Arith.Set [Arith.Nat];
hole_poss (MVar x) =
  Arith.set_empty (Phantom_Type.of_phantom Arith.set_impl_list);
hole_poss MHole =
  Arith.insert []
    (Arith.set_empty (Phantom_Type.of_phantom Arith.set_impl_list));
hole_poss (MFun f cs) =
  Arith.foldr
    (Arith.sup_set .
      (\ i -> Arith.image (\ a -> i : a) (hole_poss (Arith.nth cs i))))
    (Arith.upt Arith.zero_nat (Arith.size_list cs))
    (Arith.set_empty (Phantom_Type.of_phantom Arith.set_impl_list));

num_holes :: forall a b. Mctxt a b -> Arith.Nat;
num_holes (MVar uu) = Arith.zero_nat;
num_holes MHole = Arith.one_nat;
num_holes (MFun uv ctxts) = Groups_List.sum_list (map num_holes ctxts);

check_ground_term ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => Term a b -> Sum_Type.Sum (String -> String) ();
check_ground_term s =
  Check_Monad.check (ground s)
    ((Shows_Literal.showsl_literal "the term " . showsl_terma s) .
      Shows_Literal.showsl_literal " is not a ground term\n");

check_linear_term ::
  forall a b.
    (Shows_Literal.Showl a, Arith.Ceq b, Arith.Ccompare b, Arith.Set_impl b,
      Shows_Literal.Showl b) => Term a b -> Sum_Type.Sum (String -> String) ();
check_linear_term s =
  Check_Monad.check (linear_term s)
    ((Shows_Literal.showsl_literal "the term " . showsl_terma s) .
      Shows_Literal.showsl_literal " is not linear\n");

flatten_term_enum :: forall a b. Term [a] b -> [Term a b];
flatten_term_enum (Var x) = [Var x];
flatten_term_enum (Fun fs ts) = let {
                                  lts = map flatten_term_enum ts;
                                  ss = Missing_List.concat_lists lts;
                                } in concatMap (\ f -> map (Fun f) ss) fs;

sn :: forall a b c. Rel_impl_ext a b c -> Sum_Type.Sum (String -> String) ();
sn (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
     co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = sn;

af :: forall a b c. Rel_impl_ext a b c -> (a, Arith.Nat) -> Arith.Set Arith.Nat;
af (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
     co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = af;

ns :: forall a b c.
        Rel_impl_ext a b c ->
          (Term a b, Term a b) -> Sum_Type.Sum (String -> String) ();
ns (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
     co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = ns;

rel_impl_ns ::
  forall a b.
    Rel_impl_ext a b () ->
      [(Term a b, Term a b)] -> Sum_Type.Sum (String -> String) ();
rel_impl_ns ri =
  (\ xs ->
    Error_Monad.catch_error (Error_Monad.forallM (ns ri) xs)
      (\ x -> Sum_Type.Inl (snd x)));

rep_rel_impl_type ::
  forall b a c. Rel_impl_type b a c -> c -> Rel_impl_ext b a ();
rep_rel_impl_type (Abs_rel_impl_type x) = x;

rel_impl_of :: forall a b c. Rel_impl_type a b c -> c -> Rel_impl_ext a b ();
rel_impl_of xa = rep_rel_impl_type xa;

showsl_funa ::
  forall a. (Shows_Literal.Showl a) => (a, Arith.Nat) -> String -> String;
showsl_funa (f, n) =
  (Shows_Literal.showsl f . Shows_Literal.showsl_lit "/") .
    Shows_Literal.showsl_nat n;

is_sharp :: forall a. Sharp a -> Bool;
is_sharp (Flat uu) = False;
is_sharp (Sharp uv) = True;

update_transitions_impl ::
  forall a b c d e f.
    Lts_impl a b c d e -> [(f, Transition_rule a b c d)] -> Lts_impl a b c d f;
update_transitions_impl (Lts_Impl i tsa lc) ts = Lts_Impl i ts lc;

del_transitions_impl ::
  forall a b c d e.
    (Arith.Ceq e, Arith.Ccompare e,
      Arith.Set_impl e) => Lts_impl a b c d e -> [e] -> Lts_impl a b c d e;
del_transitions_impl p td =
  update_transitions_impl p (diff_by_label (transitions_impl p) (Arith.set td));

partition_by :: forall a. [a] -> [Arith.Nat] -> [[a]];
partition_by xs [] = [];
partition_by xs (y : ys) = Arith.take y xs : partition_by (Arith.drop y xs) ys;

fill_holes :: forall a b. Mctxt a b -> [Term a b] -> Term a b;
fill_holes (MVar x) uu = Var x;
fill_holes MHole [t] = t;
fill_holes (MFun f cs) ts =
  Fun f (map (\ i ->
               fill_holes (Arith.nth cs i)
                 (Arith.nth (partition_by ts (map num_holes cs)) i))
          (Arith.upt Arith.zero_nat (Arith.size_list cs)));

split_term ::
  forall a b. (Term a b -> Bool) -> Term a b -> (Mctxt a b, [Term a b]);
split_term p (Var x) = (if p (Var x) then (MHole, [Var x]) else (MVar x, []));
split_term p (Fun f ts) =
  (if p (Fun f ts) then (MHole, [Fun f ts])
    else let {
           us = map (split_term p) ts;
         } in (MFun f (map fst us), concatMap snd us));

uncap_till :: forall a b. (Term a b -> Bool) -> Term a b -> [Term a b];
uncap_till p (Var x) = (if p (Var x) then [Var x] else []);
uncap_till p (Fun f ts) =
  (if p (Fun f ts) then [Fun f ts] else concatMap (uncap_till p) ts);

subst_replace_impl ::
  forall a b. (Eq a) => [(a, Term b a)] -> a -> Term b a -> [(a, Term b a)];
subst_replace_impl sigma x t = (x, t) : filter (\ (y, _) -> not (y == x)) sigma;

cpx ::
  forall a b c.
    Rel_impl_ext a b c ->
      Complexity.Complexity_measure a b ->
        Complexity.Complexity_class -> Sum_Type.Sum (String -> String) ();
cpx (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
      co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = cpx;

nst ::
  forall a b c.
    Rel_impl_ext a b c ->
      (Term a b, Term a b) -> Sum_Type.Sum (String -> String) ();
nst (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
      co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = nst;

rel_impl_nst ::
  forall a b.
    Rel_impl_ext a b () ->
      [(Term a b, Term a b)] -> Sum_Type.Sum (String -> String) ();
rel_impl_nst ri =
  (\ xs ->
    Error_Monad.catch_error (Error_Monad.forallM (nst ri) xs)
      (\ x -> Sum_Type.Inl (snd x)));

r_root :: forall a b. Ta_rule a b -> b;
r_root (TA_rule x1 x2 x3) = x1;

non_collapsing_impl :: forall a b c. [(a, Term b c)] -> Bool;
non_collapsing_impl r = all ((\ t -> not (is_Var t)) . snd) r;

lp_monom :: Rat.Rat -> Arith.Nat -> Linear_poly;
lp_monom c x =
  LinearPoly
    (if Rat.equal_rat c Rat.zero_rat then Finite_Map.fmempty
      else Finite_Map.fmupd x c Finite_Map.fmempty);

funas_mctxt ::
  forall a b.
    (Arith.Finite_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Compare.Compare a, Eq a, Arith.Set_impl a, Compare.Compare b,
      Eq b) => Mctxt a b -> Arith.Set (a, Arith.Nat);
funas_mctxt (MFun f cs) =
  Arith.sup_set (Arith.insert (f, Arith.size_list cs) Arith.bot_set)
    (Complete_Lattices.sup_set (Arith.image funas_mctxt (Arith.set cs)));
funas_mctxt (MVar v) = Arith.bot_set;
funas_mctxt MHole = Arith.bot_set;

subst_compose_impla ::
  forall a b.
    (Eq a, Eq b) => [(a, Term b a)] -> (a -> Term b a) -> [(a, Term b a)];
subst_compose_impla sigma rho =
  map (\ (x, s) -> (x, eval_term Fun s rho)) (mk_subst_domain sigma);

desc :: forall a b c. Rel_impl_ext a b c -> String -> String;
desc (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
       co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = desc;

mono ::
  forall a b c.
    Rel_impl_ext a b c ->
      [(a, Arith.Nat)] -> Sum_Type.Sum (String -> String) ();
mono (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
       co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = mono;

iterative_join_search_main ::
  forall a b.
    (Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => [(Term a b, Term a b)] ->
                                   Term a b ->
                                     Term a b -> Arith.Nat -> Arith.Nat -> Bool;
iterative_join_search_main r s t i n =
  (if Arith.less_eq_nat i n
    then not (null (Arith.inter_list_set (reachable_terms r s i)
                     (reachable_terms r t i))) ||
           iterative_join_search_main r s t (Arith.suc i) n
    else False);

iterative_join_search ::
  forall a b.
    (Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => [(Term a b, Term a b)] ->
                                   Term a b -> Term a b -> Arith.Nat -> Bool;
iterative_join_search r s t n =
  iterative_join_search_main r s t Arith.zero_nat n;

check_join_BFS_limit ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => Arith.Nat ->
                                  [(Term a b, Term a b)] ->
                                    Term a b ->
                                      Term a b ->
Sum_Type.Sum (String -> String) ();
check_join_BFS_limit n r s t =
  Check_Monad.check (iterative_join_search r s t n)
    ((((((Shows_Literal.showsl_literal
            "could not find a joining sequence of length at most " .
           Shows_Literal.showsl_nat n) .
          Shows_Literal.showsl_literal " for the terms ") .
         showsl_terma s) .
        Shows_Literal.showsl_literal " and ") .
       showsl_terma t) .
      Shows_Literal.showsl_literal "\n");

check_mono_afs ::
  forall a.
    (Arith.Ceq a,
      Arith.Ccompare a) => Afs a -> Sum_Type.Sum (String -> String) ();
check_mono_afs pi =
  Check_Monad.check (mono_afs pi)
    (Shows_Literal.showsl_literal "argument filter is not monotone");

trivial_clause_checker :: forall a. (Eq a) => Formula a -> Bool;
trivial_clause_checker f = (case f of {
                             Disjunction a -> trivial_checker a;
                           });

gctxts_to_terms_intern ::
  forall a b.
    (Arith.Nat -> a) -> Arith.Nat -> [Gctxt b a] -> (Arith.Nat, [Term b a]);
gctxts_to_terms_intern iv i (GCFun f ts : cs) =
  (case gctxts_to_terms_intern iv i ts of {
    (i1, res1) -> (case gctxts_to_terms_intern iv i1 cs of {
                    (i2, res2) -> (i2, Fun f res1 : res2);
                  });
  });
gctxts_to_terms_intern iv i (GCHole : cs) =
  (case gctxts_to_terms_intern iv (Arith.plus_nat i Arith.one_nat) cs of {
    (ia, res) -> (ia, Var (iv i) : res);
  });
gctxts_to_terms_intern iv i [] = (i, []);

mgu_vd_string ::
  forall a.
    (Eq a) => Term a [Arith.Char] ->
                Term a [Arith.Char] ->
                  Maybe ([Arith.Char] -> Term a [Arith.Char],
                          [Arith.Char] -> Term a [Arith.Char]);
mgu_vd_string =
  mgu_var_disjoint_generic (\ a -> Arith.char_0x78 : a)
    (\ a -> Arith.char_0x79 : a);

gc_matcher ::
  forall a.
    (Eq a) => Gctxt a [Arith.Char] ->
                Term a [Arith.Char] ->
                  Maybe ([Arith.Char] -> Term a [Arith.Char]);
gc_matcher c l =
  Arith.map_option fst
    (mgu_vd_string l
      (Arith.hda
        (snd (gctxts_to_terms_intern
               (\ i ->
                 Arith.char_0x78 :
                   Show_Instances.shows_prec_nat Arith.zero_nat i [])
               Arith.zero_nat [c]))));

ground_mctxt :: forall a b. Mctxt a b -> Bool;
ground_mctxt (MVar uu) = False;
ground_mctxt MHole = True;
ground_mctxt (MFun f cs) = all ground_mctxt cs;

rename_vars_exp :: forall a b c d. (a -> b) -> Term c (a, d) -> Term c (b, d);
rename_vars_exp r = map_term id (Arith.map_prod r id);

intp_actxt :: forall a b. (a -> [b] -> b) -> Actxt a b -> b -> b;
intp_actxt i Hole a = a;
intp_actxt i (More f ls c rs) a = i f (ls ++ intp_actxt i c a : rs);

funas_args_term_list :: forall a b. Term a b -> [(a, Arith.Nat)];
funas_args_term_list t = concatMap funas_term_list (args t);

valid :: forall a b c. Rel_impl_ext a b c -> Sum_Type.Sum (String -> String) ();
valid (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
        co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = valid;

check_left_linear_trs ::
  forall a b.
    (Shows_Literal.Showl a, Arith.Ceq b, Arith.Ccompare b, Arith.Set_impl b,
      Shows_Literal.Showl b) => [(Term a b, Term a b)] ->
                                  Sum_Type.Sum (String -> String) ();
check_left_linear_trs trs =
  Error_Monad.catch_error
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ x ->
          (if linear_term (fst x) then Sum_Type.Inr () else Sum_Type.Inl x))
        trs)
      (\ x -> Sum_Type.Inl (snd x)))
    (\ _ ->
      Sum_Type.Inl
        (showsl_trs trs .
          Shows_Literal.showsl_literal "\nis not left-linear\n"));

insert_funas_args_term ::
  forall a b. (Eq a) => Term a b -> [(a, Arith.Nat)] -> [(a, Arith.Nat)];
insert_funas_args_term t fs = Arith.foldr insert_funas_term (args t) fs;

insert_funas_args_rule ::
  forall a b.
    (Eq a) => (Term a b, Term a b) -> [(a, Arith.Nat)] -> [(a, Arith.Nat)];
insert_funas_args_rule r fs =
  insert_funas_args_term (fst r) (insert_funas_args_term (snd r) fs);

insert_funas_args_trs ::
  forall a b.
    (Eq a) => [(Term a b, Term a b)] -> [(a, Arith.Nat)] -> [(a, Arith.Nat)];
insert_funas_args_trs trs = Arith.foldr insert_funas_args_rule trs;

permutation_afs :: forall a. (Arith.Ceq a, Arith.Ccompare a) => Afs a -> Bool;
permutation_afs pi =
  Arith.ball (afs_syms pi)
    (\ (f, n) ->
      (case afs pi (f, n) of {
        Collapse _ -> False;
        AFList xs ->
          Arith.set_eq (Arith.set xs)
            (Set_Interval.atLeastLessThan Arith.zero_nat n) &&
            Arith.distinct xs;
      }));

if_Fun_in_set ::
  forall a b.
    (Arith.Ceq a,
      Arith.Ccompare a) => Arith.Set (a, Arith.Nat) -> Term a b -> Bool;
if_Fun_in_set f = (\ t -> is_Var t || Arith.member (Arith.the (root t)) f);

mctxt_of_term :: forall a b. Term a b -> Mctxt a b;
mctxt_of_term (Var x) = MVar x;
mctxt_of_term (Fun f ts) = MFun f (map mctxt_of_term ts);

no_complexity_check :: forall a b. a -> b -> Sum_Type.Sum (String -> String) ();
no_complexity_check =
  (\ _ _ ->
    Sum_Type.Inl
      (Shows_Literal.showsl_literal "complexity analysis unsupported"));

faulty_rel_impl ::
  forall a b.
    HOL.Itself a ->
      HOL.Itself b ->
        (String -> String) -> (String -> String) -> Rel_impl_ext a b ();
faulty_rel_impl uu uv err desc =
  Rel_impl_ext (Sum_Type.Inl err) (Sum_Type.Inr ()) desc
    (\ _ -> Sum_Type.Inr ()) (\ _ -> Sum_Type.Inr ()) (\ _ -> Sum_Type.Inr ())
    Term_Order.full_af Term_Order.full_af (Sum_Type.Inr ()) (Sum_Type.Inr ())
    (Sum_Type.Inr ()) (Sum_Type.Inr ()) (Sum_Type.Inr ()) (Sum_Type.Inr ())
    Term_Order.empty_af (\ _ -> Sum_Type.Inr ()) Nothing Nothing
    no_complexity_check ();

top_af ::
  forall a b c. Rel_impl_ext a b c -> (a, Arith.Nat) -> Arith.Set Arith.Nat;
top_af
  (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
    co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = top_af;

fpair_f :: forall a. Filtered a -> a;
fpair_f (FPair x1 x2) = x1;

co_rewr ::
  forall a b c. Rel_impl_ext a b c -> Sum_Type.Sum (String -> String) ();
co_rewr
  (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
    co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = co_rewr;

mono_af ::
  forall a b c. Rel_impl_ext a b c -> (a, Arith.Nat) -> Arith.Set Arith.Nat;
mono_af
  (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
    co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = mono_af;

not_sst :: forall a b c. Rel_impl_ext a b c -> Maybe [(a, Arith.Nat)];
not_sst
  (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
    co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = not_sst;

not_wst :: forall a b c. Rel_impl_ext a b c -> Maybe [(a, Arith.Nat)];
not_wst
  (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
    co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = not_wst;

subst_s ::
  forall a b c. Rel_impl_ext a b c -> Sum_Type.Sum (String -> String) ();
subst_s
  (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
    co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = subst_s;

standard ::
  forall a b c. Rel_impl_ext a b c -> Sum_Type.Sum (String -> String) ();
standard
  (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
    co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = standard;

rel_impl_redpair ::
  forall a b. Rel_impl_ext a b () -> Sum_Type.Sum (String -> String) ();
rel_impl_redpair ri =
  Error_Monad.catch_error
    (Error_Monad.bind (valid ri)
      (\ _ ->
        Error_Monad.bind (standard ri)
          (\ _ ->
            Error_Monad.bind
              (Error_Monad.catch_error (sn ri)
                (\ x ->
                  Sum_Type.Inl
                    (x . Shows_Literal.showsl_lit
                           "\nproblem in ensuring strong normalization of relation")))
              (\ _ ->
                Error_Monad.catch_error (subst_s ri)
                  (\ x ->
                    Sum_Type.Inl
                      (x . Shows_Literal.showsl_lit
                             "\nproblem in ensuring stability of strict relation"))))))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit "problem with being a reduction pair\n" . x));

ce_compat ::
  forall a b c. Rel_impl_ext a b c -> Sum_Type.Sum (String -> String) ();
ce_compat
  (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
    co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = ce_compat;

top_refl ::
  forall a b c. Rel_impl_ext a b c -> Sum_Type.Sum (String -> String) ();
top_refl
  (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
    co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = top_refl;

filtered_rel_impl ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Compare.Compare_order a, Arith.Set_impl a,
      Shows_Literal.Showl a,
      Shows_Literal.Showl b) => [((a, Arith.Nat), Af_entry)] ->
                                  Rel_impl_ext (Filtered a) b () ->
                                    Rel_impl_ext a b ();
filtered_rel_impl pi rp =
  let {
    afso = afs_of pi;
    afs = Arith.the afso;
    af = afs_to_af afs;
  } in Rel_impl_ext
         (Error_Monad.bind
           (Check_Monad.check (not (Arith.is_none afso))
             (Shows_Literal.showsl_literal
               "invalid positions in argument filter"))
           (\ _ ->
             Error_Monad.bind (valid rp)
               (\ _ -> Error_Monad.bind (top_refl rp) (\ _ -> standard rp))))
         (Sum_Type.Inr ())
         (((Shows_Literal.showsl_literal "Argument Filter:\n" . showsl_afs pi) .
            Shows_Literal.showsl_literal "\n") .
           desc rp)
         (afs_check (Shows_Literal.showsl_literal ">") afs (s rp))
         (afs_check (Shows_Literal.showsl_literal ">=") afs (ns rp))
         (afs_check (Shows_Literal.showsl_literal ">=") afs (nst rp)) af
         Term_Order.full_af (sn rp) (subst_s rp) (ce_compat rp) (co_rewr rp)
         (Sum_Type.Inl
           (Shows_Literal.showsl_lit
             "top-mono with argument filter not yet supported"))
         (Sum_Type.Inr ()) Term_Order.empty_af
         (\ sig ->
           Error_Monad.bind (check_mono_afs afs)
             (\ _ -> mono rp (afs_sig afs sig)))
         (Arith.map_option
           (\ fs -> map fst pi ++ map (\ (f, a) -> (fpair_f f, a)) fs)
           (not_wst rp))
         Nothing no_complexity_check ();

check_trivial_implication :: forall a. (Eq a) => Formula a -> Formula a -> Bool;
check_trivial_implication phi psi =
  all (\ phia ->
        let {
          c_phis = get_conjunctions phia;
        } in any (\ psia -> all (Arith.membera c_phis) (get_conjunctions psia))
               (get_disjunctions psi))
    (get_disjunctions phi);

refine_transition_formula ::
  forall a b c d.
    Transition_rule a b c d ->
      Formula (Term a (Trans_var b, c)) -> Transition_rule a b c d;
refine_transition_formula (Transition l r phi) psi =
  Transition l r (form_and phi psi);

actxt_compose :: forall a b. Actxt a b -> Actxt a b -> Actxt a b;
actxt_compose Hole d = d;
actxt_compose (More f ls c rs) d = More f ls (actxt_compose c d) rs;

top_mono ::
  forall a b c. Rel_impl_ext a b c -> Sum_Type.Sum (String -> String) ();
top_mono
  (Rel_impl_ext valid standard desc s ns nst af top_af sn subst_s ce_compat
    co_rewr top_mono top_refl mono_af mono not_wst not_sst cpx more)
  = top_mono;

refine_transition_formulas ::
  forall a b c d e.
    Lts_impl a b c d e ->
      (e -> Formula (Term a (Trans_var b, c))) -> Lts_impl a b c d e;
refine_transition_formulas p f =
  Lts_Impl (initiala p)
    (map (\ (tr, tau) -> (tr, refine_transition_formula tau (f tr)))
      (transitions_impl p))
    (assertion_impl p);

add_funas_mctxt ::
  forall a b. Mctxt a b -> [(a, Arith.Nat)] -> [(a, Arith.Nat)];
add_funas_mctxt (MFun f cs) fs =
  (f, Arith.size_list cs) : Arith.foldr add_funas_mctxt cs fs;
add_funas_mctxt (MVar v) fs = fs;
add_funas_mctxt MHole fs = fs;

funas_mctxt_list :: forall a b. Mctxt a b -> [(a, Arith.Nat)];
funas_mctxt_list c = add_funas_mctxt c [];

vars_mctxt ::
  forall a b.
    (Compare.Compare a, Eq a, Arith.Finite_UNIV b, Arith.Cenum b, Arith.Ceq b,
      Arith.Cproper_interval b, Compare.Compare b, Eq b,
      Arith.Set_impl b) => Mctxt a b -> Arith.Set b;
vars_mctxt (MVar x1) = Arith.insert x1 Arith.bot_set;
vars_mctxt MHole = Arith.bot_set;
vars_mctxt (MFun x31 x32) =
  Complete_Lattices.sup_set (Arith.image vars_mctxt (Arith.set x32));

is_inverse_renaming_impl ::
  forall a b. (Eq a, Eq b) => [(a, Term b a)] -> [(a, Term b a)];
is_inverse_renaming_impl sigma = let {
                                   a = mk_subst_domain sigma;
                                 } in map (\ (x, y) -> (the_Var y, Var x)) a;

rel_impl_redtriple ::
  forall a b. Rel_impl_ext a b () -> Sum_Type.Sum (String -> String) ();
rel_impl_redtriple ri =
  Error_Monad.catch_error
    (Error_Monad.bind (valid ri)
      (\ _ ->
        Error_Monad.bind (standard ri)
          (\ _ ->
            Error_Monad.bind
              (Error_Monad.catch_error (top_refl ri)
                (\ x ->
                  Sum_Type.Inl
                    (x . Shows_Literal.showsl_lit
                           "\nproblem in ensuring reflexivity of top-non-strict relation")))
              (\ _ ->
                Error_Monad.bind
                  (Error_Monad.catch_error (sn ri)
                    (\ x ->
                      Sum_Type.Inl
                        (x . Shows_Literal.showsl_lit
                               "\nproblem in ensuring strong normalization of relation")))
                  (\ _ ->
                    Error_Monad.catch_error (subst_s ri)
                      (\ x ->
                        Sum_Type.Inl
                          (x . Shows_Literal.showsl_lit
                                 "\nproblem in ensuring stability of strict relation")))))))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit "problem with being a reduction triple\n" .
          x));

call_graph_impl :: forall a b c d e. (Eq d) => Lts_impl a b c d e -> [(d, d)];
call_graph_impl r =
  Arith.remdups
    (map (\ tau -> (source (snd tau), target (snd tau))) (transitions_impl r));

flat_transition ::
  forall a b c d. Transition_rule a b c d -> Transition_rule a b c (Sharp d);
flat_transition (Transition l r phi) = Transition (Flat l) (Flat r) phi;

subst_apply_mctxt :: forall a b c. Mctxt a b -> (b -> Term a c) -> Mctxt a c;
subst_apply_mctxt MHole uu = MHole;
subst_apply_mctxt (MVar x) sigma = mctxt_of_term (sigma x);
subst_apply_mctxt (MFun f cs) sigma =
  MFun f (map (\ c -> subst_apply_mctxt c sigma) cs);

map_actxt :: forall a b c d. (a -> b) -> (c -> d) -> Actxt a c -> Actxt b d;
map_actxt f1 f2 Hole = Hole;
map_actxt f1 f2 (More x21 x22 x23 x24) =
  More (f1 x21) (map f2 x22) (map_actxt f1 f2 x23) (map f2 x24);

filtered_rel_impl_af ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Compare.Compare_order a, Arith.Set_impl a,
      Shows_Literal.Showl a,
      Shows_Literal.Showl b) => [((a, Arith.Nat), Af_entry)] ->
                                  Rel_impl_ext a b () -> Rel_impl_ext a b ();
filtered_rel_impl_af pi rp =
  let {
    afso = afs_of pi;
    afs = Arith.the afso;
    afa = afs_with_af afs (af rp);
  } in Rel_impl_ext
         (Error_Monad.bind
           (Check_Monad.check (not (Arith.is_none afso))
             (Shows_Literal.showsl_literal
               "invalid positions in argument filter"))
           (\ _ ->
             Error_Monad.bind (valid rp)
               (\ _ -> Error_Monad.bind (top_refl rp) (\ _ -> standard rp))))
         (Sum_Type.Inr ())
         (((Shows_Literal.showsl_literal "Argument Filter:\n" . showsl_afs pi) .
            Shows_Literal.showsl_literal "\n") .
           desc rp)
         (af_check (Shows_Literal.showsl_literal ">") afs (s rp))
         (af_check (Shows_Literal.showsl_literal ">=") afs (ns rp))
         (af_check (Shows_Literal.showsl_literal ">=") afs (nst rp)) afa
         Term_Order.full_af (sn rp) (subst_s rp) (ce_compat rp) (co_rewr rp)
         (Sum_Type.Inl
           (Shows_Literal.showsl_lit
             "top-mono with argument filter not yet supported"))
         (Sum_Type.Inr ()) Term_Order.empty_af
         (\ sig ->
           Error_Monad.bind (check_mono_afs afs)
             (\ _ -> mono rp (af_sig afs sig)))
         (Arith.map_option (\ a -> map fst pi ++ a) (not_wst rp)) Nothing
         no_complexity_check ();

sharp_transition ::
  forall a b c d. Transition_rule a b c d -> Transition_rule a b c (Sharp d);
sharp_transition (Transition l r phi) = Transition (Sharp l) (Sharp r) phi;

initial_relation ::
  forall a b c.
    (Arith.Card_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Eq a, Arith.Set_impl a, Arith.Ccompare b, Compare.Compare b, Eq b,
      Arith.Ceq c, Arith.Ccompare c, Compare.Compare c, Eq c,
      Arith.Set_impl c) => Ta_ext a b () ->
                             Arith.Set (Term b c, Term b c) ->
                               Maybe (Arith.Set (a, a));
initial_relation ta r =
  let {
    q_qs = initial_rel ta r;
  } in (if Arith.member Arith.bot_set (Arith.image snd q_qs) then Nothing
         else Just (Complete_Lattices.sup_set
                     (Arith.image (\ (q, a) -> Arith.image (\ aa -> (q, aa)) a)
                       q_qs)));

decide_coherent_compatible_main ::
  forall a b c.
    (Arith.Card_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Eq a, Arith.Set_impl a, Arith.Ccompare b, Compare.Compare b, Eq b,
      Arith.Ceq c, Arith.Ccompare c, Compare.Compare c, Eq c,
      Arith.Set_impl c) => Ta_ext a b () ->
                             Arith.Set (Term b c, Term b c) ->
                               (Maybe (Arith.Set (a, a)) ->
                                 Maybe (Arith.Set (a, a))) ->
                                 Bool;
decide_coherent_compatible_main ta r normalizer =
  (case normalizer (initial_relation ta r) of {
    Nothing -> False;
    Just rel ->
      Arith.less_eq_set (Relation.image rel (ta_final ta)) (ta_final ta);
  });

normalize_main ::
  forall a b.
    (Arith.Finite_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Eq a, Arith.Set_impl a, Arith.Ccompare b,
      Eq b) => Ta_ext a b () ->
                 Arith.Set (a, a) ->
                   Arith.Set (a, a) -> Maybe (Arith.Set (a, a));
normalize_main ta rel accu =
  let {
    new = new_states ta rel;
  } in (if Arith.member Nothing (Arith.image snd new) then Nothing
         else let {
                new_rel = Arith.image (\ (x, y) -> (x, Arith.the y)) new;
                new_accu = Arith.sup_set accu rel;
                todo = Arith.minus_set new_rel new_accu;
              } in (if Arith.less_eq_set todo Arith.bot_set then Just new_accu
                     else normalize_main ta todo new_accu));

normalize ::
  forall a b.
    (Arith.Finite_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Eq a, Arith.Set_impl a, Arith.Ccompare b,
      Eq b) => Ta_ext a b () ->
                 Maybe (Arith.Set (a, a)) -> Maybe (Arith.Set (a, a));
normalize ta Nothing = Nothing;
normalize ta (Just rel) = normalize_main ta rel Arith.bot_set;

decide_coherent_compatible ::
  forall a b c.
    (Arith.Card_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Eq a, Arith.Set_impl a, Arith.Ccompare b, Compare.Compare b, Eq b,
      Arith.Ceq c, Arith.Ccompare c, Compare.Compare c, Eq c,
      Arith.Set_impl c) => Ta_ext a b () ->
                             Arith.Set (Term b c, Term b c) -> Bool;
decide_coherent_compatible ta r =
  decide_coherent_compatible_main ta r (normalize ta);

closed_under_rewriting ::
  forall a b c.
    (Arith.Card_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Eq a, Arith.Set_impl a, Arith.Ccompare b, Compare.Compare b,
      HOL.Default b, Eq b, Arith.Ceq c, Arith.Ccompare c, Compare.Compare c,
      Eq c,
      Arith.Set_impl c) => Ta_ext a b () ->
                             Arith.Set (Term b c, Term b c) -> Bool;
closed_under_rewriting ta r = decide_coherent_compatible (trim_ta ta) r;

showsl_formula ::
  forall a. (a -> String -> String) -> Formula a -> String -> String;
showsl_formula showsl_atom (Atom a) = showsl_atom a;
showsl_formula showsl_atom (NegAtom a) =
  (Shows_Literal.showsl_literal "! (" . showsl_atom a) .
    Shows_Literal.showsl_literal ")";
showsl_formula showsl_atom (Conjunction fs) =
  let {
    a = map (showsl_formula showsl_atom) fs;
  } in Shows_Literal.showsl_list_gen id "True" "Conj[" ", " "]" a;
showsl_formula showsl_atom (Disjunction fs) =
  let {
    a = map (showsl_formula showsl_atom) fs;
  } in Shows_Literal.showsl_list_gen id "False" "Disj[" ", " "]" a;

rel_impl_mono_redpair ::
  forall a b.
    Rel_impl_ext a b () ->
      [(Term a b, Term a b)] ->
        [(Term a b, Term a b)] -> Sum_Type.Sum (String -> String) ();
rel_impl_mono_redpair ri s ns =
  Error_Monad.catch_error
    (Error_Monad.bind (valid ri)
      (\ _ ->
        Error_Monad.bind (standard ri)
          (\ _ ->
            Error_Monad.bind
              (Error_Monad.catch_error (sn ri)
                (\ x ->
                  Sum_Type.Inl
                    (x . Shows_Literal.showsl_lit
                           "\nproblem in ensuring strong normalization of relation")))
              (\ _ ->
                Error_Monad.bind
                  (Error_Monad.catch_error (subst_s ri)
                    (\ x ->
                      Sum_Type.Inl
                        (x . Shows_Literal.showsl_lit
                               "\nproblem in ensuring stability of strict relation")))
                  (\ _ ->
                    Error_Monad.catch_error (mono ri (funas_trs_list (s ++ ns)))
                      (\ x ->
                        Sum_Type.Inl
                          (x . Shows_Literal.showsl_lit
                                 "\nproblem in ensuring monotonicity of strict relation")))))))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "problem with being a monotone reduction pair\n" .
          x));

showsl_actxta ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => Actxt a b -> String -> String;
showsl_actxta t = showsl_actxt Shows_Literal.showsl Shows_Literal.showsl t;

rel_impl_root_redtriple ::
  forall a b. Rel_impl_ext a b () -> Sum_Type.Sum (String -> String) ();
rel_impl_root_redtriple ri =
  Error_Monad.catch_error
    (Error_Monad.bind (valid ri)
      (\ _ ->
        Error_Monad.bind
          (Error_Monad.catch_error (sn ri)
            (\ x ->
              Sum_Type.Inl
                (x . Shows_Literal.showsl_lit
                       "\nproblem in ensuring strong normalization of relation")))
          (\ _ ->
            Error_Monad.bind
              (Error_Monad.catch_error (subst_s ri)
                (\ x ->
                  Sum_Type.Inl
                    (x . Shows_Literal.showsl_lit
                           "\nproblem in ensuring stability of strict relation")))
              (\ _ ->
                Error_Monad.catch_error (top_mono ri)
                  (\ x ->
                    Sum_Type.Inl
                      (x . Shows_Literal.showsl_lit
                             "\nproblem in monotonicity from non-root to root"))))))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "problem with being a root-reduction triple\n" .
          x));

comp_res_of_order :: Comparator.Order -> Intf_Comp.Comp_res;
comp_res_of_order Comparator.Eqa = Intf_Comp.EQUAL;
comp_res_of_order Comparator.Lt = Intf_Comp.LESS;
comp_res_of_order Comparator.Gt = Intf_Comp.GREATER;

compare_res :: forall a. (Compare.Compare a) => a -> a -> Intf_Comp.Comp_res;
compare_res x y = comp_res_of_order (Compare.compare x y);

ta_det_impl :: forall a b c d e f g. (a, (b, (c, (d, (e, (f, g)))))) -> f;
ta_det_impl (f, (r, (e, (rhs, (idx, (det, x)))))) = det;

ta_eps_impl ::
  forall a b c d e f g h. (a, (b, (c, (d, (e, (f, (g, h))))))) -> c;
ta_eps_impl (f, (r, (e, (rhs, (idx, (det, (efcl, eicl))))))) = e;

ta_idx_impl ::
  forall a b c d e f g h. (a, (b, (c, (d, (e, (f, (g, h))))))) -> e;
ta_idx_impl (f, (r, (e, (rhs, (idx, (det, (efcl, eicl))))))) = idx;

normalize_lits ::
  forall a b c.
    (Shows_Literal.Showl b) => (Bool ->
                                 Term a (b, c) -> Formula (Term a (b, c))) ->
                                 Formula (Term a (b, c)) ->
                                   Formula (Term a (b, c));
normalize_lits normalize_lit (Conjunction phi_s) =
  Conjunction (map (normalize_lits normalize_lit) phi_s);
normalize_lits normalize_lit (Disjunction phi_s) =
  Disjunction (map (normalize_lits normalize_lit) phi_s);
normalize_lits normalize_lit (NegAtom phi) = normalize_lit False phi;
normalize_lits normalize_lit (Atom phi) = normalize_lit True phi;

set_impl_ty :: Phantom_Type.Phantom Ty Arith.Set_impla;
set_impl_ty = Phantom_Type.Phantom Arith.Set_RBT;

type_of_fun :: Sig -> ([Ty], Ty);
type_of_fun LessF = ([IntT, IntT], BoolT);
type_of_fun LeF = ([IntT, IntT], BoolT);
type_of_fun EqF = ([IntT, IntT], BoolT);
type_of_fun (SumF n) = (Arith.replicate n IntT, IntT);
type_of_fun (ConstF uu) = ([], IntT);
type_of_fun (ProdF n) = (Arith.replicate n IntT, IntT);

def_checker_main ::
  forall a.
    (Eq a) => a -> Ty -> Term Sig (a, Ty) ->
                           Term Sig (a, Ty) ->
                             Term Sig (a, Ty) -> Term Sig (a, Ty) -> Bool;
def_checker_main x ty l1 r1 l2 r2 =
  is_bool type_of_fun
    (Arith.insert BoolT (Arith.set_empty (Phantom_Type.of_phantom set_impl_ty)))
    (Fun LeF [l1, r1]) &&
    has_type type_of_fun r1 ty &&
      is_bool type_of_fun
        (Arith.insert BoolT
          (Arith.set_empty (Phantom_Type.of_phantom set_impl_ty)))
        (Fun LeF [l2, r2]) &&
        equal_term (Var (x, ty)) l1 &&
          equal_term l1 r2 &&
            equal_term l2 r1 && not (contains_var_term (x, ty) r1);

def_checker_maina ::
  forall a. (Eq a) => a -> Ty -> Term Sig (a, Ty) -> Term Sig (a, Ty) -> Bool;
def_checker_maina x ty l1 r1 =
  is_bool type_of_fun
    (Arith.insert BoolT (Arith.set_empty (Phantom_Type.of_phantom set_impl_ty)))
    (Fun EqF [l1, r1]) &&
    has_type type_of_fun r1 ty &&
      equal_term (Var (x, ty)) l1 && not (contains_var_term (x, ty) r1);

def_checker_eq ::
  forall a.
    (Eq a) => a -> Ty -> Formula (Term Sig (a, Ty)) ->
                           Sum_Type.Sum (String -> String) ();
def_checker_eq x ty eq =
  (case eq of {
    Atom (Var _) -> Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid literal");
    Atom (Fun LessF _) ->
      Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid literal");
    Atom (Fun LeF _) ->
      Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid literal");
    Atom (Fun (SumF _) _) ->
      Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid literal");
    Atom (Fun (ConstF _) _) ->
      Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid literal");
    Atom (Fun (ProdF _) _) ->
      Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid literal");
    Atom (Fun EqF []) ->
      Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid literal");
    Atom (Fun EqF [_]) ->
      Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid literal");
    Atom (Fun EqF [l1, r1]) ->
      Check_Monad.check
        (def_checker_maina x ty l1 r1 || def_checker_maina x ty r1 l1)
        (Shows_Literal.showsl_lit "Non-equation not supported");
    Atom (Fun EqF (_ : _ : _ : _)) ->
      Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid literal");
    NegAtom _ -> Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid clause");
    Conjunction _ -> Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid clause");
    Disjunction _ -> Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid clause");
  });

iA_exp_to_tpoly :: forall a. Term Sig (a, Ty) -> Polynomials.Tpoly a Arith.Int;
iA_exp_to_tpoly (Var (a, ty)) = Polynomials.PVar a;
iA_exp_to_tpoly (Fun (SumF uu) asa) =
  Polynomials.PSum (map iA_exp_to_tpoly asa);
iA_exp_to_tpoly (Fun (ConstF a) []) = Polynomials.PNum a;
iA_exp_to_tpoly (Fun (ProdF uv) asa) =
  Polynomials.PMult (map iA_exp_to_tpoly asa);

iA_exp_to_poly ::
  forall a.
    (Eq a,
      Quasi_Order.Linorder a) => Term Sig (a, Ty) ->
                                   [(Polynomials.Monom a, Arith.Int)];
iA_exp_to_poly = Polynomials.poly_of . iA_exp_to_tpoly;

showsl_IA_exp ::
  forall a.
    (Eq a, Quasi_Order.Linorder a,
      Shows_Literal.Showl a) => Term Sig (a, Ty) -> String -> String;
showsl_IA_exp (Fun LessF [s, t]) =
  (showsl_IA_exp s . Shows_Literal.showsl_lit " < ") . showsl_IA_exp t;
showsl_IA_exp (Fun LeF [s, t]) =
  (showsl_IA_exp s . Shows_Literal.showsl_lit " <= ") . showsl_IA_exp t;
showsl_IA_exp (Fun EqF [s, t]) =
  (showsl_IA_exp s . Shows_Literal.showsl_lit " = ") . showsl_IA_exp t;
showsl_IA_exp (Var v) =
  Show_Literal_Polynomial.showsl_poly (iA_exp_to_poly (Var v));
showsl_IA_exp (Fun LeF []) =
  (Show_Literal_Polynomial.showsl_poly ::
    [(Polynomials.Monom a, Arith.Int)] -> String -> String)
    ((iA_exp_to_poly :: Term Sig (a, Ty) -> [(Polynomials.Monom a, Arith.Int)])
      (Fun LeF []));
showsl_IA_exp (Fun LeF [v]) =
  Show_Literal_Polynomial.showsl_poly (iA_exp_to_poly (Fun LeF [v]));
showsl_IA_exp (Fun LeF (v : vc : ve : vf)) =
  Show_Literal_Polynomial.showsl_poly
    (iA_exp_to_poly (Fun LeF (v : vc : ve : vf)));
showsl_IA_exp (Fun (SumF vb) va) =
  Show_Literal_Polynomial.showsl_poly (iA_exp_to_poly (Fun (SumF vb) va));
showsl_IA_exp (Fun (ConstF vb) va) =
  Show_Literal_Polynomial.showsl_poly (iA_exp_to_poly (Fun (ConstF vb) va));
showsl_IA_exp (Fun (ProdF vb) va) =
  Show_Literal_Polynomial.showsl_poly (iA_exp_to_poly (Fun (ProdF vb) va));
showsl_IA_exp (Fun EqF []) =
  (Show_Literal_Polynomial.showsl_poly ::
    [(Polynomials.Monom a, Arith.Int)] -> String -> String)
    ((iA_exp_to_poly :: Term Sig (a, Ty) -> [(Polynomials.Monom a, Arith.Int)])
      (Fun EqF []));
showsl_IA_exp (Fun EqF [v]) =
  Show_Literal_Polynomial.showsl_poly (iA_exp_to_poly (Fun EqF [v]));
showsl_IA_exp (Fun EqF (v : vc : ve : vf)) =
  Show_Literal_Polynomial.showsl_poly
    (iA_exp_to_poly (Fun EqF (v : vc : ve : vf)));
showsl_IA_exp (Fun v []) =
  (Show_Literal_Polynomial.showsl_poly ::
    [(Polynomials.Monom a, Arith.Int)] -> String -> String)
    ((iA_exp_to_poly :: Term Sig (a, Ty) -> [(Polynomials.Monom a, Arith.Int)])
      (Fun v []));
showsl_IA_exp (Fun v [vb]) =
  Show_Literal_Polynomial.showsl_poly (iA_exp_to_poly (Fun v [vb]));
showsl_IA_exp (Fun v (vb : vd : vf : vg)) =
  Show_Literal_Polynomial.showsl_poly
    (iA_exp_to_poly (Fun v (vb : vd : vf : vg)));

def_checker ::
  forall a.
    (Eq a, Quasi_Order.Linorder a,
      Shows_Literal.Showl a) => a -> Ty -> Formula (Term Sig (a, Ty)) ->
     Sum_Type.Sum (String -> String) ();
def_checker x ty phi =
  Error_Monad.catch_error
    (case phi of {
      Atom _ -> def_checker_eq x ty phi;
      NegAtom _ -> def_checker_eq x ty phi;
      Conjunction [] -> Sum_Type.Inr ();
      Conjunction [eq] -> def_checker_eq x ty eq;
      Conjunction [Atom (Var _), _] ->
        Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 1st literal");
      Conjunction [Atom (Fun LessF _), _] ->
        Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 1st literal");
      Conjunction [Atom (Fun LeF []), _] ->
        Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 1st literal");
      Conjunction [Atom (Fun LeF [_]), _] ->
        Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 1st literal");
      Conjunction [Atom (Fun LeF [l1, r1]), lt2] ->
        (case lt2 of {
          Atom (Var _) ->
            Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 2nd literal");
          Atom (Fun LessF _) ->
            Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 2nd literal");
          Atom (Fun LeF []) ->
            Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 2nd literal");
          Atom (Fun LeF [_]) ->
            Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 2nd literal");
          Atom (Fun LeF [l2, r2]) ->
            Check_Monad.check
              (def_checker_main x ty l1 r1 l2 r2 ||
                def_checker_main x ty l2 r2 l1 r1)
              (Shows_Literal.showsl_lit "Non-equation not supported");
          Atom (Fun LeF (_ : _ : _ : _)) ->
            Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 2nd literal");
          Atom (Fun (SumF _) _) ->
            Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 2nd literal");
          Atom (Fun (ConstF _) _) ->
            Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 2nd literal");
          Atom (Fun (ProdF _) _) ->
            Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 2nd literal");
          Atom (Fun EqF _) ->
            Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 2nd literal");
          NegAtom _ ->
            Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 2nd clause");
          Conjunction _ ->
            Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 2nd clause");
          Disjunction _ ->
            Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 2nd clause");
        });
      Conjunction [Atom (Fun LeF (_ : _ : _ : _)), _] ->
        Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 1st literal");
      Conjunction [Atom (Fun (SumF _) _), _] ->
        Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 1st literal");
      Conjunction [Atom (Fun (ConstF _) _), _] ->
        Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 1st literal");
      Conjunction [Atom (Fun (ProdF _) _), _] ->
        Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 1st literal");
      Conjunction [Atom (Fun EqF _), _] ->
        Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 1st literal");
      Conjunction [NegAtom _, _] ->
        Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 1st clause");
      Conjunction [Conjunction _, _] ->
        Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 1st clause");
      Conjunction [Disjunction _, _] ->
        Sum_Type.Inl (Shows_Literal.showsl_lit "Invalid 1st clause");
      Conjunction (_ : _ : _ : _) ->
        Sum_Type.Inl (Shows_Literal.showsl_lit "Conjunction of more than two");
      Disjunction _ -> def_checker_eq x ty phi;
    })
    (\ xa ->
      Sum_Type.Inl
        (((((Shows_Literal.showsl_lit "error in definibility checker for " .
              Shows_Literal.showsl x) .
             Shows_Literal.showsl_lit " on formula\n  ") .
            showsl_formula showsl_IA_exp phi) .
           Shows_Literal.showsl_literal "\n") .
          xa));

rel_impl_co_rewrite_pair ::
  forall a b. Rel_impl_ext a b () -> Sum_Type.Sum (String -> String) ();
rel_impl_co_rewrite_pair ri =
  Error_Monad.catch_error
    (Error_Monad.bind (valid ri)
      (\ _ ->
        Error_Monad.bind
          (Error_Monad.catch_error (co_rewr ri)
            (\ x ->
              Sum_Type.Inl
                (x . Shows_Literal.showsl_lit
                       "\nproblem in ensuring disjointness property")))
          (\ _ ->
            Error_Monad.catch_error (subst_s ri)
              (\ x ->
                Sum_Type.Inl
                  (x . Shows_Literal.showsl_lit
                         "\nproblem in ensuring stability of strict relation")))))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit "problem with being a co-rewrite pair\n" .
          x));

rel_impl_mono_ce_redpair ::
  forall a b.
    Rel_impl_ext a b () ->
      [(Term a b, Term a b)] ->
        [(Term a b, Term a b)] -> Sum_Type.Sum (String -> String) ();
rel_impl_mono_ce_redpair ri s ns =
  Error_Monad.catch_error
    (Error_Monad.bind (valid ri)
      (\ _ ->
        Error_Monad.bind (standard ri)
          (\ _ ->
            Error_Monad.bind
              (Error_Monad.catch_error (sn ri)
                (\ x ->
                  Sum_Type.Inl
                    (x . Shows_Literal.showsl_lit
                           "\nproblem in ensuring strong normalization of relation")))
              (\ _ ->
                Error_Monad.bind
                  (Error_Monad.catch_error (subst_s ri)
                    (\ x ->
                      Sum_Type.Inl
                        (x . Shows_Literal.showsl_lit
                               "\nproblem in ensuring stability of strict relation")))
                  (\ _ ->
                    Error_Monad.bind
                      (Error_Monad.catch_error (ce_compat ri)
                        (\ x ->
                          Sum_Type.Inl
                            (x . Shows_Literal.showsl_lit
                                   "\nproblem in ensuring ce-compatibility")))
                      (\ _ ->
                        Error_Monad.catch_error
                          (mono ri (funas_trs_list (s ++ ns)))
                          (\ x ->
                            Sum_Type.Inl
                              (x . Shows_Literal.showsl_lit
                                     "\nproblem in ensuring monotonicity of strict relation"))))))))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "problem with being a ce-compatible monotone reduction pair\n" .
          x));

memo_rtrancl ::
  forall a.
    (Arith.Ceq a, Arith.Ccompare a, Eq a,
      Arith.Set_impl a) => Arith.Set (a, a) -> a -> Arith.Set a;
memo_rtrancl (Arith.Set_Monad xs) =
  Tree_Automata_Det_Container.memo_list_rtrancl_set xs;
memo_rtrancl (Arith.DList_set dxs) =
  (case (Arith.ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "memo_rtrancl DList_set: ceq = None"
        (\ _ -> memo_rtrancl (Arith.DList_set dxs));
    Just _ ->
      Tree_Automata_Det_Container.memo_list_rtrancl_set
        (Arith.list_of_dlist dxs);
  });
memo_rtrancl (Arith.RBT_set rbt) =
  (case (Arith.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "memo_rtrancl RBT_set: ccompare = None"
        (\ _ -> memo_rtrancl (Arith.RBT_set rbt));
    Just _ ->
      Tree_Automata_Det_Container.memo_list_rtrancl_set (Arith.keysa rbt);
  });

ta_idx_rhs_init_code ::
  forall a b c.
    (Compare.Compare a, Compare.Compare b,
      Compare.Compare c) => Bool ->
                              Arith.Rbt (Ta_rule a b) () ->
                                (a -> Arith.Rbt c ()) ->
                                  (Arith.Rbt (b, Arith.Nat)
                                     (Arith.Rbt ([a], a) ()),
                                    (Bool, Arith.Rbt c ()));
ta_idx_rhs_init_code det rs efcl =
  (SetIteratorOperations.map_iterator_dom . RBT_add.rm_iterateoi) rs
    (\ _ -> True)
    (\ x (a, (aa, ba)) ->
      (case x of {
        TA_rule xg xh xi ->
          let {
            y = Arith.size_list xh;
          } in (case Arith.rbt_comp_lookup Arith.compare_prod a (xg, y) of {
                 Nothing ->
                   (Arith.rbt_comp_insert Arith.compare_prod (xg, y)
                      (Arith.rbt_comp_insert Arith.compare_prod (xh, xi) ()
                        Arith.Empty)
                      a,
                     (aa, Arith.rbt_comp_union_with_key Compare.compare
                            (\ _ _ rv -> rv) (efcl xi) ba));
                 Just xj ->
                   (Arith.rbt_comp_insert Arith.compare_prod (xg, y)
                      (Arith.rbt_comp_insert Arith.compare_prod (xh, xi) () xj)
                      a,
                     ((if aa
                        then Gen_Set.gen_ball
                               (SetIteratorOperations.map_iterator_dom .
                                 RBT_add.rm_iterateoi)
                               xj (\ (xk, _) ->
                                    not (Autoref_Bindings_HOL.list_eq
  (Intf_Comp.comp2eq compare_res) xh xk))
                        else False),
                       Arith.rbt_comp_union_with_key Compare.compare
                         (\ _ _ rv -> rv) (efcl xi) ba));
               });
      }))
    (Arith.Empty, (det, Arith.Empty));

ta_make_code ::
  forall a b c.
    (Compare.Compare a, Compare.Compare_order b,
      Compare.Compare c) => Arith.Rbt a () ->
                              Arith.Rbt (Ta_rule b c) () ->
                                [(b, b)] ->
                                  (Arith.Rbt a (),
                                    (Arith.Rbt (Ta_rule b c) (),
                                      ([(b, b)],
(Arith.Rbt b (),
  (Arith.Rbt (c, Arith.Nat) (Arith.Rbt ([b], b) ()),
    (Bool, (b -> Arith.Rbt b (), b -> Arith.Rbt b ())))))));
ta_make_code f r e =
  (case ta_idx_rhs_init_code (Autoref_Bindings_HOL.is_Nil e) r
          (\ xi ->
            RBT.impl_of (Transitive_Closure_RBT_Impl.memo_rbt_rtrancl e xi))
    of {
    (a, (aa, ba)) ->
      (f, (r, (e, (ba, (a, (aa, ((\ s ->
                                   RBT.impl_of
                                     (Transitive_Closure_RBT_Impl.memo_rbt_rtrancl
                                       e s)),
                                  (\ s ->
                                    RBT.impl_of
                                      (Transitive_Closure_RBT_Impl.memo_rbt_rtrancl
(Gen_Set.gen_image Foldi.foldli []
  (Impl_List_Set.glist_insert
    (Autoref_Bindings_HOL.prod_eq (Intf_Comp.comp2eq compare_res)
      (Intf_Comp.comp2eq compare_res)))
  (\ xc -> (snd xc, fst xc)) e)
s)))))))));
  });

showsl_formulaa ::
  forall a. (Shows_Literal.Showl a) => Formula a -> String -> String;
showsl_formulaa (Atom a) = Shows_Literal.showsl a;
showsl_formulaa (NegAtom a) =
  (Shows_Literal.showsl_lit "! (" . Shows_Literal.showsl a) .
    Shows_Literal.showsl_lit ")";
showsl_formulaa (Conjunction a) =
  Shows_Literal.showsl_list_gen id "TRUE" "(" " & " ")" (map showsl_formulaa a);
showsl_formulaa (Disjunction a) =
  Shows_Literal.showsl_list_gen id "FALSE" "(" " | " ")"
    (map showsl_formulaa a);

ta_final_impl ::
  forall a b c d e f g h. (a, (b, (c, (d, (e, (f, (g, h))))))) -> a;
ta_final_impl (f, (r, (e, (rhs, (idx, (det, (efcl, eicl))))))) = f;

ta_rules_impl ::
  forall a b c d e f g h. (a, (b, (c, (d, (e, (f, (g, h))))))) -> b;
ta_rules_impl (f, (r, (e, (rhs, (idx, (det, (efcl, eicl))))))) = r;

ta_eps_cl_impl ::
  forall a b c d e f g h i. (a, (b, (c, (d, (e, (f, (g -> h, i))))))) -> g -> h;
ta_eps_cl_impl (f, (r, (e, (rhs, (idx, (det, (efcl, eicl))))))) q = efcl q;

ta_eps_icl_impl ::
  forall a b c d e f g h i. (a, (b, (c, (d, (e, (f, (g, h -> i))))))) -> h -> i;
ta_eps_icl_impl (f, (r, (e, (rhs, (idx, (det, (efcl, eicl))))))) q = eicl q;

subst_apply_term :: forall a b c. Term a b -> (b -> Term a c) -> Term a c;
subst_apply_term = eval_term Fun;

check_valid_formula ::
  forall a b c d.
    (Eq a, Eq b, Shows_Literal.Showl b, Eq c, HOL.Default d,
      Shows_Literal.Showl d) => (Term a (b, c) -> String -> String) ->
                                  (d -> Formula (Term a (b, c)) ->
  Sum_Type.Sum (String -> String) ()) ->
                                    (Bool ->
                                      Term a (b, c) ->
Formula (Term a (b, c))) ->
                                      d ->
Formula (Term a (b, c)) -> Sum_Type.Sum (String -> String) ();
check_valid_formula showsl_atom logic_checker normalize_lit h phi =
  Error_Monad.catch_error
    (case flatten phi of {
      Conjunction phi_s ->
        Error_Monad.catch_error
          (Error_Monad.forallM
            (\ phia ->
              Error_Monad.catch_error
                (Check_Monad.check (trivial_clause_checker phia)
                  "trivial clause checker failed")
                (\ _ ->
                  (case flatten (normalize_lits normalize_lit phia) of {
                    Conjunction phi_sa ->
                      Error_Monad.catch_error
                        (Error_Monad.forallM (logic_checker h) phi_sa)
                        (\ x -> Sum_Type.Inl (snd x));
                  })))
            phi_s)
          (\ x -> Sum_Type.Inl (snd x));
    })
    (\ x ->
      Sum_Type.Inl
        (((Shows_Literal.showsl_lit "problem in checking validity of formula " .
            showsl_formula showsl_atom phi) .
           Shows_Literal.showsl_literal "\n") .
          x));

ta_rhs_states_impl ::
  forall a b c d e f g h. (a, (b, (c, (d, (e, (f, (g, h))))))) -> d;
ta_rhs_states_impl (f, (r, (e, (rhs, (idx, (det, (efcl, eicl))))))) = rhs;

rel_impl_co_discrimination_pair ::
  forall a b. Rel_impl_ext a b () -> Sum_Type.Sum (String -> String) ();
rel_impl_co_discrimination_pair ri =
  Error_Monad.catch_error
    (Error_Monad.bind (valid ri)
      (\ _ ->
        Error_Monad.catch_error (co_rewr ri)
          (\ x ->
            Sum_Type.Inl
              (x . Shows_Literal.showsl_lit
                     "\nproblem in ensuring disjointness property"))))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "problem with being a co-discrimination pair\n" .
          x));

rel_impl_quasi_reduction_triple ::
  forall a b. Rel_impl_ext a b () -> Sum_Type.Sum (String -> String) ();
rel_impl_quasi_reduction_triple ri =
  Error_Monad.catch_error
    (Error_Monad.bind (valid ri)
      (\ _ ->
        Error_Monad.bind
          (Error_Monad.catch_error (subst_s ri)
            (\ x ->
              Sum_Type.Inl
                (x . Shows_Literal.showsl_lit
                       "\nproblem in ensuring stability of strict relation")))
          (\ _ ->
            Error_Monad.bind
              (Error_Monad.catch_error (sn ri)
                (\ x ->
                  Sum_Type.Inl
                    (x . Shows_Literal.showsl_lit
                           "\nproblem in ensuring strong normalization of strict relation")))
              (\ _ ->
                Error_Monad.bind
                  (Error_Monad.catch_error (top_mono ri)
                    (\ x ->
                      Sum_Type.Inl
                        (x . Shows_Literal.showsl_lit
                               "\nproblem in ensuring top-monotonicity of non-strict relations")))
                  (\ _ ->
                    Error_Monad.catch_error (top_refl ri)
                      (\ x ->
                        Sum_Type.Inl
                          (x . Shows_Literal.showsl_lit
                                 "\nproblem in ensuring top-reflexivity")))))))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "problem with being a quasi-reduction triple\n" .
          x));

union_image_rs_code ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => Arith.Rbt a () ->
                              (a -> Arith.Rbt b ()) -> Arith.Rbt b ();
union_image_rs_code s f =
  (SetIteratorOperations.map_iterator_dom . RBT_add.rm_iterateoi) s
    (\ _ -> True)
    (\ x ->
      Arith.rbt_comp_union_with_key Compare.compare (\ _ _ rv -> rv) (f x))
    Arith.Empty;

showsl_gctxt ::
  forall a b. (Shows_Literal.Showl a) => Gctxt a b -> String -> String;
showsl_gctxt GCHole = Shows_Literal.showsl_literal "_";
showsl_gctxt (GCFun f ts) =
  Shows_Literal.showsl f .
    Shows_Literal.showsl_list_gen id "" "(" ", " ")" (map showsl_gctxt ts);

showsl_poly_constraint ::
  forall a.
    (Eq a, Quasi_Order.Linorder a,
      Shows_Literal.Showl a) => Poly_constraint a -> String -> String;
showsl_poly_constraint (Poly_Ge p) =
  Show_Literal_Polynomial.showsl_poly p . Shows_Literal.showsl_lit " >= 0";
showsl_poly_constraint (Poly_Eq p) =
  Show_Literal_Polynomial.showsl_poly p . Shows_Literal.showsl_lit " = 0";

showsl_mctxt ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => Mctxt a b -> String -> String;
showsl_mctxt MHole = Shows_Literal.showsl_lit "[]";
showsl_mctxt (MVar x) = Shows_Literal.showsl x;
showsl_mctxt (MFun f cs) =
  Shows_Literal.showsl f .
    Shows_Literal.showsl_list_gen id "" "(" ", " ")" (map showsl_mctxt cs);

iA_exp_to_poly_constraint ::
  forall a.
    (Eq a, Quasi_Order.Linorder a) => Term Sig (a, Ty) -> Poly_constraint a;
iA_exp_to_poly_constraint (Fun LeF [a, b]) =
  Poly_Ge (Polynomials.poly_minus (iA_exp_to_poly b) (iA_exp_to_poly a));
iA_exp_to_poly_constraint (Fun EqF [a, b]) =
  Poly_Eq (Polynomials.poly_minus (iA_exp_to_poly b) (iA_exp_to_poly a));
iA_exp_to_poly_constraint (Fun LessF [a, b]) =
  Poly_Ge
    (Polynomials.poly_minus
      (Polynomials.poly_minus (iA_exp_to_poly b) (iA_exp_to_poly a))
      Polynomials.one_poly);

interpret_poly_constraint ::
  forall a.
    (Quasi_Order.Linorder a) => (a -> Arith.Int) -> Poly_constraint a -> Bool;
interpret_poly_constraint f (Poly_Ge p) =
  Arith.less_eq_int Arith.zero_int (Polynomials.eval_poly f p);
interpret_poly_constraint f (Poly_Eq p) =
  Arith.equal_int (Polynomials.eval_poly f p) Arith.zero_int;

vars_poly_constraint_list ::
  forall a. (Eq a, Quasi_Order.Linorder a) => Poly_constraint a -> [a];
vars_poly_constraint_list (Poly_Ge p) = Polynomials.poly_vars_list p;
vars_poly_constraint_list (Poly_Eq p) = Polynomials.poly_vars_list p;

check_skip_transition ::
  forall a b c d e.
    (Eq a, Eq b, Shows_Literal.Showl b, Eq c, HOL.Default d,
      Shows_Literal.Showl d) => (Term a (b, c) -> String -> String) ->
                                  (d -> Formula (Term a (b, c)) ->
  Sum_Type.Sum (String -> String) ()) ->
                                    (Bool ->
                                      Term a (b, c) ->
Formula (Term a (b, c))) ->
                                      Transition_rule a b c e ->
Sum_Type.Sum (String -> String) ();
check_skip_transition showsl_atom logic_checker normalize_lit tau =
  (case tau of {
    Transition _ _ phi ->
      check_valid_formula showsl_atom logic_checker normalize_lit HOL.defaulta
        (map_formula (rename_vars_exp untrans_var) phi);
  });

}
