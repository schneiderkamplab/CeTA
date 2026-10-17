theory Relative_ADP_Checker_Adapter
  imports
    Dependency_Pair_Injective_Renaming
    Relative_ADP_Com_Reduction_Pair_Dev.Relative_ADP_Com_Reduction_Pair
    Proof_Checker_Base.Check_Termination
    Framework.Termination_Problem_Impl
    Framework.Dependency_Pair_Problem_Impl
    Ord.Reduction_Pair_Implementations
    Auxx.Map_Choice
    Containers.Containers
begin

derive compare_order adp_symbol
derive countable adp_symbol
derive (eq) ceq adp_symbol
derive ccompare adp_symbol
derive (rbt) set_impl adp_symbol
derive compare_order adp_com_symbol
derive countable adp_com_symbol
derive (eq) ceq adp_com_symbol
derive ccompare adp_com_symbol
derive (rbt) set_impl adp_com_symbol

instantiation adp_symbol :: (showl) showl
begin
fun showsl_adp_symbol where
  "showsl_adp_symbol (Plain f) = showsl f"
| "showsl_adp_symbol (adp_symbol.Sharp f) =
    (showsl f \<circ> showsl_lit (STR ''#''))"
definition "showsl_list (xs :: 'a adp_symbol list) =
  default_showsl_list showsl xs"
instance by standard
end

instantiation adp_com_symbol :: (showl) showl
begin
fun showsl_adp_com_symbol where
  "showsl_adp_com_symbol (ADP_Symbol f) = showsl f"
| "showsl_adp_com_symbol Com0 = showsl_lit (STR ''Com0'')"
| "showsl_adp_com_symbol Com2 = showsl_lit (STR ''Com2'')"
definition "showsl_list (xs :: 'a adp_com_symbol list) =
  default_showsl_list showsl xs"
instance by standard
end

type_synonym ('f, 'v) relative_adp_problem_list =
  "('f, 'v) adp list \<times> ('f, 'v) adp list"

definition adp_defined_symbols_list ::
  "('f, 'v) rules \<Rightarrow> 'f list" where
  "adp_defined_symbols_list R = remdups (List.map_filter
    (\<lambda>(l,r). case Term.root l of
      None \<Rightarrow> None | Some (f,n) \<Rightarrow> Some f) R)"

definition adp_defined_positions_list ::
  "'f list \<Rightarrow> ('f, 'v) term \<Rightarrow> pos list" where
  "adp_defined_positions_list D t = filter
    (\<lambda>p. case Term.root (t |_ p) of
      None \<Rightarrow> False | Some (f,n) \<Rightarrow> f \<in> set D)
    (poss_list t)"

definition canonical_adps_list ::
  "nat \<Rightarrow> 'f list \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) adp list" where
  "canonical_adps_list n D R = concat (map (\<lambda>(l,r).
    let ps = adp_defined_positions_list D r
    in map (\<lambda>A. (plain_adp_term l, annotate_term (set A) r))
      (rev (filter (\<lambda>A. length (remdups A) =
        min n (length (remdups ps))) (subseqs ps)))) R)"

lemma adp_defined_symbols_list_sound:
  "set (adp_defined_symbols_list R) = adp_defined_symbols (set R)"
proof (induction R)
  case Nil
  then show ?case
    by (simp add: adp_defined_symbols_list_def adp_defined_symbols_def)
next
  case (Cons rule R)
  obtain l r where rule: "rule = (l,r)" by (cases rule)
  show ?case
    using Cons.IH
    by (cases l) (auto simp: rule adp_defined_symbols_list_def
        adp_defined_symbols_def)
qed

lemma adp_defined_positions_list_sound:
  "set (adp_defined_positions_list D t) =
    adp_defined_positions (set D) t"
proof
  show "set (adp_defined_positions_list D t) \<subseteq>
      adp_defined_positions (set D) t"
  proof
    fix p
    assume "p \<in> set (adp_defined_positions_list D t)"
    then show "p \<in> adp_defined_positions (set D) t"
      unfolding adp_defined_positions_list_def adp_defined_positions_def
      by (cases "t |_ p") (auto simp: poss_list_sound)
  qed
  show "adp_defined_positions (set D) t \<subseteq>
      set (adp_defined_positions_list D t)"
  proof
    fix p
    assume "p \<in> adp_defined_positions (set D) t"
    then show "p \<in> set (adp_defined_positions_list D t)"
      unfolding adp_defined_positions_list_def adp_defined_positions_def
      by (auto simp: poss_list_sound)
  qed
qed

lemma canonical_adps_list_sound:
  "set (canonical_adps_list n D R) =
    canonical_adps n (set D) (set R)"
proof
  show "set (canonical_adps_list n D R) \<subseteq>
      canonical_adps n (set D) (set R)"
  proof
    fix p
    assume "p \<in> set (canonical_adps_list n D R)"
    then obtain l r A where rule: "(l,r) \<in> set R"
      and subseq: "subseq A (adp_defined_positions_list D r)"
      and size: "length (remdups A) = min n
        (length (remdups (adp_defined_positions_list D r)))"
      and p: "p = (plain_adp_term l, annotate_term (set A) r)"
      unfolding canonical_adps_list_def
      by (auto simp: Let_def split: prod.splits)
    have subset: "set A \<subseteq> adp_defined_positions (set D) r"
      using subseq
      by (metis adp_defined_positions_list_sound subseq_subset)
    have A_card: "length (remdups A) = card (set A)"
      by (rule length_remdups_card_conv)
    have positions_card:
        "length (remdups (adp_defined_positions_list D r)) =
          card (adp_defined_positions (set D) r)"
      by (simp add: length_remdups_card_conv
          adp_defined_positions_list_sound)
    have card: "card (set A) =
        min n (card (adp_defined_positions (set D) r))"
      using size A_card positions_card by simp
    show "p \<in> canonical_adps n (set D) (set R)"
      unfolding canonical_adps_def
      using p rule subset card by blast
  qed
  show "canonical_adps n (set D) (set R) \<subseteq>
      set (canonical_adps_list n D R)"
  proof
    fix p
    assume "p \<in> canonical_adps n (set D) (set R)"
    then obtain l r A where p:
        "p = (plain_adp_term l, annotate_term A r)"
      and rule: "(l,r) \<in> set R"
      and subset: "A \<subseteq> adp_defined_positions (set D) r"
      and card: "card A = min n (card (adp_defined_positions (set D) r))"
      unfolding canonical_adps_def by blast
    have positions_eq:
        "set (adp_defined_positions_list D r) =
          adp_defined_positions (set D) r"
      by (rule adp_defined_positions_list_sound)
    have A_pow:
        "A \<in> Pow (set (adp_defined_positions_list D r))"
      using subset positions_eq by simp
    have subseqs_eq:
        "set ` set (subseqs (adp_defined_positions_list D r)) =
          Pow (set (adp_defined_positions_list D r))"
      by (rule subseqs_powset)
    have A_image:
        "A \<in> set ` set (subseqs (adp_defined_positions_list D r))"
      using A_pow subseqs_eq by simp
    from A_image
    obtain As where As:
        "As \<in> set (subseqs (adp_defined_positions_list D r))"
        "set As = A"
      by auto
    show "p \<in> set (canonical_adps_list n D R)"
      unfolding canonical_adps_list_def
      using rule As card p
      by (auto simp: adp_defined_positions_list_sound
          length_remdups_card_conv split: prod.splits)
  qed
qed

definition canonical_relative_adp_problem_list ::
  "('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow>
   ('f, 'v) relative_adp_problem_list" where
  "canonical_relative_adp_problem_list R B = (let
      D = adp_defined_symbols_list (R @ B)
    in (canonical_adps_list 1 D R, canonical_adps_list 2 D B))"

lemma canonical_relative_adp_problem_list_sound:
  "case canonical_relative_adp_problem_list R B of (P,S) \<Rightarrow>
      (set P, set S) = canonical_relative_adp_problem (set R) (set B)"
proof -
  let ?D = "adp_defined_symbols_list (R @ B)"
  have D: "set ?D = adp_defined_symbols (set R \<union> set B)"
    using adp_defined_symbols_list_sound[of "R @ B"] by simp
  have main: "set (canonical_adps_list 1 ?D R) =
      canonical_adps 1 (adp_defined_symbols (set R \<union> set B)) (set R)"
    using canonical_adps_list_sound[of 1 ?D R] D by simp
  have base: "set (canonical_adps_list 2 ?D B) =
      canonical_adps 2 (adp_defined_symbols (set R \<union> set B)) (set B)"
    using canonical_adps_list_sound[of 2 ?D B] D by simp
  show ?thesis
    unfolding canonical_relative_adp_problem_list_def
      canonical_relative_adp_problem_def Let_def
    using main base by simp
qed

definition erase_annotations_adp_list ::
  "('f, 'v) adp list \<Rightarrow> ('f, 'v) adp list" where
  "erase_annotations_adp_list = map erase_annotations_adp"

definition relative_adp_erasure_residual ::
  "('f, 'v) adp list \<Rightarrow> ('f, 'v) adp list \<Rightarrow>
   ('f, 'v) adp list \<Rightarrow> ('f, 'v) relative_adp_problem_list" where
  "relative_adp_erasure_residual P B selected =
    (list_diff P selected, remdups
      (erase_annotations_adp_list (filter (\<lambda>p. p \<in> set selected) P) @
       map (\<lambda>p. if p \<in> set selected
         then erase_annotations_adp p else p) B))"

definition check_relative_adp_erasure_redpair ::
  "('f::{compare_order,showl}) redtriple_impl \<Rightarrow>
   ('f, string) adp list \<Rightarrow> ('f, string) adp list \<Rightarrow>
   ('f, string) adp list \<Rightarrow> showsl check" where
  "check_relative_adp_erasure_redpair redp P B selected = (let
      rp = get_rel_impl redp;
      strict = map erase_adp selected;
      weak = map erase_adp (P @ B)
    in do {
      check (set selected \<subseteq> set P \<union> set B)
        (showsl_lit (STR ''selected relative ADPs are not in the problem''));
      check (selected \<noteq> [])
        (showsl_lit (STR ''relative ADP reduction pair removes no ADP''));
      rel_impl_mono_redpair rp strict weak;
      rel_impl_s rp strict;
      rel_impl_ns rp weak
    })"

lemma relative_adp_erasure_residual_sets:
  assumes "set selected \<subseteq> set P \<union> set B"
  shows "case relative_adp_erasure_residual P B selected of (P',B') \<Rightarrow>
    (set P', set B') =
      (set P - set selected,
       (set B - set selected) \<union> erase_annotations_adp ` set selected)"
  using assms
  by (auto simp: relative_adp_erasure_residual_def
      erase_annotations_adp_list_def split: if_splits)

theorem check_relative_adp_erasure_redpair_sound:
  fixes redp :: "('f::{compare_order,showl}) redtriple_impl"
  assumes checked:
      "isOK (check_relative_adp_erasure_redpair redp P B selected)"
    and residual:
      "adp_problem_SN
        (case relative_adp_erasure_residual P B selected of
          (P',B') \<Rightarrow> (set P', set B'))"
  shows "adp_problem_SN (set P, set B)"
proof -
  let ?rp = "get_rel_impl redp"
  let ?strict = "map erase_adp selected"
  let ?weak = "map erase_adp (P @ B)"
  from checked[unfolded check_relative_adp_erasure_redpair_def,
      simplified Let_def]
  have selected: "set selected \<subseteq> set P \<union> set B"
    and valid: "isOK (rel_impl_mono_redpair ?rp ?strict ?weak)"
    and strict: "isOK (rel_impl_s ?rp ?strict)"
    and weak: "isOK (rel_impl_ns ?rp ?weak)"
    by auto
  from rel_impl_mono_redpair[OF get_rel_impl valid strict weak,
      of undefined undefined]
  obtain S NS NST where order: "mono_redtriple_order S NS NST"
    and strict: "set ?strict \<subseteq> S"
    and weak: "set ?weak \<subseteq> NS"
    by auto
  have all_weak: "erase_adp ` (set P \<union> set B) \<subseteq> NS"
    using weak by auto
  have selected_strict: "erase_adp ` set selected \<subseteq> S"
    using strict by auto
  have residual': "adp_problem_SN
      (set P - set selected,
       (set B - set selected) \<union> erase_annotations_adp ` set selected)"
    using residual relative_adp_erasure_residual_sets[OF selected]
    by (cases "relative_adp_erasure_residual P B selected") simp
  show ?thesis
    by (rule relative_adp_erasure_reduction_pair[
          OF order all_weak selected_strict residual'])
qed

definition relative_adp_com_constraints_list where
  "relative_adp_com_constraints_list A = map
    (\<lambda>pair. (relative_adp_com_lhs pair,
      relative_adp_annotation_summary pair)) A"

definition relative_adp_com_flat_rules_list where
  "relative_adp_com_flat_rules_list A = map relative_adp_com_flat_rule A"

definition relative_adp_com_law_rules ::
  "('f adp_com_symbol, string) rules" where
  "relative_adp_com_law_rules = (let
      x = Var ''__com_x'';
      y = Var ''__com_y'';
      z = Var ''__com_z'';
      c = (\<lambda>a b. Fun Com2 [a,b])
    in [
      (c x y, c y x),
      (c y x, c x y),
      (c x (c y z), c (c x y) z),
      (c (c x y) z, c x (c y z)),
      (c x y, x),
      (c x y, y),
      (x, Fun Com0 [])
    ])"

definition check_relative_adp_com_redpair ::
  "(('f::{compare_order,showl}) adp_com_symbol) redtriple_impl \<Rightarrow>
   ('f, string) adp list \<Rightarrow> ('f, string) adp list \<Rightarrow>
   ('f, string) adp list \<Rightarrow> showsl check" where
  "check_relative_adp_com_redpair redp P B selected = (let
      rp = get_rel_impl redp;
      strict = relative_adp_com_constraints_list selected;
      weak = relative_adp_com_flat_rules_list (P @ B) @
        relative_adp_com_constraints_list (P @ B) @
        relative_adp_com_law_rules
    in do {
      check (set selected \<subseteq> set P \<union> set B)
        (showsl_lit (STR ''selected relative ADPs are not in the problem''));
      check (selected \<noteq> [])
        (showsl_lit (STR ''relative ADP Com reduction pair removes no ADP''));
      check_all (\<lambda>pair. is_Fun (fst pair)) (P @ B)
        <+? (\<lambda>pair. showsl_lit
          (STR ''relative ADP Com requires function-rooted left-hand sides''));
      rel_impl_mono_redpair rp strict weak;
      rel_impl_s rp strict;
      rel_impl_ns rp weak
    })"

lemma relative_adp_com_constraints_list_set:
  "set (relative_adp_com_constraints_list A) =
    (\<lambda>pair. (relative_adp_com_lhs pair,
      relative_adp_annotation_summary pair)) ` set A"
  unfolding relative_adp_com_constraints_list_def by simp

lemma relative_adp_com_flat_rules_list_set:
  "set (relative_adp_com_flat_rules_list A) =
    relative_adp_com_flat_rule ` set A"
  unfolding relative_adp_com_flat_rules_list_def by simp

lemma relative_adp_com_laws_sound:
  fixes NS :: "((('f adp_com_symbol, string) term) \<times>
    (('f adp_com_symbol, string) term)) set"
  assumes laws: "set relative_adp_com_law_rules \<subseteq> NS"
    and stable: "subst.closed NS"
  shows "adp_com_invariant NS" "adp_com_discarding NS"
proof -
  let ?x = "Var ''__com_x''"
  let ?y = "Var ''__com_y''"
  let ?z = "Var ''__com_z''"
  let ?c = "\<lambda>a b. Fun Com2 [a,b]"
  have schemas:
      "(?c ?x ?y, ?c ?y ?x) \<in> NS"
      "(?c ?y ?x, ?c ?x ?y) \<in> NS"
      "(?c ?x (?c ?y ?z), ?c (?c ?x ?y) ?z) \<in> NS"
      "(?c (?c ?x ?y) ?z, ?c ?x (?c ?y ?z)) \<in> NS"
      "(?c ?x ?y, ?x) \<in> NS" "(?c ?x ?y, ?y) \<in> NS"
      "(?x, Fun Com0 []) \<in> NS"
    using laws unfolding relative_adp_com_law_rules_def Let_def by auto
  show "adp_com_invariant NS"
    unfolding adp_com_invariant_def
  proof (intro allI conjI)
    fix x y z :: "('f adp_com_symbol, string) term"
    let ?sigma = "Var(''__com_x'' := x,
      ''__com_y'' := y, ''__com_z'' := z)"
    show "(Fun Com2 [x,y], Fun Com2 [y,x]) \<in> NS"
      using subst.closedD[OF stable schemas(1), of ?sigma] by simp
    show "(Fun Com2 [y,x], Fun Com2 [x,y]) \<in> NS"
      using subst.closedD[OF stable schemas(2), of ?sigma] by simp
    show "(Fun Com2 [x, Fun Com2 [y,z]],
        Fun Com2 [Fun Com2 [x,y],z]) \<in> NS"
      using subst.closedD[OF stable schemas(3), of ?sigma] by simp
    show "(Fun Com2 [Fun Com2 [x,y],z],
        Fun Com2 [x, Fun Com2 [y,z]]) \<in> NS"
      using subst.closedD[OF stable schemas(4), of ?sigma] by simp
  qed
  show "adp_com_discarding NS"
    unfolding adp_com_discarding_def
  proof (intro allI conjI)
    fix x y :: "('f adp_com_symbol, string) term"
    let ?sigma = "Var(''__com_x'' := x, ''__com_y'' := y)"
    show "(Fun Com2 [x,y],x) \<in> NS"
      using subst.closedD[OF stable schemas(5), of ?sigma] by simp
    show "(Fun Com2 [x,y],y) \<in> NS"
      using subst.closedD[OF stable schemas(6), of ?sigma] by simp
    show "(x,Fun Com0 []) \<in> NS"
      using subst.closedD[OF stable schemas(7), of ?sigma] by simp
  qed
qed

theorem check_relative_adp_com_redpair_sound:
  fixes redp :: "(('f::{compare_order,showl}) adp_com_symbol) redtriple_impl"
  assumes checked: "isOK (check_relative_adp_com_redpair redp P B selected)"
    and residual: "adp_problem_SN
      (case relative_adp_erasure_residual P B selected of
        (P',B') \<Rightarrow> (set P',set B'))"
  shows "adp_problem_SN (set P,set B)"
proof -
  let ?rp = "get_rel_impl redp"
  let ?strict = "relative_adp_com_constraints_list selected"
  let ?weak = "relative_adp_com_flat_rules_list (P @ B) @
    relative_adp_com_constraints_list (P @ B) @
    relative_adp_com_law_rules"
  from checked[unfolded check_relative_adp_com_redpair_def,
      simplified Let_def]
  have selected: "set selected \<subseteq> set P \<union> set B"
    and lhs_fun: "\<And>pair. pair \<in> set P \<union> set B \<Longrightarrow>
      is_Fun (fst pair)"
    and valid: "isOK (rel_impl_mono_redpair ?rp ?strict ?weak)"
    and strict: "isOK (rel_impl_s ?rp ?strict)"
    and weak: "isOK (rel_impl_ns ?rp ?weak)"
    by (auto simp: isOK_check_allm)
  from rel_impl_mono_redpair[OF get_rel_impl valid strict weak,
      of undefined undefined]
  obtain S NS NST where order: "mono_redtriple_order S NS NST"
    and strict_set: "set ?strict \<subseteq> S"
    and weak_set: "set ?weak \<subseteq> NS" by auto
  have law_set: "set relative_adp_com_law_rules \<subseteq> NS"
    using weak_set by auto
  interpret mono_redtriple_order S NS NST by (rule order)
  have invariant: "adp_com_invariant NS"
    and discard: "adp_com_discarding NS"
    by (rule relative_adp_com_laws_sound[OF law_set subst_NS])+
  have flat_list_weak:
      "set (relative_adp_com_flat_rules_list (P @ B)) \<subseteq> NS"
    using weak_set by auto
  have constraint_list_weak:
      "set (relative_adp_com_constraints_list (P @ B)) \<subseteq> NS"
    using weak_set by auto
  have flat_weak: "relative_adp_com_flat_rule pair \<in> NS"
      if "pair \<in> set P \<union> set B" for pair
    using flat_list_weak that
    unfolding relative_adp_com_flat_rules_list_set by auto
  have com_weak: "(relative_adp_com_lhs pair,
      relative_adp_annotation_summary pair) \<in> NS"
    if "pair \<in> set P \<union> set B" for pair
    using constraint_list_weak that
    unfolding relative_adp_com_constraints_list_set by auto
  have selected_strict: "(relative_adp_com_lhs pair,
      relative_adp_annotation_summary pair) \<in> S"
    if "pair \<in> set selected" for pair
    using strict_set that unfolding relative_adp_com_constraints_list_set by auto
  have residual': "adp_problem_SN
      (set P - set selected,
       (set B - set selected) \<union> erase_annotations_adp ` set selected)"
    using residual relative_adp_erasure_residual_sets[OF selected]
    by (cases "relative_adp_erasure_residual P B selected") simp
  show ?thesis
    by (rule relative_adp_com_reduction_pair_finite[
        OF order invariant discard lhs_fun flat_weak com_weak
          selected_strict selected residual'])
qed

datatype 'f relative_adp_termination_proof =
    Relative_ADP_Empty
  | Relative_ADP_Erasure_Redpair
      "'f redtriple_impl"
      "nat list"
      "nat list"
      "'f relative_adp_termination_proof"
  | Relative_ADP_Com_Redpair
      "('f adp_com_symbol) redtriple_impl"
      "nat list"
      "nat list"
      "'f relative_adp_termination_proof"
  | Relative_ADP_Dependency_Graph
      "'f relative_adp_termination_proof list"
  | Relative_ADP_Derelatification
      "('f adp_symbol, nat list, string) dp_termination_proof"

definition relative_adps_at_indices ::
  "('f, 'v) adp list \<Rightarrow> ('f, 'v) adp list \<Rightarrow>
   nat list \<Rightarrow> nat list \<Rightarrow> ('f, 'v) adp list" where
  "relative_adps_at_indices P B main_indices base_indices =
    map (List.nth P) main_indices @ map (List.nth B) base_indices"

definition relative_adp_graph_child ::
  "('f, 'v) adp list \<Rightarrow> ('f, 'v) adp list \<Rightarrow>
   ('f, 'v) adp list \<Rightarrow> ('f, 'v) relative_adp_problem_list" where
  "relative_adp_graph_child P B Q = (let
      P' = filter (\<lambda>p. p \<in> set Q) P;
      B' = filter (\<lambda>p. p \<notin> set P')
        (remdups (Q @ map erase_annotations_adp
          (filter (\<lambda>p. p \<notin> set Q) (P @ B))))
    in (P',B'))"

lemma relative_adp_graph_child_sets:
  "case relative_adp_graph_child P B Q of (P',B') \<Rightarrow>
    (set P',set B') =
      (set P \<inter> set Q,
       (set Q \<union> erase_annotations_adp `
          ((set P \<union> set B) - set Q)) - (set P \<inter> set Q))"
  by (auto simp: relative_adp_graph_child_def Let_def)

definition relative_adp_move_base_to_main_list ::
  "('f, 'v) adp list \<Rightarrow> ('f, 'v) adp list \<Rightarrow>
   ('f, 'v) relative_adp_problem_list" where
  "relative_adp_move_base_to_main_list P B = (let
      moved = filter (\<lambda>pair. annotated_rhs_subterms_list pair \<noteq> []) B
    in (remdups (P @ moved),
        filter (\<lambda>pair. annotated_rhs_subterms_list pair = []) B))"

lemma annotated_rhs_subterms_list_empty_iff:
  "annotated_rhs_subterms_list pair = [] \<longleftrightarrow>
    annotated_rhs_subterms pair = {}"
proof
  assume "annotated_rhs_subterms_list pair = []"
  with annotated_rhs_subterms_list_sound[of pair]
  show "annotated_rhs_subterms pair = {}" by simp
next
  assume "annotated_rhs_subterms pair = {}"
  with annotated_rhs_subterms_list_sound[of pair]
  have "set (annotated_rhs_subterms_list pair) = {}" by simp
  then show "annotated_rhs_subterms_list pair = []" by simp
qed

lemma relative_adp_move_base_to_main_list_sound:
  assumes finite: "case relative_adp_move_base_to_main_list P B of
      (P',B') \<Rightarrow> adp_problem_SN (set P', set B')"
  shows "adp_problem_SN (set P, set B)"
proof -
  let ?A = "{pair \<in> set B. annotated_rhs_subterms pair \<noteq> {}}"
  have selected: "?A \<subseteq> set B" by blast
  have sets: "case relative_adp_move_base_to_main_list P B of
      (P',B') \<Rightarrow> (set P',set B') =
        (set P \<union> ?A, set B - ?A)"
    unfolding relative_adp_move_base_to_main_list_def Let_def
    by (auto simp: annotated_rhs_subterms_list_empty_iff)
  have "adp_problem_SN (set P \<union> ?A, set B - ?A)"
    using finite sets
    by (cases "relative_adp_move_base_to_main_list P B") simp
  then show ?thesis
    by (rule relative_adp_move_base_to_main[OF selected])
qed

definition relative_adp_drp1_dpp_list where
  "relative_adp_drp1_dpp_list P B =
    (False, False,
      map (map_funs_rule UnLab) (relative_adp_dp_pairs_list P),
      [], [], [],
      map (map_funs_rule UnLab) (relative_adp_flat_rules_list (P @ B)))"

text \<open>Compatibility names for the extracted semantic renaming interface.\<close>

lemmas inj_map_funs_term_NF_terms = Dependency_Pair_Injective_Renaming.inj_map_funs_term_NF_terms
lemmas inj_map_funs_term_NF_subst = Dependency_Pair_Injective_Renaming.inj_map_funs_term_NF_subst
lemmas inj_map_funs_term_qrstep = Dependency_Pair_Injective_Renaming.inj_map_funs_term_qrstep
lemmas inj_map_funs_term_qrsteps = Dependency_Pair_Injective_Renaming.inj_map_funs_term_qrsteps
lemmas inj_map_funs_term_finite_dpp = Dependency_Pair_Injective_Renaming.inj_map_funs_term_finite_dpp

fun check_relative_adp_termination_proof ::
  "(('f::{compare_order,showl,countable}) adp_symbol, string) rule list \<Rightarrow>
   ('f adp_symbol, string) rule list \<Rightarrow>
   'f relative_adp_termination_proof \<Rightarrow> showsl check" where
  "check_relative_adp_termination_proof P B Relative_ADP_Empty =
    check (P = [])
      (showsl_lit (STR ''relative ADP main component is not empty''))"
| "check_relative_adp_termination_proof P B
      (Relative_ADP_Erasure_Redpair redp main_indices base_indices proof) = do {
    check_all (\<lambda>i. i < length P) main_indices
      <+? (\<lambda>i. showsl_lit (STR ''relative ADP main index out of range''));
    check_all (\<lambda>i. i < length B) base_indices
      <+? (\<lambda>i. showsl_lit (STR ''relative ADP base index out of range''));
    let selected = relative_adps_at_indices P B main_indices base_indices;
    check_relative_adp_erasure_redpair redp P B selected;
    let residual = relative_adp_erasure_residual P B selected;
    check_relative_adp_termination_proof (fst residual) (snd residual) proof
  }"
| "check_relative_adp_termination_proof P B
      (Relative_ADP_Com_Redpair redp main_indices base_indices proof) = do {
    check_all (\<lambda>i. i < length P) main_indices
      <+? (\<lambda>i. showsl_lit (STR ''relative ADP main index out of range''));
    check_all (\<lambda>i. i < length B) base_indices
      <+? (\<lambda>i. showsl_lit (STR ''relative ADP base index out of range''));
    let selected = relative_adps_at_indices P B main_indices base_indices;
    check_relative_adp_com_redpair redp P B selected;
    let residual = relative_adp_erasure_residual P B selected;
    check_relative_adp_termination_proof (fst residual) (snd residual) proof
  }"
| "check_relative_adp_termination_proof P B
      (Relative_ADP_Dependency_Graph proofs) = (let
    candidates = relative_adp_estimated_graph_candidates P B
  in do {
    check_all (\<lambda>pair. is_Fun (fst pair)) (P @ B)
      <+? (\<lambda>pair. showsl_lit
        (STR ''relative ADP graph requires function-rooted left-hand sides''));
    check (length proofs = length candidates)
      (showsl_lit (STR ''relative ADP graph child count mismatch''));
    check_allm (\<lambda>(Q,proof).
      let child = relative_adp_graph_child P B Q
      in check_relative_adp_termination_proof
        (fst child) (snd child) proof)
      (zip candidates proofs)
  })"
| "check_relative_adp_termination_proof P B
      (Relative_ADP_Derelatification proof) = (let
    transformed = relative_adp_move_base_to_main_list P B;
    P' = fst transformed;
    B' = snd transformed;
    dpp = relative_adp_drp1_dpp_list P' B'
  in do {
    check (relative_adp_base_flat_list B')
      (showsl_lit (STR ''DRP1 requires an annotation-free base''));
    check_all (\<lambda>pair. is_Fun (fst pair)) (P' @ B')
      <+? (\<lambda>pair. showsl_lit
        (STR ''DRP1 requires function-rooted left-hand sides''));
    check_dp_termination_proof tp_rbt_impl dpp_rbt_impl False
      (showsl_lit (STR ''relative ADP DRP1''))
      (mk_dpp dpp_rbt_impl dpp) proof
  })"

theorem check_relative_adp_termination_proof_sound:
  fixes certificate ::
    "('f::{compare_order,showl,countable}) relative_adp_termination_proof"
  assumes checked:
    "isOK (check_relative_adp_termination_proof P B certificate)"
  shows "adp_problem_SN (set P, set B)"
  using checked
proof (induction certificate arbitrary: P B)
  case Relative_ADP_Empty
  then have "P = []" by simp
  then show ?case by (simp add: empty_main_adp_problem_SN)
next
  case (Relative_ADP_Erasure_Redpair redp main_indices base_indices
      continuation_certificate)
  let ?selected =
    "relative_adps_at_indices P B main_indices base_indices"
  from Relative_ADP_Erasure_Redpair.prems have step:
      "isOK (check_relative_adp_erasure_redpair redp P B ?selected)"
    and continuation:
      "isOK (check_relative_adp_termination_proof
        (fst (relative_adp_erasure_residual P B ?selected))
        (snd (relative_adp_erasure_residual P B ?selected))
        continuation_certificate)"
    by simp_all
  have residual_SN:
    "adp_problem_SN
      (case relative_adp_erasure_residual P B ?selected of
        (P',B') \<Rightarrow> (set P', set B'))"
    using Relative_ADP_Erasure_Redpair.IH[OF continuation]
    by (cases "relative_adp_erasure_residual P B ?selected") simp
  show ?case
    by (rule check_relative_adp_erasure_redpair_sound[
          OF step residual_SN])
next
  case (Relative_ADP_Com_Redpair redp main_indices base_indices
      continuation_certificate)
  let ?selected =
    "relative_adps_at_indices P B main_indices base_indices"
  from Relative_ADP_Com_Redpair.prems have step:
      "isOK (check_relative_adp_com_redpair redp P B ?selected)"
    and continuation:
      "isOK (check_relative_adp_termination_proof
        (fst (relative_adp_erasure_residual P B ?selected))
        (snd (relative_adp_erasure_residual P B ?selected))
        continuation_certificate)"
    by simp_all
  have residual_SN:
    "adp_problem_SN
      (case relative_adp_erasure_residual P B ?selected of
        (P',B') \<Rightarrow> (set P', set B'))"
    using Relative_ADP_Com_Redpair.IH[OF continuation]
    by (cases "relative_adp_erasure_residual P B ?selected") simp
  show ?case
    by (rule check_relative_adp_com_redpair_sound[OF step residual_SN])
next
  case (Relative_ADP_Dependency_Graph proofs)
  let ?candidates = "relative_adp_estimated_graph_candidates P B"
  from Relative_ADP_Dependency_Graph.prems have lhs_fun:
      "\<And>pair. pair \<in> set P \<union> set B \<Longrightarrow> is_Fun (fst pair)"
    by (auto simp: isOK_check_allm)
  from Relative_ADP_Dependency_Graph.prems have length:
      "length proofs = length ?candidates" by simp
  have children: "\<And>Q. Q \<in> set ?candidates \<Longrightarrow>
      adp_problem_SN
        (set P \<inter> set Q,
         (set Q \<union> erase_annotations_adp `
           ((set P \<union> set B) - set Q)) - (set P \<inter> set Q))"
  proof -
    fix Q
    assume Q: "Q \<in> set ?candidates"
    from Q obtain i where i: "i < length ?candidates"
      and Q_nth: "Q = ?candidates ! i"
      by (metis in_set_conv_nth)
    let ?proof = "proofs ! i"
    have proof_index: "i < length proofs" using i length by simp
    have proof_member: "?proof \<in> set proofs"
      using proof_index by simp
    have zipped: "(Q,?proof) \<in> set (zip ?candidates proofs)"
      using i proof_index Q_nth by (auto simp: in_set_zip)
    from Relative_ADP_Dependency_Graph.prems zipped have checked:
        "isOK (check_relative_adp_termination_proof
          (fst (relative_adp_graph_child P B Q))
          (snd (relative_adp_graph_child P B Q)) ?proof)"
      by (auto simp: isOK_check_allm Let_def)
    have child_SN: "adp_problem_SN
        (set (fst (relative_adp_graph_child P B Q)),
         set (snd (relative_adp_graph_child P B Q)))"
      using Relative_ADP_Dependency_Graph.IH[OF proof_member checked] .
    have child_sets: "case relative_adp_graph_child P B Q of (P',B') \<Rightarrow>
        (set P',set B') =
          (set P \<inter> set Q,
           (set Q \<union> erase_annotations_adp `
             ((set P \<union> set B) - set Q)) - (set P \<inter> set Q))"
      by (rule relative_adp_graph_child_sets)
    show "adp_problem_SN
        (set P \<inter> set Q,
         (set Q \<union> erase_annotations_adp `
           ((set P \<union> set B) - set Q)) - (set P \<inter> set Q))"
      using child_SN child_sets
      by (cases "relative_adp_graph_child P B Q") simp
  qed
  show ?case
    by (rule relative_adp_estimated_graph_processor[OF lhs_fun children])
next
  fix cert P B
  assume checked:
    "isOK (check_relative_adp_termination_proof P B
      (Relative_ADP_Derelatification cert))"
  let ?transformed = "relative_adp_move_base_to_main_list P B"
  let ?P' = "fst ?transformed"
  let ?B' = "snd ?transformed"
  let ?dpp = "relative_adp_drp1_dpp_list ?P' ?B'"
  from checked have flat_list:
      "relative_adp_base_flat_list ?B'"
    and lhs_list: "\<And>pair. pair \<in> set (?P' @ ?B') \<Longrightarrow>
      is_Fun (fst pair)"
    and nested: "isOK (check_dp_termination_proof
      tp_rbt_impl dpp_rbt_impl False
      (showsl_lit (STR ''relative ADP DRP1''))
      (mk_dpp dpp_rbt_impl ?dpp) cert)"
    by (auto simp: Let_def isOK_check_allm)
  from check_dp_termination_proof[OF tp_rbt_impl dpp_rbt_impl nested]
  have finite_labeled: "finite_dpp
      (False, False,
        map_funs_trs
          (UnLab :: _ \<Rightarrow> (_, nat list) lab)
          (set (relative_adp_dp_pairs_list ?P')),
        {}, {}, {},
        map_funs_trs
          (UnLab :: _ \<Rightarrow> (_, nat list) lab)
          (set (relative_adp_flat_rules_list (?P' @ ?B'))))"
    unfolding dpp_spec.mk_sound[OF dpp_rbt_impl]
      relative_adp_drp1_dpp_list_def map_funs_trs.simps
    by (simp add: dpp_spec.mk_sound[OF dpp_rbt_impl])
  have finite_plain: "finite_dpp
      (False, False, set (relative_adp_dp_pairs_list ?P'),
        {}, {}, {}, set (relative_adp_flat_rules_list (?P' @ ?B')))"
  proof (rule inj_map_funs_term_finite_dpp[
      where fg="UnLab :: _ \<Rightarrow> (_, nat list) lab" and Q="{}"])
    show "inj (UnLab :: _ \<Rightarrow> (_, nat list) lab)"
      by (rule injI, simp)
    show "finite_dpp
        (False, False,
          map_funs_trs (UnLab :: _ \<Rightarrow> (_, nat list) lab)
            (set (relative_adp_dp_pairs_list ?P')),
          {}, map_funs_term (UnLab :: _ \<Rightarrow> (_, nat list) lab) ` {}, {},
          map_funs_trs (UnLab :: _ \<Rightarrow> (_, nat list) lab)
            (set (relative_adp_flat_rules_list (?P' @ ?B'))))"
      using finite_labeled by simp
  qed
  have transformed_SN: "adp_problem_SN (set ?P', set ?B')"
  proof (rule relative_adp_derelatification_one)
    show "relative_adp_base_flat (set ?B')"
      by (rule iffD1[OF relative_adp_base_flat_list_sound flat_list])
    show "is_Fun (fst pair)" if "pair \<in> set ?P' \<union> set ?B'" for pair
      using lhs_list[of pair] that by simp
    show "finite_dpp
        (False, False, relative_adp_dp_pairs (set ?P'), {}, {}, {},
          relative_adp_flat_rules (set ?P' \<union> set ?B'))"
      using finite_plain
      unfolding relative_adp_dp_pairs_list_sound
        relative_adp_flat_rules_list_sound
      by simp
  qed
  show "adp_problem_SN (set P, set B)"
  proof (rule relative_adp_move_base_to_main_list_sound)
    show "case ?transformed of
        (P', B') \<Rightarrow> adp_problem_SN (set P', set B')"
      using transformed_SN by (cases ?transformed) simp
  qed
qed

definition check_nonduplicating_rules ::
  "('f::{showl}, string) rules \<Rightarrow> showsl check" where
  "check_nonduplicating_rules R =
    check_all (\<lambda>(l,r). vars_term_ms r \<subseteq># vars_term_ms l) R
      <+? (\<lambda>(l,r). showsl_lit (STR ''base rule '') \<circ>
        showsl_rule (l,r) \<circ>
        showsl_lit (STR '' is duplicating''))"

definition check_relative_adp_from_trs ::
  "('f::{compare_order,showl,countable}, string) rules \<Rightarrow>
   ('f, string) rules \<Rightarrow>
   'f relative_adp_termination_proof \<Rightarrow> showsl check" where
  "check_relative_adp_from_trs R B certificate = do {
    check_wf_trs (R @ B);
    check_nonduplicating_rules B;
    let problem = canonical_relative_adp_problem_list R B;
    check_relative_adp_termination_proof
      (fst problem) (snd problem) certificate
  }"

theorem check_relative_adp_from_trs_sound:
  fixes certificate ::
    "('f::{compare_order,showl,countable}) relative_adp_termination_proof"
  assumes checked:
    "isOK (check_relative_adp_from_trs R B certificate)"
  shows "SN_rel (rstep (set R)) (rstep (set B))"
proof -
  from checked have wf: "wf_trs (set R \<union> set B)"
    unfolding check_relative_adp_from_trs_def by simp
  from checked have nondup:
      "\<forall>l r. (l,r) \<in> set B \<longrightarrow>
        vars_term_ms r \<subseteq># vars_term_ms l"
    unfolding check_relative_adp_from_trs_def
      check_nonduplicating_rules_def
    by (auto simp: isOK_check_allm split: prod.splits)
  then have nd: "nonduplicating_trs (set B)"
    unfolding nonduplicating_trs_def by blast
  obtain P S where problem:
      "canonical_relative_adp_problem_list R B = (P,S)"
    by (cases "canonical_relative_adp_problem_list R B") simp
  from checked have cert:
      "isOK (check_relative_adp_termination_proof P S certificate)"
    unfolding check_relative_adp_from_trs_def problem by simp
  have adp_lists: "adp_problem_SN (set P, set S)"
    by (rule check_relative_adp_termination_proof_sound[OF cert])
  have sets:
      "(set P, set S) = canonical_relative_adp_problem (set R) (set B)"
    using canonical_relative_adp_problem_list_sound[of R B]
    unfolding problem by simp
  have adp: "adp_problem_SN
      (canonical_relative_adp_problem (set R) (set B))"
    using adp_lists sets by simp
  show ?thesis
    by (rule canonical_relative_adp_SN_imp_relative_SN[OF wf nd adp])
qed

end
