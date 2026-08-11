theory Relative_ADP_Semantics
  imports
    TRS.Q_Relative_Rewriting
    Framework.Relative_DP_Framework
begin

datatype 'f adp_symbol = Plain 'f | Sharp 'f

fun erase_adp_symbol :: "'f adp_symbol \<Rightarrow> 'f" where
  "erase_adp_symbol (Plain f) = f"
| "erase_adp_symbol (Sharp f) = f"

fun is_sharp_symbol :: "'f adp_symbol \<Rightarrow> bool" where
  "is_sharp_symbol (Plain _) = False"
| "is_sharp_symbol (Sharp _) = True"

fun erase_adp_term :: "('f adp_symbol, 'v) term \<Rightarrow> ('f, 'v) term" where
  "erase_adp_term (Var x) = Var x"
| "erase_adp_term (Fun f ts) = Fun (erase_adp_symbol f) (map erase_adp_term ts)"

fun plain_adp_term :: "('f, 'v) term \<Rightarrow> ('f adp_symbol, 'v) term" where
  "plain_adp_term (Var x) = Var x"
| "plain_adp_term (Fun f ts) = Fun (Plain f) (map plain_adp_term ts)"

type_synonym ('f, 'v) adp = "('f adp_symbol, 'v) term \<times> ('f adp_symbol, 'v) term"
type_synonym ('f, 'v) adp_problem = "('f, 'v) adp set \<times> ('f, 'v) adp set"

definition erase_adp :: "('f, 'v) adp \<Rightarrow> ('f, 'v) rule" where
  "erase_adp p = (erase_adp_term (fst p), erase_adp_term (snd p))"

fun annotate_term_at and annotate_terms_at where
  "annotate_term_at A p (Var x) = Var x"
| "annotate_term_at A p (Fun f ts) =
    Fun (if p \<in> A then Sharp f else Plain f) (annotate_terms_at A p 0 ts)"
| "annotate_terms_at A p i [] = []"
| "annotate_terms_at A p i (t # ts) =
    annotate_term_at A (p @ [i]) t # annotate_terms_at A p (Suc i) ts"

definition annotate_term :: "pos set \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f adp_symbol, 'v) term" where
  "annotate_term A t = annotate_term_at A [] t"

lemma erase_plain_adp_term [simp]: "erase_adp_term (plain_adp_term t) = t"
  by (induct t) (auto simp: map_idI)

lemma erase_annotate_term_at:
  fixes t :: "('f, 'v) term"
  shows "erase_adp_term (annotate_term_at A p t) = t"
  and erase_annotate_terms_at:
  "map erase_adp_term (annotate_terms_at A p i (ts :: ('f, 'v) term list)) = ts"
  by (induct A p t and A p i ts rule: annotate_term_at_annotate_terms_at.induct) auto

lemma erase_annotate_term [simp]: "erase_adp_term (annotate_term A t) = t"
  unfolding annotate_term_def by (rule erase_annotate_term_at)

lemma poss_erase_adp_term [simp]: "poss (erase_adp_term t) = poss t"
  by (induct t) auto

lemma erase_adp_term_subt_at [simp]:
  "p \<in> poss t \<Longrightarrow> erase_adp_term (t |_ p) = erase_adp_term t |_ p"
proof (induct p arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons i p)
  then show ?case by (cases t) (auto simp: take_map drop_map)
qed

lemma erase_adp_term_replace_at [simp]:
  "p \<in> poss t \<Longrightarrow> erase_adp_term (replace_at t p u) =
    replace_at (erase_adp_term t) p (erase_adp_term u)"
proof (induct p arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons i p)
  then show ?case by (cases t) (auto simp: take_map drop_map)
qed

definition sharp_positions :: "('f adp_symbol, 'v) term \<Rightarrow> pos set" where
  "sharp_positions t =
    {p \<in> poss t. case root (t |_ p) of Some (f, _) \<Rightarrow> is_sharp_symbol f | None \<Rightarrow> False}"

fun plain_adp_term_pred :: "('f adp_symbol, 'v) term \<Rightarrow> bool" where
  "plain_adp_term_pred (Var _) = True"
| "plain_adp_term_pred (Fun f ts) =
    ((\<exists>g. f = Plain g) \<and> list_all plain_adp_term_pred ts)"

definition valid_vrf ::
  "('f, 'v) adp \<Rightarrow> (pos \<Rightarrow> pos option) \<Rightarrow> bool" where
  "valid_vrf adp phi \<longleftrightarrow>
    (\<forall>p \<in> var_poss (fst adp).
      case phi p of
        None \<Rightarrow> True
      | Some q \<Rightarrow> q \<in> var_poss (snd adp) \<and> fst adp |_ p = snd adp |_ q)"

definition transported_annotations ::
  "(pos \<Rightarrow> pos option) \<Rightarrow> ('f adp_symbol, 'v) term \<Rightarrow>
    ('f adp_symbol, 'v) term \<Rightarrow> pos set" where
  "transported_annotations phi l source =
    {q @ tau | p q tau. p \<in> var_poss l \<and> phi p = Some q \<and>
      p @ tau \<in> sharp_positions source}"

inductive adp_step_case ::
  "('f, 'v) adp set \<Rightarrow> bool \<Rightarrow>
    ('f adp_symbol, 'v) term \<Rightarrow> ('f adp_symbol, 'v) term \<Rightarrow> bool" where
  adp_stepI:
    "(l, r) \<in> P \<Longrightarrow>
     plain_adp_term_pred l \<Longrightarrow>
     valid_vrf (l, r) phi \<Longrightarrow>
     p \<in> fun_poss s \<Longrightarrow>
     at_sharp = (p \<in> sharp_positions s) \<Longrightarrow>
     erase_adp_term (s |_ p) = erase_adp_term l \<cdot> sigma \<Longrightarrow>
     A = (if at_sharp then sharp_positions r else {}) \<union>
         transported_annotations phi l (s |_ p) \<Longrightarrow>
     t = replace_at s p (annotate_term A (erase_adp_term r \<cdot> sigma)) \<Longrightarrow>
     adp_step_case P at_sharp s t"

definition adp_step_case_rel ::
  "('f, 'v) adp set \<Rightarrow> bool \<Rightarrow> ('f adp_symbol, 'v) term rel" where
  "adp_step_case_rel P at_sharp = {(s, t). adp_step_case P at_sharp s t}"

definition adp_step :: "('f, 'v) adp set \<Rightarrow> ('f adp_symbol, 'v) term rel" where
  "adp_step P = adp_step_case_rel P True \<union> adp_step_case_rel P False"

lemma adp_step_case_rel_empty [simp]: "adp_step_case_rel {} at_sharp = {}"
  unfolding adp_step_case_rel_def
  by (auto elim: adp_step_case.cases)

lemma adp_step_case_erases:
  assumes "adp_step_case P at_sharp s t"
  shows "(erase_adp_term s, erase_adp_term t) \<in> rstep (erase_adp ` P)"
  using assms
proof cases
  case (adp_stepI l r phi p sigma A)
  have p_poss: "p \<in> poss s"
    using adp_stepI(4) by (rule fun_poss_imp_poss)
  have rule: "(erase_adp_term l, erase_adp_term r) \<in> erase_adp ` P"
    using adp_stepI(1) by (force simp: erase_adp_def)
  show ?thesis
  proof (rule rstep_r_p_s_imp_rstep[
      where r = "(erase_adp_term l, erase_adp_term r)" and p = p and \<sigma> = sigma])
    show "(erase_adp_term s, erase_adp_term t)
        \<in> rstep_r_p_s (erase_adp ` P)
          (erase_adp_term l, erase_adp_term r) p sigma"
      unfolding rstep_r_p_s_def'
      using adp_stepI p_poss rule
      by auto
  qed
qed

lemma adp_step_case_rel_erases:
  assumes "(s, t) \<in> adp_step_case_rel P at_sharp"
  shows "(erase_adp_term s, erase_adp_term t) \<in> rstep (erase_adp ` P)"
  using assms adp_step_case_erases
  unfolding adp_step_case_rel_def by auto

lemma adp_step_erases:
  assumes "(s, t) \<in> adp_step P"
  shows "(erase_adp_term s, erase_adp_term t) \<in> rstep (erase_adp ` P)"
  using assms adp_step_case_rel_erases
  unfolding adp_step_def by auto

definition adp_problem_SN :: "('f, 'v) adp_problem \<Rightarrow> bool" where
  "adp_problem_SN problem \<longleftrightarrow>
    SN_rel (adp_step_case_rel (fst problem) True)
      (adp_step (fst problem \<union> snd problem))"

definition adp_defined_symbols :: "('f, 'v) trs \<Rightarrow> 'f set" where
  "adp_defined_symbols R =
    {f. \<exists>l r ts. (l, r) \<in> R \<and> l = Fun f ts}"

definition adp_defined_positions ::
  "'f set \<Rightarrow> ('f, 'v) term \<Rightarrow> pos set" where
  "adp_defined_positions D t =
    {p \<in> poss t. \<exists>f ts. t |_ p = Fun f ts \<and> f \<in> D}"

definition canonical_adps ::
  "nat \<Rightarrow> 'f set \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) adp set" where
  "canonical_adps n D R =
    {(plain_adp_term l, annotate_term A r) | l r A.
      (l, r) \<in> R \<and>
      A \<subseteq> adp_defined_positions D r \<and>
      card A = min n (card (adp_defined_positions D r))}"

definition canonical_relative_adp_problem ::
  "('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) adp_problem" where
  "canonical_relative_adp_problem R B =
    (let D = adp_defined_symbols (R \<union> B)
     in (canonical_adps 1 D R, canonical_adps 2 D B))"

definition nonduplicating_trs :: "('f, 'v) trs \<Rightarrow> bool" where
  "nonduplicating_trs R \<longleftrightarrow>
    (\<forall>l r. (l, r) \<in> R \<longrightarrow> vars_term_ms r \<subseteq># vars_term_ms l)"

lemma erase_adp_plain_annotated [simp]:
  "erase_adp (plain_adp_term l, annotate_term A r) = (l, r)"
  by (simp add: erase_adp_def)

lemma erase_canonical_adps_subset:
  "erase_adp ` canonical_adps n D R \<subseteq> R"
  unfolding canonical_adps_def by auto

lemma finite_adp_defined_positions [simp]:
  "finite (adp_defined_positions D t)"
  unfolding adp_defined_positions_def by (rule finite_subset[OF _ finite_poss]) auto

lemma erase_canonical_adps:
  "erase_adp ` canonical_adps n D R = R"
proof (rule equalityI, rule erase_canonical_adps_subset, rule subsetI)
  fix lr
  assume "lr \<in> R"
  then obtain l r where lr: "lr = (l, r)" by (cases lr) auto
  let ?A = "adp_defined_positions D r"
  have "min n (card ?A) \<le> card ?A" by simp
  then obtain A where A: "A \<subseteq> ?A" "card A = min n (card ?A)"
    using obtain_subset_with_card_n by blast
  have "(plain_adp_term l, annotate_term A r) \<in> canonical_adps n D R"
    using `lr \<in> R` A unfolding lr canonical_adps_def by blast
  then show "lr \<in> erase_adp ` canonical_adps n D R"
    unfolding lr by force
qed

lemma SN_rel_hom:
  fixes R S :: "'a rel" and R' S' :: "'b rel" and f :: "'a \<Rightarrow> 'b"
  assumes sn: "SN_rel R' S'"
    and strict: "\<And>s t. (s, t) \<in> R \<Longrightarrow> (f s, f t) \<in> R'"
    and weak: "\<And>s t. (s, t) \<in> S \<Longrightarrow> (f s, f t) \<in> R' \<union> S'"
  shows "SN_rel R S"
  unfolding SN_rel_ideriv
proof (intro notI, elim exE)
  fix as
  assume deriv: "ideriv R S as"
  have steps: "\<forall>i. (f (as i), f (as (Suc i))) \<in> R' \<union> S'"
    using deriv strict weak unfolding ideriv_def by blast
  have inf: "INFM i. (f (as i), f (as (Suc i))) \<in> R'"
  proof (rule INFM_mono[OF deriv[unfolded ideriv_def, THEN conjunct2]])
    fix i
    assume "(as i, as (Suc i)) \<in> R"
    then show "(f (as i), f (as (Suc i))) \<in> R'" by (rule strict)
  qed
  have "ideriv R' S' (f \<circ> as)"
    using steps inf unfolding ideriv_def by simp
  with sn[unfolded SN_rel_ideriv] show False by blast
qed

lemma adp_problem_SN_if_erasure_SN:
  assumes sn: "SN_rel (rstep R) (rstep B)"
    and main: "erase_adp ` P \<subseteq> R"
    and base: "erase_adp ` Q \<subseteq> B"
  shows "adp_problem_SN (P, Q)"
  unfolding adp_problem_SN_def fst_conv snd_conv
  apply (rule SN_rel_hom[OF sn, where f = erase_adp_term])
  subgoal for s t
    using adp_step_case_rel_erases[of s t P True] rstep_mono[OF main]
    by blast
  subgoal for s t
    using adp_step_erases[of s t "P \<union> Q"]
      rstep_mono[OF Un_mono[OF main base]]
    by (simp only: rstep_union) blast
  done

lemma relative_SN_imp_canonical_adp_SN:
  assumes "SN_rel (rstep R) (rstep B)"
  shows "adp_problem_SN (canonical_relative_adp_problem R B)"
  unfolding canonical_relative_adp_problem_def Let_def
  by (rule adp_problem_SN_if_erasure_SN[OF assms])
     (rule erase_canonical_adps_subset)+

lemma empty_main_adp_problem_SN [simp]: "adp_problem_SN ({}, B)"
  unfolding adp_problem_SN_def by (simp add: SN_rel_empty1)

end
