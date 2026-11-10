theory LP_Representation
  imports Category_Specification_Bridges.TRS_Representation
    Category_Specifications.LP_Finite_Spec Category_Specifications.LP_Rational_Spec
    Category_LP_Library.LP_TOCL09_Checker
begin

primcorec logic_to_native :: "'f logic_tree \<Rightarrow> ('f,string) lp_iterm" where
  "logic_to_native t = (case t of LVar x \<Rightarrow> LPIVar x
    | LFun f ts \<Rightarrow> LPIFun f (map logic_to_native ts))"
primcorec logic_from_native :: "('f,string) lp_iterm \<Rightarrow> 'f logic_tree" where
  "logic_from_native t = (case t of LPIVar x \<Rightarrow> LVar x
    | LPIFun f ts \<Rightarrow> LFun f (map logic_from_native ts))"

lemma logic_to_simps[simp]:
  "logic_to_native (LVar x) = LPIVar x"
  "logic_to_native (LFun f ts) = LPIFun f (map logic_to_native ts)"
  by (subst logic_to_native.code; simp)+

lemma logic_from_simps[simp]:
  "logic_from_native (LPIVar x) = LVar x"
  "logic_from_native (LPIFun f ts) = LFun f (map logic_from_native ts)"
  by (subst logic_from_native.code; simp)+

lemma logic_roundtrip[simp]: "logic_from_native (logic_to_native t) = t"
  by (coinduction arbitrary: t) (case_tac t; auto simp: list_all2_map1 list.rel_refl)

lemma logic_native_roundtrip[simp]: "logic_to_native (logic_from_native t) = t"
  by (coinduction arbitrary: t) (case_tac t; auto simp: list_all2_map1 list.rel_refl)

lemma logic_translation_inj[simp]: "logic_to_native a = logic_to_native b \<longleftrightarrow> a=b"
  by (metis logic_roundtrip)


lemma logic_subst_simps[simp]:
  "logic_subst s (LVar x) = s x"
  "logic_subst s (LFun f ts) = LFun f (map (logic_subst s) ts)"
  by (subst logic_subst.code; simp)+

lemma logic_subst_translation:
  "logic_to_native (logic_subst s t) = lp_isubst (logic_to_native t) (logic_to_native \<circ> s)"
  by (coinduction arbitrary: t rule: lp_iterm.coinduct_strong)
    (case_tac t; auto simp: list_all2_map1 list_all2_map2 intro!: list.rel_refl)

lemma logic_eval_translation:
  "logic_to_native (logic_eval r t) = lp_ieval (to_term t) (logic_to_native \<circ> r)"
  by (induct t) (auto simp: map_map o_def)

lemma logic_embed_translation:
  "logic_to_native (logic_embed t) = lp_ieval (to_term t) LPIVar"
  by (induct t) (auto simp: map_map o_def)

lemma logic_ground_translation:
  "logic_ground t \<longleftrightarrow> ground (to_term t)"
  by (induct t) (auto simp: list_all_iff)


definition logic_to_program where
  "logic_to_program P = map (\<lambda>(h,bs).
    (logic_atom_map to_term h, map (logic_atom_map to_term) bs)) P"
definition logic_to_goals where
  "logic_to_goals gs = map (logic_atom_map logic_to_native) gs"

lemma logic_atom_map_comp:
  "logic_atom_map f (logic_atom_map g a) = logic_atom_map (f \<circ> g) a"
  by (simp add: logic_atom_map_def)

lemma logic_atom_subst_translation:
  "logic_atom_map logic_to_native (logic_atom_map (logic_subst s) a) =
    lp_iatom_subst (logic_atom_map logic_to_native a) (logic_to_native \<circ> s)"
  by (simp add: logic_atom_map_def lp_iatom_subst_def map_map logic_subst_translation o_def)

lemma logic_atom_eval_translation:
  "logic_atom_map logic_to_native (logic_atom_map (logic_eval r) a) =
    lp_atom_eval (logic_atom_map to_term a) (logic_to_native \<circ> r)"
  by (simp add: logic_atom_map_def lp_atom_eval_def map_map logic_eval_translation o_def)


text \<open>The existing YES calculus admits all unifiers and all infinite trees.
Each exact finite or rational most-general step is included in that calculus.
This is a one-way simulation, deliberately not an asserted equivalence.\<close>
lemma logic_step_native:
  assumes "logic_step D P s t"
  shows "(logic_to_goals s,logic_to_goals t) \<in> lp_ild (logic_to_program P)"
  using assms
proof (cases rule: logic_step.cases)
  case (resolve h bs a gs sigma rho)
  obtain c where c: "c<length P" "P!c=(h,bs)"
    using resolve by (auto simp: in_set_conv_nth)
  have index: "c<length (logic_to_program P)" using c by (simp add: logic_to_program_def)
  have mgu: "logic_mgu D a gs h bs sigma rho" using resolve by blast
  have equation: "logic_atom_map (logic_subst sigma) a = logic_atom_map (logic_eval rho) h"
    using mgu unfolding logic_mgu_def by blast
  have eq: "lp_iatom_subst (logic_atom_map logic_to_native a) (logic_to_native \<circ> sigma) =
    lp_atom_eval (fst (logic_to_program P!c)) (logic_to_native \<circ> rho)"
    using arg_cong[where f="logic_atom_map logic_to_native", OF equation]
    by (simp add: logic_to_program_def c logic_atom_subst_translation logic_atom_eval_translation)
  show ?thesis using lp_ild.resolve[OF index eq, where gs="logic_to_goals gs"]
    by (simp add: resolve logic_to_goals_def logic_to_program_def c map_map
      logic_atom_subst_translation logic_atom_eval_translation o_def)
qed


theorem logic_native_termination:
  assumes native: "\<And>a. logic_query p modes a \<Longrightarrow>
    SN_on (lp_ild (logic_to_program P)) {logic_to_goals [logic_atom_map logic_embed a]}"
  shows "logic_terminates_in D P p modes"
proof (unfold logic_terminates_in_def, clarify)
  fix a s assume query: "logic_query p modes a"
    and initial: "s 0 = [logic_atom_map logic_embed a]"
    and steps: "\<forall>n. logic_step D P (s n) (s (Suc n))"
  have "\<forall>n. ((logic_to_goals \<circ> s) n,(logic_to_goals \<circ> s) (Suc n))
    \<in> lp_ild (logic_to_program P)" by (simp only: o_apply; intro allI; rule logic_step_native; rule spec[OF steps])
  moreover have "(logic_to_goals \<circ> s) 0 = logic_to_goals [logic_atom_map logic_embed a]"
    using initial by simp
  ultimately have bad: "\<exists>f. f 0 \<in> {logic_to_goals [logic_atom_map logic_embed a]} \<and>
    (\<forall>n. (f n,f (Suc n)) \<in> lp_ild (logic_to_program P))"
    by (intro exI[of _ "logic_to_goals \<circ> s"]) simp
  show False using native[OF query] bad unfolding SN_on_def by blast
qed


end
