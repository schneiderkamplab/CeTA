theory LP_Representation
  imports Category_Specification_Bridges.TRS_Representation Category_Properties.LP_Properties
    Category_Specifications.LP_Finite_Spec Category_Specifications.LP_Rational_Spec
    Category_LP_Library.LP_TOCL09_Checker
begin

primcorec logic_to_native :: "('f,'v) logic_tree \<Rightarrow> ('f,'v) lp_iterm" where
  "logic_to_native t = (case t of LVar x \<Rightarrow> LPIVar x
    | LFun f ts \<Rightarrow> LPIFun f (map logic_to_native ts))"
primcorec logic_from_native :: "('f,'v) lp_iterm \<Rightarrow> ('f,'v) logic_tree" where
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


fun logic_to_atom :: "('s \<Rightarrow> 't) \<Rightarrow> ('p,'s) logic_atom \<Rightarrow> 'p \<times> 't list" where
  "logic_to_atom f (LAtom p ts) = (p,map f ts)"
fun logic_from_atom :: "('s \<Rightarrow> 't) \<Rightarrow> ('p \<times> 's list) \<Rightarrow> ('p,'t) logic_atom" where
  "logic_from_atom f (p,ts) = LAtom p (map f ts)"
lemma logic_atom_map_selectors[simp]:
  "logic_predicate (logic_atom_map f a) = logic_predicate a"
  "logic_arguments (logic_atom_map f a) = map f (logic_arguments a)"
  by (cases a; simp)+
lemma logic_to_atom_selectors:
  "logic_to_atom f a = (logic_predicate a, map f (logic_arguments a))"
  by (cases a) simp
lemma logic_to_atom_map:
  "logic_to_atom f (logic_atom_map g a) = logic_to_atom (f \<circ> g) a"
  by (cases a) (simp add: map_map)
lemma logic_atom_subst_translation:
  "logic_to_atom logic_to_native (logic_atom_map (logic_subst s) a) =
    lp_iatom_subst (logic_to_atom logic_to_native a) (logic_to_native \<circ> s)"
  by (cases a) (simp add: lp_iatom_subst_def map_map logic_subst_translation o_def)
lemma logic_atom_eval_translation:
  "logic_to_atom logic_to_native (logic_atom_map (logic_eval r) a) =
    lp_atom_eval (logic_to_atom to_term a) (logic_to_native \<circ> r)"
  by (cases a) (simp add: lp_atom_eval_def map_map logic_eval_translation o_def)
lemma logic_atom_renamed_eval_translation:
  "logic_to_atom logic_to_native
      (logic_atom_map (logic_subst s) (logic_atom_map (logic_eval (LVar \<circ> r)) a)) =
    lp_atom_eval (logic_to_atom to_term a) (logic_to_native \<circ> s \<circ> r)"
  by (cases a) (simp add: lp_atom_eval_def map_map logic_eval_translation
      logic_subst_translation logic_embed_translation lp_ieval_subst o_def)

lemma logic_native_renamed_eval:
  fixes s :: "'v \<Rightarrow> ('f,'v) logic_tree" and r :: "'v \<Rightarrow> 'v"
    and a :: "('p,('f,'v) fo_term) logic_atom"
  shows "lp_iatom_subst (logic_to_atom logic_to_native
      (logic_atom_map (logic_eval (LVar \<circ> r)) a)) (logic_to_native \<circ> s) =
    lp_atom_eval (logic_to_atom to_term a) (logic_to_native \<circ> s \<circ> r)"
  using logic_atom_renamed_eval_translation[of s r a]
  by (simp only: logic_atom_subst_translation)

definition logic_to_program :: "('f,'v) logic_clause list \<Rightarrow> ('f,'v) lp_clause list" where
  "logic_to_program P = map (\<lambda>(h,bs). (logic_to_atom to_term h, map (logic_to_atom to_term) bs)) P"
definition logic_to_goals :: "('f,('f,'v) logic_tree) logic_atom list \<Rightarrow> ('f,'v) lp_iatom list" where
  "logic_to_goals gs = map (logic_to_atom logic_to_native) gs"

text \<open>Every signature-correct single-MGU step is included in the native
all-unifier calculus. This is the direction required by its YES soundness
proofs; it does not assert termination preservation by signature restriction.\<close>
lemma logic_step_native:
  assumes "logic_step A D P s t"
  shows "(logic_to_goals s,logic_to_goals t) \<in> lp_ild (logic_to_program P)"
  using assms
proof (cases rule: logic_step.cases)
  case (resolve h bs r a gs sigma)
  obtain c where c: "c<length P" "P!c=(h,bs)"
    using resolve by (auto simp: in_set_conv_nth)
  have index: "c<length (logic_to_program P)" using c by (simp add: logic_to_program_def)
  have equation: "logic_atom_map (logic_subst sigma) a =
      logic_atom_map (logic_subst sigma) (logic_atom_map (logic_eval (LVar \<circ> r)) h)"
    using resolve unfolding logic_mgu_def by blast
  have eq: "lp_iatom_subst (logic_to_atom logic_to_native a) (logic_to_native \<circ> sigma) =
      lp_atom_eval (fst (logic_to_program P!c)) (logic_to_native \<circ> sigma \<circ> r)"
    using arg_cong[where f="logic_to_atom logic_to_native", OF equation]
    by (simp add: logic_to_program_def c logic_atom_subst_translation logic_atom_renamed_eval_translation logic_native_renamed_eval)
  show ?thesis using lp_ild.resolve[OF index eq, where gs="logic_to_goals gs"]
    by (simp add: resolve logic_to_goals_def logic_to_program_def c map_map
      logic_atom_subst_translation logic_atom_renamed_eval_translation logic_native_renamed_eval[unfolded o_def] o_def)
qed

theorem logic_native_termination:
  fixes P :: "('f,'v) logic_clause list"
  assumes native: "\<And>a :: ('f,('f,'v) fo_term) logic_atom. logic_query A p modes a \<Longrightarrow>
    SN_on (lp_ild (logic_to_program P)) {logic_to_goals [logic_atom_map logic_embed a]}"
  shows "logic_terminates_in A D P p modes"
proof (unfold logic_terminates_in_def, clarify)
  fix a s assume query: "logic_query A p modes a"
    and initial: "s 0 = [logic_atom_map logic_embed a]"
    and steps: "\<forall>n. logic_step A D P (s n) (s (Suc n))"
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
