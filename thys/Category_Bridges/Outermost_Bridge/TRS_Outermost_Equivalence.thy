theory TRS_Outermost_Equivalence
  imports Category_Properties.TRS_Outermost_Properties
    Category_Specification_Bridges.TRS_Standard_Equivalence
    TRS.Outermost_Rewriting
begin
lemma outermost_root_redex_iff:
  assumes wf: "arity_correct A t"
  shows "outermost_root_redex A R t \<longleftrightarrow>
    (\<exists>l\<in>fst ` to_rules R. \<exists>sigma. to_term t = l \<cdot> sigma)"
proof
  assume "outermost_root_redex A R t"
  then obtain l r sigma where "(l,r) \<in> R" "t = fo_subst sigma l"
    by (auto simp: outermost_root_redex_def)
  then show "\<exists>l\<in>fst ` to_rules R. \<exists>sigma. to_term t = l \<cdot> sigma"
    by (force simp: to_rules_def)
next
  assume "\<exists>l\<in>fst ` to_rules R. \<exists>sigma. to_term t = l \<cdot> sigma"
  then obtain l r sigma where lr: "(l,r) \<in> R" and eq: "to_term t = to_term l \<cdot> sigma"
    by (force simp: to_rules_def)
  let ?sigma = "\<lambda>x. if x \<in> vars_term (to_term l) then sigma x else Var undefined"
  have image: "\<And>x. funas_term (?sigma x) \<subseteq> to_signature A"
    using wf unfolding correct_term_iff eq by (auto simp: funas_term_subst)
  have sub: "to_term l \<cdot> ?sigma = to_term l \<cdot> sigma"
    by (rule term_subst_eq) auto
  have subst: "correct_substitution A (from_substitution ?sigma)"
    using image by (simp add: correct_substitution_iff)
  have term_eq: "t = fo_subst (from_substitution ?sigma) l"
    by (rule to_term_inj[THEN iffD1]) (use eq sub in simp)
  show "outermost_root_redex A R t"
    using lr subst term_eq by (auto simp: outermost_root_redex_def)
qed

lemma outermost_all_positions:
  "(\<forall>q :: nat list. P q) \<longleftrightarrow> P [] \<and> (\<forall>i q. P (i # q))"
  by (metis list.exhaust)
lemma outermost_cond_single_more:
  "ostep_cond_single l (length ls # p) (Fun f (ls @ u # rs)) \<longleftrightarrow>
    ((\<not>(\<exists>sigma. Fun f (ls @ u # rs) = l \<cdot> sigma)) \<and> ostep_cond_single l p u)"
  unfolding ostep_cond_single_def
  apply (subst outermost_all_positions)
  by (auto simp: strict_prefix_def)
lemma outermost_cond_more:
  "ostep_cond Q (length ls # p) (Fun f (ls @ u # rs)) \<longleftrightarrow>
    ((\<forall>l\<in>Q. \<not>(\<exists>sigma. Fun f (ls @ u # rs) = l \<cdot> sigma)) \<and> ostep_cond Q p u)"
  unfolding ostep_cond_def
  by (auto simp: outermost_cond_single_more)

lemma outermost_above_iff:
  assumes "arity_correct A (fo_plug C u)"
  shows "outermost_above A R C u \<longleftrightarrow>
    ostep_cond (fst ` to_rules R) (hole_pos (to_context C)) (to_term (fo_plug C u))"
  using assms
proof (induct C)
  case SHole
  then show ?case by (simp add: ostep_cond_def ostep_cond_single_def)
next
  case (SMore f ls C rs)
  have wf: "arity_correct A (fo_plug C u)"
    using SMore.prems by (simp add: list_all_iff)
  show ?case using SMore.hyps[OF wf] outermost_root_redex_iff[OF SMore.prems, of R]
    using outermost_cond_more[where ls="map to_term ls" and rs="map to_term rs" and f=f]
    by simp
qed

lemma outermost_step_iff:
  "outermost_step A R s t \<longleftrightarrow>
    (to_term s, to_term t) \<in> sig_step (to_signature A) (ostep (fst ` to_rules R) (to_rules R))"
proof
  assume "outermost_step A R s t"
  then obtain l r C sigma where
    wf: "arity_correct A s" "arity_correct A t" and lr: "(l,r) \<in> R"
    and above: "outermost_above A R C (fo_subst sigma l)"
    and eq: "s = fo_plug C (fo_subst sigma l)"
      "t = fo_plug C (fo_subst sigma r)"
    by (auto simp: outermost_step_def)
  have raw: "(to_term s,to_term t) \<in> rstep_r_p_s (to_rules R)
    (to_term l,to_term r) (hole_pos (to_context C)) (to_substitution sigma)"
    using lr unfolding eq by (auto simp: rstep_r_p_s_def Let_def to_rules_def)
  have cond: "ostep_cond (fst ` to_rules R) (hole_pos (to_context C)) (to_term s)"
    using outermost_above_iff[of A C "fo_subst sigma l" R] above wf(1) unfolding eq by simp
  have at_p: "(to_term s,to_term t) \<in> ostep_p (fst ` to_rules R) (to_rules R) (hole_pos (to_context C))"
    by (rule ostep_pI[OF raw cond])
  have outer: "(to_term s,to_term t) \<in> ostep (fst ` to_rules R) (to_rules R)"
    using at_p unfolding ostep_def by blast
  show "(to_term s, to_term t) \<in> sig_step (to_signature A) (ostep (fst ` to_rules R) (to_rules R))"
    using outer wf by auto
next
  assume step: "(to_term s, to_term t) \<in> sig_step (to_signature A) (ostep (fst ` to_rules R) (to_rules R))"
  then have wf: "funas_term (to_term s) \<subseteq> to_signature A"
    "funas_term (to_term t) \<subseteq> to_signature A" by auto
  obtain l' r' p sigma where raw:
    "(to_term s,to_term t) \<in> rstep_r_p_s (to_rules R) (l',r') p sigma"
    and cond: "ostep_cond (fst ` to_rules R) p (to_term s)"
    using step by (auto simp: ostep_defs)
  define C where "C = ctxt_of_pos_term p (to_term s)"
  have lr': "(l',r') \<in> to_rules R"
    and eq: "to_term s = C\<langle>l' \<cdot> sigma\<rangle>" "to_term t = C\<langle>r' \<cdot> sigma\<rangle>"
    and pos: "p \<in> poss (to_term s)"
    using raw by (auto simp: rstep_r_p_s_def Let_def C_def)
  from lr' obtain l r where lr: "(l,r) \<in> R" and l: "l' = to_term l" and r: "r' = to_term r"
    by (auto simp: to_rules_def)
  let ?sigma = "\<lambda>x. if x \<in> vars_term l' \<union> vars_term r' then sigma x else Var undefined"
  have image: "\<And>x. funas_term (?sigma x) \<subseteq> to_signature A"
    using wf unfolding eq by (auto simp: funas_term_subst)
  have sub: "l' \<cdot> ?sigma = l' \<cdot> sigma" "r' \<cdot> ?sigma = r' \<cdot> sigma"
    by (auto intro: term_subst_eq)
  have ctxt: "correct_context A (from_context C)"
    using wf(1) unfolding eq by simp
  have subst: "correct_substitution A (from_substitution ?sigma)"
    using image by (simp add: correct_substitution_iff)
  have se: "s = fo_plug (from_context C) (fo_subst (from_substitution ?sigma) l)"
    by (rule to_term_inj[THEN iffD1]) (use eq(1) sub(1) in \<open>simp add: l\<close>)
  have te: "t = fo_plug (from_context C) (fo_subst (from_substitution ?sigma) r)"
    by (rule to_term_inj[THEN iffD1]) (use eq(2) sub(2) in \<open>simp add: r\<close>)
  have hole: "hole_pos C = p" using pos by (simp add: C_def)
  have awf: "arity_correct A (fo_plug (from_context C) (fo_subst (from_substitution ?sigma) l))"
    using wf(1) by (simp only: se[symmetric] correct_term_iff)
  have above: "outermost_above A R (from_context C) (fo_subst (from_substitution ?sigma) l)"
    using outermost_above_iff[OF awf, of R] cond
    by (simp only: se[symmetric] contexts_roundtrip hole)
  show "outermost_step A R s t"
    unfolding outermost_step_def
    using wf lr ctxt subst se te above by (auto simp only: correct_term_iff)
qed

lemma trs_outermost_terminates_iff_signature:
  "trs_outermost_terminates A R \<longleftrightarrow> SN (sig_step (to_signature A) (ostep (fst ` to_rules R) (to_rules R)))"
proof -
  have chains: "(\<exists>ts. \<forall>i. outermost_step A R (ts i) (ts (Suc i))) \<longleftrightarrow>
    (\<exists>ts. \<forall>i. (ts i, ts (Suc i)) \<in> sig_step (to_signature A) (ostep (fst ` to_rules R) (to_rules R)))"
  proof
    assume "\<exists>ts. \<forall>i. outermost_step A R (ts i) (ts (Suc i))"
    then obtain ts where "\<forall>i. outermost_step A R (ts i) (ts (Suc i))" by blast
    then show "\<exists>ts. \<forall>i. (ts i, ts (Suc i)) \<in> sig_step (to_signature A) (ostep (fst ` to_rules R) (to_rules R))"
      by (intro exI[of _ "to_term \<circ> ts"]) (simp add: outermost_step_iff)
  next
    assume "\<exists>ts. \<forall>i. (ts i, ts (Suc i)) \<in> sig_step (to_signature A) (ostep (fst ` to_rules R) (to_rules R))"
    then obtain ts where "\<forall>i. (ts i, ts (Suc i)) \<in> sig_step (to_signature A) (ostep (fst ` to_rules R) (to_rules R))" by blast
    then show "\<exists>ts. \<forall>i. outermost_step A R (ts i) (ts (Suc i))"
      by (intro exI[of _ "from_term \<circ> ts"]) (simp add: outermost_step_iff)
  qed
  show ?thesis unfolding trs_outermost_terminates_def no_infinite_steps_def SN_defs using chains by blast
qed
lemma trs_outermost_nonterminates_iff_signature:
  "\<not> trs_outermost_terminates A R \<longleftrightarrow>
    \<not> SN (sig_step (to_signature A) (ostep (fst ` to_rules R) (to_rules R)))"
  by (simp only: trs_outermost_terminates_iff_signature)
end
