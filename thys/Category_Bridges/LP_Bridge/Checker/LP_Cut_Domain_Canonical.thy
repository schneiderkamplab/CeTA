theory LP_Cut_Domain_Canonical
  imports LP_Cut_Domain_Table
begin

context cut_runtime_domain
begin

lemma unifiable_iff:
  "(\<exists>s r. (\<forall>x. D (s x)) \<and> (\<forall>x. D (r x)) \<and>
    lp_isubst (cut_tree a) s = lp_ieval (cut_term h) r) \<longleftrightarrow>
   (\<exists>s r. logic_substitution (\<lambda>t. D (cut_tree t)) s \<and>
    logic_substitution (\<lambda>t. D (cut_tree t)) r \<and> logic_subst s a = logic_eval r h)"
proof
  assume "\<exists>s r. (\<forall>x. D (s x)) \<and> (\<forall>x. D (r x)) \<and>
    lp_isubst (cut_tree a) s = lp_ieval (cut_term h) r"
  then obtain s r where ds: "\<forall>x. D (s x)" and dr: "\<forall>x. D (r x)"
    and eq: "lp_isubst (cut_tree a) s = lp_ieval (cut_term h) r" by blast
  have backward: "logic_subst (cut_tree_back \<circ> s) a = logic_eval (cut_tree_back \<circ> r) h"
    by (rule cut_tree_injective[THEN iffD1])
      (use eq in \<open>simp add: cut_tree_subst cut_tree_eval o_def\<close>)
  show "\<exists>s r. logic_substitution (\<lambda>t. D (cut_tree t)) s \<and>
    logic_substitution (\<lambda>t. D (cut_tree t)) r \<and> logic_subst s a = logic_eval r h"
    by (rule exI[of _ "cut_tree_back \<circ> s"], rule exI[of _ "cut_tree_back \<circ> r"])
      (simp add: backward[unfolded o_def] logic_substitution_def o_def ds dr)
next
  assume "\<exists>s r. logic_substitution (\<lambda>t. D (cut_tree t)) s \<and>
    logic_substitution (\<lambda>t. D (cut_tree t)) r \<and> logic_subst s a = logic_eval r h"
  then obtain s r where ds: "logic_substitution (\<lambda>t. D (cut_tree t)) s"
    and dr: "logic_substitution (\<lambda>t. D (cut_tree t)) r"
    and eq: "logic_subst s a = logic_eval r h" by blast
  have forward: "lp_isubst (cut_tree a) (cut_tree \<circ> s) = lp_ieval (cut_term h) (cut_tree \<circ> r)"
    using arg_cong[OF eq, of cut_tree] by (simp add: cut_tree_subst cut_tree_eval)
  show "\<exists>s r. (\<forall>x. D (s x)) \<and> (\<forall>x. D (r x)) \<and>
    lp_isubst (cut_tree a) s = lp_ieval (cut_term h) r"
    by (rule exI[of _ "cut_tree \<circ> s"], rule exI[of _ "cut_tree \<circ> r"])
      (use ds dr forward in \<open>simp add: logic_substitution_def o_def\<close>)
qed

lemma equalizable_iff:
  "(\<exists>s. (\<forall>x. D (s x)) \<and> lp_isubst (cut_tree a) s = lp_isubst (cut_tree b) s) \<longleftrightarrow>
    (\<exists>s. logic_substitution (\<lambda>t. D (cut_tree t)) s \<and> logic_subst s a = logic_subst s b)"
proof
  assume "\<exists>s. (\<forall>x. D (s x)) \<and> lp_isubst (cut_tree a) s = lp_isubst (cut_tree b) s"
  then obtain s where ds: "\<forall>x. D (s x)"
    and eq: "lp_isubst (cut_tree a) s = lp_isubst (cut_tree b) s" by blast
  have backward: "logic_subst (cut_tree_back \<circ> s) a = logic_subst (cut_tree_back \<circ> s) b"
    by (rule cut_tree_injective[THEN iffD1]) (use eq in \<open>simp add: cut_tree_subst o_def\<close>)
  show "\<exists>s. logic_substitution (\<lambda>t. D (cut_tree t)) s \<and> logic_subst s a = logic_subst s b"
    by (rule exI[of _ "cut_tree_back \<circ> s"])
      (simp add: backward[unfolded o_def] logic_substitution_def o_def ds)
next
  assume "\<exists>s. logic_substitution (\<lambda>t. D (cut_tree t)) s \<and> logic_subst s a = logic_subst s b"
  then obtain s where ds: "logic_substitution (\<lambda>t. D (cut_tree t)) s"
    and eq: "logic_subst s a = logic_subst s b" by blast
  have forward: "lp_isubst (cut_tree a) (cut_tree \<circ> s) = lp_isubst (cut_tree b) (cut_tree \<circ> s)"
    using arg_cong[OF eq, of cut_tree] by (simp add: cut_tree_subst)
  show "\<exists>s. (\<forall>x. D (s x)) \<and> lp_isubst (cut_tree a) s = lp_isubst (cut_tree b) s"
    by (rule exI[of _ "cut_tree \<circ> s"])
      (use ds forward in \<open>simp add: logic_substitution_def o_def\<close>)
qed

lemma canonical_step:
  fixes P :: "'f logic_cut_program"
  assumes "logic_cut_step (\<lambda>t. D (cut_tree t)) P s t"
  shows "(cut_state s,cut_state t) \<in> source (cut_program P)"
  using assms
proof (cases rule: logic_cut_step.cases)
  case admin
  then show ?thesis by (auto intro: source.admin simp: cut_admin)
next
  case (case_call m f ts gs es)
  then show ?thesis
    using source.case_call[of m f "map cut_tree ts" "map (cut_goal cut_tree) gs"
      "cut_state es" "cut_program P"]
    by (simp add: cut_slice map_map o_def lp_cut_fresh_def logic_fresh_mark_def image_image)
next
  case (resolve c a gs sigma rho m es)
  have index: "c<length (cut_program P)" using resolve by simp
  have eq: "logic_subst sigma a = logic_eval rho (fst (P!c))"
    using resolve by (auto simp: logic_cut_mgu_def logic_mgu_def logic_atom_map_def)
  have native_eq: "lp_isubst (cut_tree a) (cut_tree \<circ> sigma) =
    lp_ieval (fst (cut_program P!c)) (cut_tree \<circ> rho)"
    using arg_cong[OF eq, of cut_tree] index
    by (simp add: cut_program_nth cut_tree_subst cut_tree_eval)
  have ds: "\<forall>x. D ((cut_tree \<circ> sigma) x)"
    and dr: "\<forall>x. D ((cut_tree \<circ> rho) x)"
    using resolve by (auto simp: logic_cut_mgu_def logic_mgu_def logic_substitution_def o_def)
  show ?thesis
    using source.resolve[OF index native_eq ds dr, where m=m and
      gs="map (cut_goal cut_tree) gs" and es="cut_state es"] resolve
    by (simp add: cut_program_nth map_map o_def
      cut_goal_subst cut_goal_eval_bind)
next
  case (backtrack c a gs m)
  have head: "fst (cut_program P!c) = cut_term (fst (P!c))"
    using backtrack by (simp add: cut_program_nth)
  have index: "c<length (cut_program P)" using backtrack by simp
  have failure: "\<not>(\<exists>sigma :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm. \<exists>rho.
    (\<forall>x. D (sigma x)) \<and> (\<forall>x. D (rho x)) \<and>
    lp_isubst (cut_tree a) sigma = lp_ieval (fst (cut_program P!c)) rho)"
    unfolding head using backtrack unifiable_iff[of a "fst (P!c)"] by blast
  show ?thesis using source.backtrack[OF index failure,
    where gs="map (cut_goal cut_tree) gs" and m=m and es="cut_state t"] backtrack by simp
next
  case (unify a b gs sigma es)
  have eq: "logic_subst sigma a = logic_subst sigma b"
    using unify by (auto simp: logic_unify_mgu_def)
  have native_eq: "lp_isubst (cut_tree a) (cut_tree \<circ> sigma) =
    lp_isubst (cut_tree b) (cut_tree \<circ> sigma)"
    using arg_cong[OF eq, of cut_tree] by (simp add: cut_tree_subst)
  have ds: "\<forall>x. D ((cut_tree \<circ> sigma) x)"
    using unify by (auto simp: logic_unify_mgu_def logic_substitution_def o_def)
  show ?thesis using source.unify[OF native_eq ds,
    where gs="map (cut_goal cut_tree) gs" and es="cut_state es"] unify
    by (simp add: map_map o_def cut_goal_subst)
next
  case (unify_fail a b gs)
  have failure: "\<not>(\<exists>sigma :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm.
    (\<forall>x. D (sigma x)) \<and> lp_isubst (cut_tree a) sigma = lp_isubst (cut_tree b) sigma)"
    using unify_fail by (simp add: equalizable_iff logic_substitution_def)
  show ?thesis using source.unify_fail[OF failure,
    where gs="map (cut_goal cut_tree) gs" and es="cut_state t"] unify_fail by simp
next
  case (meta m f ts gs es body)
  have fresh: "lp_cut_fresh m (cut_state (LogicGoals (LogicMeta (LFun f ts)#gs)#es))"
    using meta by (simp add: lp_cut_fresh_def logic_fresh_mark_def image_image)
  have lower: "lp_cut_lower m (cut_tree (LFun f ts)) (map (cut_goal cut_tree) body)"
    by (rule cut_lower) (use meta in blast)
  show ?thesis using source.meta[OF _ lower,
    where gs="map (cut_goal cut_tree) gs" and es="cut_state es"] meta fresh by simp
next
  case (meta_diverges a gs es)
  have failure: "\<not>(\<exists>m body. lp_cut_lower m (cut_tree a) body)"
    by (rule cut_diverges_unlowerable) (use meta_diverges in blast)
  show ?thesis using source.meta_unlowerable[OF failure,
    where gs="map (cut_goal cut_tree) gs" and es="cut_state es"] meta_diverges
    by simp
qed

theorem canonical_termination:
  assumes native: "\<And>ts. logic_query (LogicUser p) modes (LogicUser p,ts) \<Longrightarrow>
    SN_on (source (cut_program P))
      {cut_state [LogicGoals [LogicAtom (LFun (LogicUser p) (map logic_embed ts))]]}"
  shows "logic_cut_terminates_in (\<lambda>t. D (cut_tree t)) P p modes"
proof (unfold logic_cut_terminates_in_def, clarify)
  fix ts s assume query: "logic_query (LogicUser p) modes (LogicUser p,ts)"
    and init: "s 0 = [LogicGoals [LogicAtom (LFun (LogicUser p) (map logic_embed ts))]]"
    and steps: "\<forall>n. logic_cut_step (\<lambda>t. D (cut_tree t)) P (s n) (s (Suc n))"
  have chain: "\<forall>n. ((cut_state \<circ> s) n,(cut_state \<circ> s) (Suc n))
    \<in> source (cut_program P)"
    by (simp only: o_apply; intro allI; rule canonical_step; rule spec[OF steps])
  have bad: "\<exists>f. f 0 \<in> {cut_state [LogicGoals [LogicAtom (LFun (LogicUser p) (map logic_embed ts))]]}
    \<and> (\<forall>n. (f n,f (Suc n)) \<in> source (cut_program P))"
    by (rule exI[of _ "cut_state \<circ> s"], rule conjI)
      (simp add: init, rule chain)
  show False using native[OF query] bad unfolding SN_on_def by blast
qed

end
end
