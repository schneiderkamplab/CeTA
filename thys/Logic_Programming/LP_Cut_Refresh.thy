theory LP_Cut_Refresh
  imports LP_Cut_Guards LP_Symbolic_Evaluation
begin

text \<open>Resolution substitutes the active goal but not saved alternatives.
The symbolic successor must therefore separate their unknown values. Finite
ground values may safely stay shared. Guards on the incoming values remain in
the old namespace; they are not silently rewritten with the answer substitution.\<close>

definition lp_cut_refresh where
  "lp_cut_refresh k G x = (if x\<in>G then Var x else Var (lp_prefix k x))"

definition lp_cut_refresh_env where
  "lp_cut_refresh_env k \<eta> \<sigma> x =
    (if length x<k then \<eta> x else lp_isubst (\<eta> (drop k x)) \<sigma>)"

lemma lp_cut_refresh_active:
  assumes short: "\<forall>x\<in>vars_term t. length x<k"
    and ground: "\<forall>x\<in>G. lp_seg_ground (\<eta> x)"
  shows "lp_ieval (t\<cdot>lp_cut_refresh k G) (lp_cut_refresh_env k \<eta> \<sigma>) =
    lp_isubst (lp_ieval t \<eta>) \<sigma>"
  using short
proof (induct t)
  case (Var x)
  show ?case
    using Var ground by (auto simp: lp_cut_refresh_def lp_cut_refresh_env_def lp_prefix_def
      lp_seg_ground_subst)
next
  case (Fun f ts)
  show ?case using Fun by (auto intro!: map_cong)
qed

lemma lp_cut_refresh_saved:
  assumes "\<forall>x\<in>vars_term t. length x<k"
  shows "lp_ieval t (lp_cut_refresh_env k \<eta> \<sigma>) = lp_ieval t \<eta>"
  by (rule lp_ieval_cong) (use assms in \<open>auto simp: lp_cut_refresh_env_def\<close>)

lemma lp_cut_ground_anchor:
  assumes "lp_ieval t \<eta> = value" "lp_seg_ground value"
  shows "\<forall>x\<in>vars_term t. lp_seg_ground (\<eta> x)"
proof -
  have "lp_seg_ground (lp_ieval t \<eta>)"
    using assms by simp
  then show ?thesis by (simp only: lp_seg_ground_eval)
qed

end
