theory LP_Prolog_Stable_Refresh
 imports LP_Prolog_Stable_Observed_Is
begin

lemma lpp_stable_context_refresh_sound:
  fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes known: "lpp_stable_context_holds operation P source_context eta"
    and short: "lpp_context_short k source_context"
    and bounds: "2 * k \<le> l"
    and ground: "\<forall>x\<in>G. lp_seg_ground (eta x)"
  shows "lpp_stable_context_holds operation P (lpp_source_context_subst source_context (lp_cut_refresh k G))
    (lp_cut_resolution_env k l eta sigma rho)"
proof -
  have stable: "lpp_stable_context_holds operation P source_context (\<lambda>x. lp_isubst (eta x) sigma)"
    by (rule lpp_stable_context_runtime_subst[OF known])
  have same: "lp_ieval t (\<lambda>x. lp_ieval (lp_cut_refresh k G x) (lp_cut_resolution_env k l eta sigma rho)) =
    lp_ieval t (\<lambda>x. lp_isubst (eta x) sigma)" if member: "t\<in>set (lpp_context_terms source_context)" for t
  proof -
    have small: "\<forall>x\<in>vars_term t. length x<k"
      using short member by (auto simp: lpp_context_short_def list_all_iff)
    show ?thesis using lp_cut_resolution_active[OF small bounds ground]
      by (simp add: lp_ieval_finite_subst lp_ieval_subst)
  qed
  show ?thesis using lpp_stable_context_environment_cong[where ctx=source_context and P=P, OF same] stable
    by (simp only: lpp_stable_context_substitute)
qed

lemma lpp_stable_context_fork_sound:
  fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes known: "lpp_stable_context_holds operation P source_context eta"
    and short: "lpp_context_short k source_context"
    and bounds: "2 * k \<le> l"
    and ground: "\<forall>x\<in>G. lp_seg_ground (eta x)"
  shows "lpp_stable_context_holds operation P (lpp_evaluation_fork_context source_context k G)
    (lp_cut_resolution_env k l eta sigma rho)"
proof -
  have old: "lp_ieval t (lp_cut_resolution_env k l eta sigma rho)=lp_ieval t eta"
    if "t\<in>set (lpp_context_terms source_context)" for t
    by (rule lp_cut_resolution_old)
      (use short that bounds in \<open>auto simp: lpp_context_short_def list_all_iff\<close>)
  have original: "lpp_stable_context_holds operation P source_context (lp_cut_resolution_env k l eta sigma rho)"
    using known lpp_stable_context_environment_cong[where ctx=source_context and operation=operation and P=P, OF old]
    by simp
  have refreshed: "lpp_stable_context_holds operation P
    (lpp_source_context_subst source_context (lp_cut_refresh k G)) (lp_cut_resolution_env k l eta sigma rho)"
    by (rule lpp_stable_context_refresh_sound[OF known short bounds ground])
  show ?thesis using original refreshed
    by (simp add: lpp_evaluation_fork_context_def lpp_stable_context_join)
qed

ML \<open>
val checked = [@{thm lpp_stable_context_refresh_sound}, @{thm lpp_stable_context_fork_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable refresh dependency" else ();
\<close>
end
