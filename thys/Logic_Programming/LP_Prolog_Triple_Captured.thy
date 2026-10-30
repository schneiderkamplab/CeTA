theory LP_Prolog_Triple_Captured
 imports LP_Prolog_Triple_Interface LP_Cut_SEG_Observations
begin

lemma lpp_seg_captured_term:
  assumes actual: "lpp_actual_return P ss eta"
    and ground: "\<forall>x\<in>vars_term t. lp_seg_ground (initial_env x)"
    and known: "list_all (\<lambda>e. \<forall>x\<in>vars_term t. snd e x=initial_env x) ss"
  shows "lp_ieval t eta=lp_ieval t initial_env"
proof (rule lp_ieval_cong)
  fix x assume x: "x\<in>vars_term t"
  have finite: "lp_seg_ground (initial_env x)" using ground x by blast
  have initialized: "list_all (\<lambda>e. snd e x=initial_env x) ss"
    using known x by (auto simp: list_all_iff)
  show "eta x=initial_env x"
    by (rule lpp_actual_return_preserves_finite_value[OF finite actual initialized])
qed

lemma lpp_seg_observed_actual:
  assumes actual: "lpp_actual_return P (lpc_return_eval eta [(e,map Var vs)]) rho"
  obtains theta where
    "lpp_actual_return P [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e,eta)] theta"
    "rho=lpc_return_env (map Var vs) theta"
proof -
  have shape: "lpc_return_eval eta [(e,map Var vs)] =
    lpc_reinterface (lpc_return_env (map Var vs))
      [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e,eta)]"
    by (simp add: lpc_return_eval_def lpc_reinterface_def)
  have observed: "lpp_actual_return P
    (lpc_reinterface (lpc_return_env (map Var vs))
      [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e,eta)]) rho"
    using actual by (simp only: shape)
  show ?thesis
    using lpp_actual_return_reinterface[where F="lpc_return_env (map Var vs)",
      OF lpc_return_env_commutes observed] that by blast
qed

lemma lpp_seg_observed_captured_term:
  assumes actual: "lpp_actual_return P (lpc_return_eval eta [(e,map Var vs)]) rho"
    and distinct: "distinct vs"
    and vars: "vars_term t \<subseteq> set vs"
    and finite: "lp_seg_ground (lp_ieval t eta)"
  shows "lp_ieval (lpc_seg_position_template vs t) rho = lp_ieval t eta"
proof -
  obtain theta where source: "lpp_actual_return P
      [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e,eta)] theta"
    and rho: "rho=lpc_return_env (map Var vs) theta"
    using lpp_seg_observed_actual[OF actual] by blast
  have known: "\<forall>x\<in>vars_term t. lp_seg_ground (eta x)"
    using finite by (simp only: lp_seg_ground_eval)
  have preserved: "lp_ieval t theta=lp_ieval t eta"
    by (rule lpp_seg_captured_term[OF source known]) simp
  show ?thesis unfolding rho
    by (simp only: lpc_seg_position_eval[OF distinct vars] preserved)
qed

end
