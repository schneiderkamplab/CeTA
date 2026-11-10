theory LP_Cut_Domain_SEG_Captured
 imports LP_Cut_Domain_SEG_Instance
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

lemma precise_seg_captured_step:
  assumes step: "precise_answer_transition P ss event us"
    and ground: "\<forall>x\<in>G. lp_seg_ground (initial_env x)"
    and known: "list_all (\<lambda>e. \<forall>x\<in>G. snd e x=initial_env x) ss"
  shows "list_all (\<lambda>e. \<forall>x\<in>G. snd e x=initial_env x) us \<and>
    (\<forall>eta. event=Some eta \<longrightarrow> (\<forall>x\<in>G. eta x=initial_env x))"
  using step known ground
  by (cases rule: precise_answer_transition.cases)
    (auto simp: list_all_iff lp_seg_ground_subst
      dest: subsetD[OF lpc_answer_prune_set_subset])


lemma precise_seg_captured_actual:
  assumes actual: "precise_actual_return P ss eta"
    and ground: "\<forall>x\<in>G. lp_seg_ground (initial_env x)"
    and known: "list_all (\<lambda>e. \<forall>x\<in>G. snd e x=initial_env x) ss"
  shows "\<forall>x\<in>G. eta x=initial_env x"
proof -
  obtain us tail where path: "(ss,us)\<in>(precise_answer_steps P)\<^sup>*"
    and event: "precise_answer_transition P us (Some eta) tail"
    using actual by (auto simp: precise_actual_return_def)
  have preserved: "list_all (\<lambda>e. \<forall>x\<in>G. snd e x=initial_env x) us"
    using path known
    by (induct rule: rtrancl_induct)
      (auto simp: precise_answer_steps_def dest: precise_seg_captured_step[OF _ ground])
  show ?thesis using precise_seg_captured_step[OF event ground preserved] by simp
qed


lemma precise_seg_captured_term:
  assumes actual: "precise_actual_return P ss eta"
    and ground: "\<forall>x\<in>vars_term t. lp_seg_ground (initial_env x)"
    and known: "list_all (\<lambda>e. \<forall>x\<in>vars_term t. snd e x=initial_env x) ss"
  shows "lp_ieval t eta=lp_ieval t initial_env"
  by (rule lp_ieval_cong) (use precise_seg_captured_actual[OF actual ground known] in auto)


lemma precise_seg_observed_actual:
  assumes actual: "precise_actual_return P (lpc_return_eval eta [(e,map Var vs)]) rho"
  obtains theta where
    "precise_actual_return P [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e,eta)] theta"
    "rho=lpc_return_env (map Var vs) theta"
proof -
  have shape: "lpc_return_eval eta [(e,map Var vs)] =
    lpc_reinterface (lpc_return_env (map Var vs))
      [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e,eta)]"
    by (simp add: lpc_return_eval_def lpc_reinterface_def)
  have observed: "precise_actual_return P
    (lpc_reinterface (lpc_return_env (map Var vs))
      [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e,eta)]) rho"
    using actual by (simp only: shape)
  show ?thesis
    using precise_actual_return_reinterface[where F="lpc_return_env (map Var vs)",
      OF lpc_return_env_commutes observed] that by blast
qed


lemma precise_seg_observed_captured_term:
  assumes actual: "precise_actual_return P (lpc_return_eval eta [(e,map Var vs)]) rho"
    and distinct: "distinct vs"
    and vars: "vars_term t \<subseteq> set vs"
    and finite: "lp_seg_ground (lp_ieval t eta)"
  shows "lp_ieval (lpc_seg_position_template vs t) rho = lp_ieval t eta"
proof -
  obtain theta where source: "precise_actual_return P
      [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e,eta)] theta"
    and rho: "rho=lpc_return_env (map Var vs) theta"
    using precise_seg_observed_actual[OF actual] by blast
  have known: "\<forall>x\<in>vars_term t. lp_seg_ground (eta x)"
    using finite by (simp only: lp_seg_ground_eval)
  have preserved: "lp_ieval t theta=lp_ieval t eta"
    by (rule precise_seg_captured_term[OF source known]) simp
  show ?thesis unfolding rho
    by (simp only: lpc_seg_position_eval[OF distinct vars] preserved)
qed


end
end
