theory LP_Cut_Domain_Return_Output_Groundness
 imports LP_Cut_Domain_Return_Answer_Control
begin

context cut_runtime_domain
begin

theorem precise_success_output_groundness:
  assumes program: "lpc_control_program P Q F"
    and domain: "list_all (lpc_control_goal F) goals"
    and checked: "lp_ground_check Q modes"
    and ground: "\<forall>x\<in>G. lp_seg_ground (\<eta> x)"
    and path: "([(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>)) goals),\<eta>)],ss)
      \<in>(precise_answer_steps P)\<^sup>*"
    and event: "precise_answer_transition P ss (Some \<rho>) tt"
  shows "\<forall>x\<in>lp_ground_flow modes (map lpc_control_atom goals) G.
    lp_seg_ground (\<rho> x)"
proof -
  have answers: "((map (\<lambda>a. lp_atom_eval a \<eta>) (map lpc_control_atom goals),\<eta>),([],\<rho>))
    \<in>(lp_seg_answer_step Q)\<^sup>*"
    using precise_control_successful_answer[OF program lpc_control_eval(1)[OF domain] path event]
    by (simp only: lpc_control_eval(2)[OF domain])
  show ?thesis by (rule lp_ground_check_answers[OF checked answers ground])
qed

lemma precise_actual_return_reinterface:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and actual: "precise_actual_return P (lpc_reinterface F ss) rho"
  shows "\<exists>eta. precise_actual_return P ss eta \<and> rho=F eta"
proof -
  obtain us tail where path: "(lpc_reinterface F ss,us)\<in>(precise_answer_steps P)\<^sup>*"
    and event: "precise_answer_transition P us (Some rho) tail"
    using actual by (auto simp: precise_actual_return_def)
  obtain vs where reached: "(ss,vs)\<in>(precise_answer_steps P)\<^sup>*"
    and shape: "lpc_reinterface F vs=us"
    using precise_reinterface_path_reflect[where F=F, OF commute path] by blast
  obtain ev ws where source: "precise_answer_transition P vs ev ws" and mapped: "map_option F ev=Some rho"
    using precise_reinterface_reflect[where F=F, OF commute, of P vs "Some rho" tail] event shape by blast
  obtain eta where ev: "ev=Some eta" and rho: "rho=F eta" using mapped by (cases ev) auto
  show ?thesis using reached source ev rho by (auto simp: precise_actual_return_def)
qed

theorem precise_return_output_groundness_sound:
  assumes checked: "lpc_check_return_output_groundness P pre G interface positions Q Fs modes"
    and known: "\<forall>x\<in>set G. lp_seg_ground (eta x)"
    and actual: "precise_actual_return P (lpc_return_eval eta [(LPCGoals pre,interface)]) rho"
  shows "\<forall>i\<in>set positions. lp_seg_ground (rho i)"
proof -
  let ?ss = "[(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) pre),eta)]"
  have shape: "lpc_return_eval eta [(LPCGoals pre,interface)] =
    lpc_reinterface (lpc_return_env interface) ?ss"
    by (simp add: lpc_return_eval_def lpc_reinterface_def)
  have mapped: "precise_actual_return P (lpc_reinterface (lpc_return_env interface) ?ss) rho"
    using actual by (simp only: shape)
  obtain theta where source: "precise_actual_return P ?ss theta" and rho: "rho=lpc_return_env interface theta"
    using precise_actual_return_reinterface[where F="lpc_return_env interface", OF lpc_return_env_commutes mapped] by blast
  show ?thesis
  proof (cases "list_all (\<lambda>i. i<length interface \<and> vars_term (interface!i) \<subseteq> set G) positions")
    case True
    have preserved: "\<forall>x\<in>set G. lp_seg_ground (theta x)"
      by (rule precise_actual_return_preserves_ground_env[OF source]) (simp add: known)
    show ?thesis using True preserved
      by (auto simp: list_all_iff rho lpc_return_env_def lp_seg_ground_eval)
  next
    case False
  obtain us tail where path: "(?ss,us)\<in>(precise_answer_steps P)\<^sup>*"
    and event: "precise_answer_transition P us (Some theta) tail"
    using source by (auto simp: precise_actual_return_def)
  have program: "lpc_control_program P Q (set Fs)" and domain: "list_all (lpc_control_goal (set Fs)) pre"
    and modes: "lp_ground_check Q modes"
    using checked False by (auto simp: lpc_check_return_output_groundness_def)
  have outputs: "\<forall>x\<in>lp_ground_flow modes (map lpc_control_atom pre) (set G). lp_seg_ground (theta x)"
    by (rule precise_success_output_groundness[OF program domain modes known path event])
  show ?thesis using checked False outputs
    by (auto simp: lpc_check_return_output_groundness_def list_all_iff rho lpc_return_env_def lp_seg_ground_eval)
  qed
qed


end
end
