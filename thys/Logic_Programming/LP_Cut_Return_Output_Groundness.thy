theory LP_Cut_Return_Output_Groundness
  imports LP_Cut_Return_Preserved_Ground LP_Cut_Output_Groundness
begin

lemma lpc_return_env_commutes:
  "lpc_return_env ts (\<lambda>x. lp_isubst (eta x) sigma) =
    (\<lambda>i. lp_isubst (lpc_return_env ts eta i) sigma)"
  by (rule ext) (simp add: lpc_return_env_def lp_ieval_subst)

lemma lpc_actual_return_reinterface:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and actual: "lpc_actual_return P (lpc_reinterface F ss) rho"
  shows "\<exists>eta. lpc_actual_return P ss eta \<and> rho=F eta"
proof -
  obtain us tail where path: "(lpc_reinterface F ss,us)\<in>(lpc_answer_steps P)\<^sup>*"
    and event: "lpc_answer_transition P us (Some rho) tail"
    using actual by (auto simp: lpc_actual_return_def)
  obtain vs where reached: "(ss,vs)\<in>(lpc_answer_steps P)\<^sup>*"
    and shape: "lpc_reinterface F vs=us"
    using lpc_reinterface_path_reflect[where F=F, OF commute path] by blast
  obtain ev ws where source: "lpc_answer_transition P vs ev ws" and mapped: "map_option F ev=Some rho"
    using lpc_reinterface_reflect[where F=F, OF commute, of P vs "Some rho" tail] event shape by blast
  obtain eta where ev: "ev=Some eta" and rho: "rho=F eta" using mapped by (cases ev) auto
  show ?thesis using reached source ev rho by (auto simp: lpc_actual_return_def)
qed

definition lpc_check_return_output_groundness where
  "lpc_check_return_output_groundness P pre G interface positions Q Fs modes =
    (list_all (\<lambda>i. i<length interface \<and> vars_term (interface!i) \<subseteq> set G) positions \<or>
     (lpc_control_program P Q (set Fs) \<and> list_all (lpc_control_goal (set Fs)) pre \<and>
     lp_ground_check Q modes \<and>
     list_all (\<lambda>i. i<length interface \<and>
       vars_term (interface!i) \<subseteq> lp_ground_flow modes (map lpc_control_atom pre) (set G)) positions))"

theorem lpc_return_output_groundness_sound:
  assumes checked: "lpc_check_return_output_groundness P pre G interface positions Q Fs modes"
    and known: "\<forall>x\<in>set G. lp_seg_ground (eta x)"
    and actual: "lpc_actual_return P (lpc_return_eval eta [(LPCGoals pre,interface)]) rho"
  shows "\<forall>i\<in>set positions. lp_seg_ground (rho i)"
proof -
  let ?ss = "[(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) pre),eta)]"
  have shape: "lpc_return_eval eta [(LPCGoals pre,interface)] =
    lpc_reinterface (lpc_return_env interface) ?ss"
    by (simp add: lpc_return_eval_def lpc_reinterface_def)
  have mapped: "lpc_actual_return P (lpc_reinterface (lpc_return_env interface) ?ss) rho"
    using actual by (simp only: shape)
  obtain theta where source: "lpc_actual_return P ?ss theta" and rho: "rho=lpc_return_env interface theta"
    using lpc_actual_return_reinterface[where F="lpc_return_env interface", OF lpc_return_env_commutes mapped] by blast
  show ?thesis
  proof (cases "list_all (\<lambda>i. i<length interface \<and> vars_term (interface!i) \<subseteq> set G) positions")
    case True
    have preserved: "\<forall>x\<in>set G. lp_seg_ground (theta x)"
      by (rule lpc_actual_return_preserves_ground_env[OF source]) (simp add: known)
    show ?thesis using True preserved
      by (auto simp: list_all_iff rho lpc_return_env_def lp_seg_ground_eval)
  next
    case False
  obtain us tail where path: "(?ss,us)\<in>(lpc_answer_steps P)\<^sup>*"
    and event: "lpc_answer_transition P us (Some theta) tail"
    using source by (auto simp: lpc_actual_return_def)
  have program: "lpc_control_program P Q (set Fs)" and domain: "list_all (lpc_control_goal (set Fs)) pre"
    and modes: "lp_ground_check Q modes"
    using checked False by (auto simp: lpc_check_return_output_groundness_def)
  have outputs: "\<forall>x\<in>lp_ground_flow modes (map lpc_control_atom pre) (set G). lp_seg_ground (theta x)"
    by (rule lpc_success_output_groundness[OF program domain modes known path event])
  show ?thesis using checked False outputs
    by (auto simp: lpc_check_return_output_groundness_def list_all_iff rho lpc_return_env_def lp_seg_ground_eval)
  qed
qed

end
