theory LP_Cut_Output_Groundness
  imports LP_Answer_Groundness LP_Cut_Answer_Knowledge LP_Cut_Control_Check
begin

text \<open>Output groundness is a property of successful returns, independently
of prefix termination. In particular the cut-erased approximation need not be
terminating. Actual cuts, saved alternatives and their private environments
remain in the source path. Failure and barrier removal cannot supply an answer.\<close>

theorem lpc_success_output_groundness:
  assumes program: "lpc_control_program P Q F"
    and domain: "list_all (lpc_control_goal F) goals"
    and checked: "lp_ground_check Q modes"
    and ground: "\<forall>x\<in>G. lp_seg_ground (\<eta> x)"
    and path: "([(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>)) goals),\<eta>)],ss)
      \<in>(lpc_answer_steps P)\<^sup>*"
    and event: "lpc_answer_transition P ss (Some \<rho>) tt"
  shows "\<forall>x\<in>lp_ground_flow modes (map lpc_control_atom goals) G.
    lp_seg_ground (\<rho> x)"
proof -
  have answers: "((map (\<lambda>a. lp_atom_eval a \<eta>) (map lpc_control_atom goals),\<eta>),([],\<rho>))
    \<in>(lp_seg_answer_step Q)\<^sup>*"
    using lpc_control_successful_answer[OF program lpc_control_eval(1)[OF domain] path event]
    by (simp only: lpc_control_eval(2)[OF domain])
  show ?thesis by (rule lp_ground_check_answers[OF checked answers ground])
qed

theorem lpc_answer_knowledge_outputs:
  assumes checked: "lp_ground_check Q modes"
    and path: "((map (\<lambda>a. lp_atom_eval a \<eta>) goals,\<eta>),([],\<rho>))
      \<in>(lp_seg_answer_step Q)\<^sup>*"
    and known: "lp_cut_knowledge G K \<eta>"
    and grounds: "G' \<subseteq> lp_ground_flow modes goals G"
    and guards: "set K' \<subseteq> set (filter lpc_answer_negative_guard K)"
  shows "lp_cut_knowledge G' K' \<rho>"
proof -
  have ground: "\<forall>x\<in>G. lp_seg_ground (\<eta> x)"
    using known by (simp add: lp_cut_knowledge_def)
  have outputs: "\<forall>x\<in>lp_ground_flow modes goals G. lp_seg_ground (\<rho> x)"
    by (rule lp_ground_check_answers[OF checked path ground])
  have keep: "lp_cut_knowledge G K' \<rho>"
    by (rule lpc_answer_knowledge_preserved[OF path known subset_refl guards])
  show ?thesis using outputs keep grounds by (auto simp: lp_cut_knowledge_def)
qed

end
