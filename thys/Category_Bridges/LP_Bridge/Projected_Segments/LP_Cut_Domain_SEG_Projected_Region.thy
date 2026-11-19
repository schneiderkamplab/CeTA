theory LP_Cut_Domain_SEG_Projected_Region
 imports LP_Cut_Domain_SEG_Projected_Connection
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

theorem precise_seg_projected_control_contract:
  assumes checked: "lpc_seg_free_check_control fuel P Q nds states Fs returned arity actions"
    and ranked: "lpc_seg_ranked_control rank_of Q"
    and program: "lp_cut_source_program P"
    and represented: "precise_return_free_module_rep nds states Fs ss [a]"
    and preserved: "lpc_seg_projected_template_program filtering is_cont c d active templates Q"
    and emits: "lpc_seg_check_projected_emits filtering templates returned outp is_cont c d R Q"
    and not_returned: "fst a\<noteq>returned"
    and observed: "lpc_seg_has_projection filtering (lpc_seg_role_value 1 is_cont c d (lpc_seg_template_value templates a))"
    and out_vars: "vars_term outp \<subseteq> set [0..<arity]"
    and ambient: "lpc_seg_projection_context filtering A"
    and boundary: "\<And>i eta. i<length nds \<Longrightarrow> actions!i=None \<Longrightarrow>
      knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
      lpc_free_knowledge (set (Fs!i)) eta \<Longrightarrow>
      ([a],[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))])\<in>(lp_ild Q)\<^sup>* \<Longrightarrow>
      precise_return_contract P (lpc_return_eval eta (states!i)) (lpc_seg_projected_rel filtering R)
        (A (lpc_seg_role_value 1 is_cont c d (lpc_seg_template_value templates a)))
        (\<lambda>rho. A (lpc_seg_runtime_value is_cont c d outp rho))"
  shows "precise_return_contract P ss (lpc_seg_projected_rel filtering R)
    (A (lpc_seg_role_value 1 is_cont c d (lpc_seg_template_value templates a)))
    (\<lambda>rho. A (lpc_seg_runtime_value is_cont c d outp rho))"
proof (rule precise_seg_free_control_contract[OF checked ranked program represented boundary])
  fix rho assume path: "([a],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*"
  have edge: "(lpc_seg_role_value 1 is_cont c d (lpc_seg_template_value templates a),
    lpc_seg_runtime_value is_cont c d outp rho)\<in>lpc_seg_projected_rel filtering R"
    using lpc_seg_projected_emit_path[OF preserved emits not_returned path observed]
    by (simp only: lpc_seg_output_template[OF out_vars] lpc_seg_runtime_value_def)
  show "(A (lpc_seg_role_value 1 is_cont c d (lpc_seg_template_value templates a)),
    A (lpc_seg_runtime_value is_cont c d outp rho))\<in>(lpc_seg_projected_rel filtering R)\<^sup>*"
    by (rule r_into_rtrancl[OF lpc_seg_projection_context_step[OF ambient edge]])
qed


end
end
