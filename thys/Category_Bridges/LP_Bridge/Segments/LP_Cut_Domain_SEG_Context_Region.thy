theory LP_Cut_Domain_SEG_Context_Region
 imports LP_Cut_Domain_SEG_Encoded_Emit
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

theorem precise_seg_context_region_contract:
  assumes checked: "lpc_seg_check_control fuel P Q nds states returned arity actions"
    and ranked: "lpc_seg_ranked_control rank_of Q"
    and program: "lp_cut_source_program P"
    and represented: "precise_return_module_rep nds states ss [a]"
    and preserved: "lpc_seg_template_program_on active templates Q"
    and emits: "lpc_seg_check_encoded_emits templates returned outp is_cont c d C R Q"
    and not_returned: "fst a\<noteq>returned"
    and finite: "lp_seg_ground (lpc_seg_template_value templates a)"
    and out_vars: "vars_term outp \<subseteq> set [0..<arity]"
    and range: "range d \<subseteq> C"
    and roots: "\<And>q. q\<in>N \<Longrightarrow> \<exists>g us. q=Fun g us \<and> g\<notin>C"
    and boundary: "\<And>i eta. i<length nds \<Longrightarrow> actions!i=None \<Longrightarrow>
      knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
      ([a],[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))])\<in>(lp_ild Q)\<^sup>* \<Longrightarrow>
      precise_return_contract P (lpc_return_eval eta (states!i)) (qrstep False N R)
        (A\<langle>lpc_seg_finite_value (lpc_seg_role_value 1 is_cont c d (lpc_seg_template_value templates a))\<rangle>)
        (\<lambda>rho. A\<langle>lpc_seg_return_value is_cont c d outp rho\<rangle>)"
  shows "precise_return_contract P ss (qrstep False N R)
    (A\<langle>lpc_seg_finite_value (lpc_seg_role_value 1 is_cont c d (lpc_seg_template_value templates a))\<rangle>)
    (\<lambda>rho. A\<langle>lpc_seg_return_value is_cont c d outp rho\<rangle>)"
proof (rule precise_seg_control_contract[OF checked ranked program represented boundary])
  fix rho assume path: "([a],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*"
  have step: "(lpc_seg_finite_value (lpc_seg_role_value 1 is_cont c d (lpc_seg_template_value templates a)),
    lpc_seg_return_value is_cont c d outp rho)\<in>qrstep False N R"
    using lpc_seg_encoded_emit_path[where N=N, OF preserved emits not_returned path finite range roots]
    by (simp only: lpc_seg_output_template[OF out_vars] lpc_seg_return_value_def)
  show "(A\<langle>lpc_seg_finite_value (lpc_seg_role_value 1 is_cont c d (lpc_seg_template_value templates a))\<rangle>,
    A\<langle>lpc_seg_return_value is_cont c d outp rho\<rangle>)\<in>(qrstep False N R)\<^sup>*"
    by (rule r_into_rtrancl[OF qrstep.ctxt[OF step]])
qed


end
end
