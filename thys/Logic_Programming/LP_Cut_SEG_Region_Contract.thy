theory LP_Cut_SEG_Region_Contract
  imports LP_Cut_SEG_Control LP_Cut_SEG_Emit
begin

text \<open>Connect checked finite source-control regions to their extracted
return rules. The return obligation is discharged by the finite syntactic
template/rule check, rather than supplied as a semantic assumption. Open
recursive boundaries remain explicit premises for the outer residual induction.
\<close>

theorem lpc_seg_region_contract:
  fixes P :: "('f,string) lp_cut_program"
    and a :: "('f lp_cut_symbol,string) lp_iatom"
  assumes checked: "lpc_seg_check_control fuel P Q nds states returned arity actions"
    and ranked: "lpc_seg_ranked_control rank_of Q"
    and program: "lp_cut_source_program P"
    and represented: "lpc_return_module_rep nds states ss [a]"
    and preserved: "lpc_seg_template_program_on active templates Q"
    and emits: "lpc_seg_check_emits templates returned outp R Q"
    and not_returned: "fst a\<noteq>returned"
    and finite: "lp_seg_ground (lpc_seg_template_value templates a)"
    and normal: "\<forall>s\<lhd>lpc_seg_finite_value (lpc_seg_template_value templates a). s\<in>NF_terms N"
    and boundary: "\<And>i eta. i<length nds \<Longrightarrow> actions!i=None \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
      ([a],[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))])\<in>(lp_ild Q)\<^sup>* \<Longrightarrow>
      lpc_return_contract P (lpc_return_eval eta (states!i)) (qrstep False N R)
        (lpc_seg_finite_value (lpc_seg_template_value templates a))
        (\<lambda>rho. lpc_seg_finite_value (lpc_seg_template_value (\<lambda>_. outp)
          (returned,map rho [0..<arity])))"
  shows "lpc_return_contract P ss (qrstep False N R)
    (lpc_seg_finite_value (lpc_seg_template_value templates a))
    (\<lambda>rho. lpc_seg_finite_value (lpc_seg_template_value (\<lambda>_. outp)
      (returned,map rho [0..<arity])))"
proof (rule lpc_seg_control_contract[OF checked ranked program represented boundary])
  fix rho
  assume path: "([a],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*"
  have step: "(lpc_seg_finite_value (lpc_seg_template_value templates a),
    lpc_seg_finite_value (lpc_seg_template_value (\<lambda>_. outp)
      (returned,map rho [0..<arity])))\<in>qrstep False N R"
    by (rule lpc_seg_emit_path[OF preserved emits not_returned path finite normal])
  show "(lpc_seg_finite_value (lpc_seg_template_value templates a),
    lpc_seg_finite_value (lpc_seg_template_value (\<lambda>_. outp)
      (returned,map rho [0..<arity])))\<in>(qrstep False N R)\<^sup>*"
    by (rule r_into_rtrancl[OF step])
qed

end
