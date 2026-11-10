theory LP_Cut_Domain_SEG_Child
 imports LP_Cut_Domain_SEG_Prefix
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

theorem precise_seg_child_lower:
  assumes checked: "lpc_seg_check_child roots pre G guards vs inp outp receipt"
    and program: "lp_cut_source_program P"
    and known: "knowledge (set G) guards eta"
    and finite: "lp_seg_ground (lp_ieval inp eta)"
    and lower: "\<And>us v out. (t,v)\<in>R\<^sup>+ \<Longrightarrow>
      precise_seg_root_rep roots is_cont c d us v out \<Longrightarrow> precise_return_contract P us R v out"
    and strict: "(t,A\<langle>lpc_seg_return_value is_cont c d inp eta\<rangle>)\<in>R\<^sup>+"
  shows "precise_return_contract P (lpc_return_eval eta [(LPCGoals pre,map Var vs)]) R
    (A\<langle>lpc_seg_return_value is_cont c d inp eta\<rangle>)
    (\<lambda>rho. A\<langle>lpc_seg_return_value is_cont c d (lpc_seg_position_template vs outp) rho\<rangle>)"
proof -
  let ?i="lpcsh_target receipt"
  let ?root="roots!?i"
  let ?nd="lpcsr_node ?root"
  let ?mu="lp_cut_instance_subst (lpcsh_bindings receipt)"
  let ?eta="\<lambda>x. lp_ieval (?mu x) eta"
  have index: "?i<length roots" using checked by (simp add: lpc_seg_check_child_def)
  have single: "length (lpcn_state ?nd)=1"
  proof (cases "lpcn_state ?nd")
    case Nil then show ?thesis using checked by (simp add: lpc_seg_check_child_def Let_def)
  next
    case (Cons x xs)
    show ?thesis using checked Cons by (cases xs) (simp_all add: lpc_seg_check_child_def Let_def)
  qed
  obtain child where state: "lpcn_state ?nd=[child]" using single by (cases "lpcn_state ?nd") auto
  have inst: "lpc_seg_check_instance_boundary (LPCGoals pre) G guards vs (map Var vs)
           child (lpcn_ground ?nd) (lpcn_guards ?nd) (lpcn_vars ?nd)
           (lpcsh_bindings receipt) (lpcsh_swaps receipt)"
    and inp: "lpcsr_input ?root\<cdot>?mu=inp"
    and template: "lpc_seg_compose_observation (map (lpc_seg_position_template vs) (map ?mu (lpcn_vars ?nd)))
           (lpcsr_output ?root)=lpc_seg_position_template vs outp"
    using checked by (auto simp: lpc_seg_check_child_def Let_def state)
  have child_known: "knowledge (set (lpcn_ground ?nd)) (lpcn_guards ?nd) ?eta"
    by (rule precise_seg_instance_boundary_knowledge[OF inst known])
  have equal: "lp_ieval (lpcsr_input ?root) ?eta=lp_ieval inp eta"
    using arg_cong[OF inp, of "\<lambda>t. lp_ieval t eta"]
    by (simp only: lp_ieval_finite_subst)
  have child_finite: "lp_seg_ground (lp_ieval (lpcsr_input ?root) ?eta)"
    using finite by (simp only: equal)
  have child_strict: "(t,A\<langle>lpc_seg_return_value is_cont c d (lpcsr_input ?root) ?eta\<rangle>)\<in>R\<^sup>+"
    using strict by (simp only: lpc_seg_return_value_def equal)
  have child_contract: "precise_return_contract P (lpc_return_eval ?eta [(child,map Var (lpcn_vars ?nd))]) R
    (A\<langle>lpc_seg_return_value is_cont c d inp eta\<rangle>)
    (\<lambda>rho. A\<langle>lpc_seg_return_value is_cont c d (lpcsr_output ?root) rho\<rangle>)"
    using precise_seg_root_lower[OF lower index child_known child_finite child_strict]
    by (simp add: lpc_seg_root_state_def state lpc_seg_return_value_def equal)
  show ?thesis by (rule precise_seg_prefix_instance_contract[OF inst program known child_contract template])
qed


end
end
