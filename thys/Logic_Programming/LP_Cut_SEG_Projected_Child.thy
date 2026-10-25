theory LP_Cut_SEG_Projected_Child
  imports LP_Cut_SEG_Projected_Root LP_Cut_SEG_Free_Child
begin

theorem lpc_seg_projected_prefix_contract:
  assumes inst: "lpc_seg_check_instance_boundary (LPCGoals pre) G guards vs (map Var vs)
      child H guards' child_vars bindings swaps"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set G) guards eta"
    and child_contract: "lpc_return_contract P
      (lpc_return_eval (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) eta)
        [(child,map Var child_vars)]) R t
      (\<lambda>rho. A (lpc_seg_runtime_value is_cont c d child_tmpl rho))"
    and template: "lpc_seg_compose_observation
      (map (lpc_seg_position_template vs) (map (lp_cut_instance_subst bindings) child_vars)) child_tmpl = outp"
  shows "lpc_return_contract P (lpc_return_eval eta [(LPCGoals pre,map Var vs)]) R t
    (\<lambda>rho. A (lpc_seg_runtime_value is_cont c d outp rho))"
proof -
  have distinct: "distinct vs" using inst by (simp add: lpc_seg_check_instance_boundary_def Let_def)
  show ?thesis
  proof (rule lpc_seg_checked_instance_contract[OF inst program known child_contract rtrancl_refl])
    fix us tail rho
    assume path: "(lpc_return_eval eta [(LPCGoals pre,map Var vs)],us)\<in>(lpc_answer_steps P)\<^sup>*"
      and event: "lpc_answer_transition P us (Some rho) tail"
      and residual: "(t,A (lpc_seg_runtime_value is_cont c d child_tmpl
        (lpc_seg_observe (map (lpc_seg_position_template vs)
          (map (lp_cut_instance_subst bindings) child_vars)) rho)))\<in>R\<^sup>*"
    have actual: "lpc_actual_return P (lpc_return_eval eta [(LPCGoals pre,map Var vs)]) rho"
      using path event by (auto simp: lpc_actual_return_def)
    have identity: "lpc_seg_observe (map (lpc_seg_position_template vs) (map Var vs)) rho=rho"
    proof -
      obtain theta where rho: "rho=lpc_return_env (map Var vs) theta"
        by (rule lpc_seg_observed_actual[OF actual]) assumption
      show ?thesis unfolding rho by (rule lpc_seg_observe_environment[OF distinct]) auto
    qed
    show "(A (lpc_seg_runtime_value is_cont c d child_tmpl
        (lpc_seg_observe (map (lpc_seg_position_template vs)
          (map (lp_cut_instance_subst bindings) child_vars)) rho)),
      A (lpc_seg_runtime_value is_cont c d outp
        (lpc_seg_observe (map (lpc_seg_position_template vs) (map Var vs)) rho)))\<in>R\<^sup>*"
      by (simp only: identity lpc_seg_runtime_value_def lpc_seg_observation_eval template)
  qed
qed

theorem lpc_seg_projected_child_lower:
  assumes checked: "lpc_seg_free_check_child fuel roots Fs pre G F guards vs inp outp receipt"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set G) guards eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpc_seg_has_projection filtering (lpc_seg_runtime_value is_cont c d inp eta)"
    and ambient: "lpc_seg_projection_context filtering A"
    and lower: "\<And>us v out. (t,v)\<in>R\<^sup>+ \<Longrightarrow>
      lpc_seg_projected_root_rep filtering roots Fs is_cont c d us v out \<Longrightarrow>
      lpc_return_contract P us R v out"
    and strict: "(t,A (lpc_seg_runtime_value is_cont c d inp eta))\<in>R\<^sup>+"
  shows "lpc_return_contract P (lpc_return_eval eta [(LPCGoals pre,map Var vs)]) R
    (A (lpc_seg_runtime_value is_cont c d inp eta))
    (\<lambda>rho. A (lpc_seg_runtime_value is_cont c d (lpc_seg_position_template vs outp) rho))"
proof -
  let ?i="lpcsh_target receipt"
  let ?root="roots!?i"
  let ?nd="lpcsr_node ?root"
  let ?mu="lp_cut_instance_subst (lpcsh_bindings receipt)"
  let ?eta="\<lambda>x. lp_ieval (?mu x) eta"
  have index: "?i<length roots" using checked by (simp add: lpc_seg_free_check_child_def lpc_seg_check_child_def)
  have single: "length (lpcn_state ?nd)=1"
  proof (cases "lpcn_state ?nd")
    case Nil then show ?thesis using checked by (simp add: lpc_seg_free_check_child_def lpc_seg_check_child_def Let_def)
  next
    case (Cons x xs)
    show ?thesis using checked Cons by (cases xs) (simp_all add: lpc_seg_free_check_child_def lpc_seg_check_child_def Let_def)
  qed
  obtain child where state: "lpcn_state ?nd=[child]" using single by (cases "lpcn_state ?nd") auto
  have inst: "lpc_seg_check_instance_boundary (LPCGoals pre) G guards vs (map Var vs)
      child (lpcn_ground ?nd) (lpcn_guards ?nd) (lpcn_vars ?nd)
      (lpcsh_bindings receipt) (lpcsh_swaps receipt)"
    and inp: "lpcsr_input ?root\<cdot>?mu=inp"
    and template: "lpc_seg_compose_observation (map (lpc_seg_position_template vs) (map ?mu (lpcn_vars ?nd)))
      (lpcsr_output ?root)=lpc_seg_position_template vs outp"
    using checked by (auto simp: lpc_seg_free_check_child_def lpc_seg_check_child_def Let_def state)
  have child_known: "lp_cut_knowledge (set (lpcn_ground ?nd)) (lpcn_guards ?nd) ?eta"
    by (rule lpc_seg_instance_boundary_knowledge[OF inst known])
  have equal: "lpc_seg_runtime_value is_cont c d (lpcsr_input ?root) ?eta=lpc_seg_runtime_value is_cont c d inp eta"
    using arg_cong[OF inp, of "\<lambda>t. lp_ieval t eta"]
    by (simp only: lpc_seg_runtime_value_def lp_ieval_finite_subst)
  have child_observed: "lpc_seg_has_projection filtering (lpc_seg_runtime_value is_cont c d (lpcsr_input ?root) ?eta)"
    using observed by (simp only: equal)
  have child_strict: "(t,A (lpc_seg_runtime_value is_cont c d (lpcsr_input ?root) ?eta))\<in>R\<^sup>+"
    using strict by (simp only: equal)
  have free_check: "lpc_check_link_free fuel [] F (Fs!?i) (lpcsh_bindings receipt)"
    using checked by (simp add: lpc_seg_free_check_child_def)
  have child_free: "lpc_free_knowledge (set (Fs!?i)) ?eta"
    by (rule lpc_checked_link_free_sound[OF free_check _ free]) (simp add: lp_equations_def)
  have child_contract: "lpc_return_contract P (lpc_return_eval ?eta [(child,map Var (lpcn_vars ?nd))]) R
    (A (lpc_seg_runtime_value is_cont c d inp eta))
    (\<lambda>rho. A (lpc_seg_runtime_value is_cont c d (lpcsr_output ?root) rho))"
    using lower[OF child_strict lpc_seg_projected_root_repI[OF index child_known child_free child_observed ambient]]
    by (simp add: lpc_seg_root_state_def state equal)
  show ?thesis by (rule lpc_seg_projected_prefix_contract[OF inst program known child_contract template])
qed

end
