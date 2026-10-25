theory LP_Cut_SEG_Prefix
  imports LP_Cut_SEG_Connection_Check
begin

text \<open>A Split prefix keeps the full parent answer interface while its
recursive contract is looked up at an independently addressed child root.
No return-rule step is needed until the prefix actually returns.\<close>

theorem lpc_seg_prefix_instance_contract:
  assumes inst: "lpc_seg_check_instance_boundary (LPCGoals pre) G guards vs (map Var vs)
      child H guards' child_vars bindings swaps"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set G) guards eta"
    and child_contract: "lpc_return_contract P
      (lpc_return_eval (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) eta)
        [(child,map Var child_vars)]) R t
      (\<lambda>rho. A\<langle>lpc_seg_return_value is_cont c d child_tmpl rho\<rangle>)"
    and template: "lpc_seg_compose_observation
      (map (lpc_seg_position_template vs) (map (lp_cut_instance_subst bindings) child_vars)) child_tmpl = outp"
  shows "lpc_return_contract P (lpc_return_eval eta [(LPCGoals pre,map Var vs)]) R t
    (\<lambda>rho. A\<langle>lpc_seg_return_value is_cont c d outp rho\<rangle>)"
proof -
  have distinct: "distinct vs"
    using inst by (simp add: lpc_seg_check_instance_boundary_def Let_def)
  show ?thesis
  proof (rule lpc_seg_checked_instance_contract[OF inst program known child_contract rtrancl_refl])
    fix us tail rho
    assume path: "(lpc_return_eval eta [(LPCGoals pre,map Var vs)],us)\<in>(lpc_answer_steps P)\<^sup>*"
      and event: "lpc_answer_transition P us (Some rho) tail"
      and residual: "(t,A\<langle>lpc_seg_return_value is_cont c d child_tmpl
        (lpc_seg_observe (map (lpc_seg_position_template vs)
          (map (lp_cut_instance_subst bindings) child_vars)) rho)\<rangle>)\<in>R\<^sup>*"
    have actual: "lpc_actual_return P (lpc_return_eval eta [(LPCGoals pre,map Var vs)]) rho"
      using path event by (auto simp: lpc_actual_return_def)
    have id_observation: "lpc_seg_observe (map (lpc_seg_position_template vs) (map Var vs)) rho = rho"
    proof -
      obtain theta where rho: "rho=lpc_return_env (map Var vs) theta"
        by (rule lpc_seg_observed_actual[OF actual]) assumption
      show ?thesis unfolding rho
        by (rule lpc_seg_observe_environment[OF distinct]) auto
    qed
    show "(A\<langle>lpc_seg_return_value is_cont c d child_tmpl
        (lpc_seg_observe (map (lpc_seg_position_template vs)
          (map (lp_cut_instance_subst bindings) child_vars)) rho)\<rangle>,
      A\<langle>lpc_seg_return_value is_cont c d outp
        (lpc_seg_observe (map (lpc_seg_position_template vs) (map Var vs)) rho)\<rangle>)\<in>R\<^sup>*"
      by (simp only: id_observation lpc_seg_return_value_def lpc_seg_observation_eval template)
  qed
qed

end
