theory LP_Cut_Domain_SEG_Projected_Connection
 imports LP_Cut_Domain_SEG_Projected_Return
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

theorem precise_seg_projected_connection_contract:
  fixes filtering :: "'g afs" and ms :: "('g,string) term list"
    and c d u eta captured
  defines "ctxtD \<equiv> \<lambda>x. LPIFun (c u) (x#map (\<lambda>t. map_lp_iterm d id (lp_ieval t eta)) captured)"
  assumes inst: "lpc_seg_check_instance_boundary (LPCGoals pre) G guards vs observed
      child H guards' child_vars bindings swaps"
    and program: "lp_cut_source_program P"
    and known: "knowledge (set G) guards eta"
    and leave: "lpc_seg_check_projected_pair filtering 2 1 is_cont c d R
      (Fun u (child_out#captured)) parent_out"
    and cont: "is_cont u"
    and child_vars: "vars_term child_out \<subseteq> set vs"
    and parent_vars: "vars_term parent_out \<subseteq> set vs"
    and af: "afs filtering (c u,Suc (length captured)) = AFList (0#map Suc indices)"
    and captured_pr: "list_all2 (\<lambda>i m. i<length captured \<and>
      lp_iproject filtering (map_lp_iterm d id (lp_ieval (captured!i) eta)) m) indices ms"
    and child_template: "lpc_seg_compose_observation
      (map (lpc_seg_position_template vs) (map (lp_cut_instance_subst bindings) child_vars)) child_tmpl =
        lpc_seg_position_template vs child_out"
    and parent_template: "lpc_seg_compose_observation
      (map (lpc_seg_position_template vs) observed) parent_tmpl = lpc_seg_position_template vs parent_out"
    and entry: "(t,A (ctxtD child_in))\<in>(lpc_seg_projected_rel filtering R)\<^sup>*"
    and initial: "lpc_seg_has_projection filtering (A (ctxtD child_in))"
    and ambient: "lpc_seg_projection_context filtering A"
    and child_contract: "precise_return_contract P
      (lpc_return_eval (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) eta)
        [(child,map Var child_vars)]) (lpc_seg_projected_rel filtering R)
      (A (ctxtD child_in)) (\<lambda>rho. A (ctxtD (lpc_seg_runtime_value is_cont c d child_tmpl rho)))"
  shows "precise_return_contract P (lpc_return_eval eta [(LPCGoals pre,observed)])
    (lpc_seg_projected_rel filtering R) t
    (\<lambda>rho. A (lpc_seg_runtime_value is_cont c d parent_tmpl rho))"
proof (rule precise_seg_checked_instance_contract[OF inst program known child_contract entry])
  fix us tail rho
  let ?cf = "lpc_seg_observe (map (lpc_seg_position_template vs)
    (map (lp_cut_instance_subst bindings) child_vars))"
  let ?pf = "lpc_seg_observe (map (lpc_seg_position_template vs) observed)"
  assume path: "(lpc_return_eval eta [(LPCGoals pre,map Var vs)],us)\<in>(precise_answer_steps P)\<^sup>*"
    and event: "precise_answer_transition P us (Some rho) tail"
    and reached: "(A (ctxtD child_in),A (ctxtD (lpc_seg_runtime_value is_cont c d child_tmpl (?cf rho))))
      \<in>(lpc_seg_projected_rel filtering R)\<^sup>*"
  have actual: "precise_actual_return P (lpc_return_eval eta [(LPCGoals pre,map Var vs)]) rho"
    using path event by (auto simp: precise_actual_return_def)
  have distinct: "distinct vs" using inst by (simp add: lpc_seg_check_instance_boundary_def Let_def)
  have finite: "lpc_seg_has_projection filtering
    (ctxtD (lpc_seg_runtime_value is_cont c d child_tmpl (?cf rho)))"
    by (rule lpc_seg_projection_context_reflect[OF ambient lpc_seg_projected_reachable[OF reached initial]])
  have af': "afs filtering (c u,Suc (length (map (\<lambda>t. map_lp_iterm d id (lp_ieval t eta)) captured)))
    = AFList (0#map Suc indices)" using af by simp
  have child_finite: "lpc_seg_has_projection filtering (lpc_seg_runtime_value is_cont c d child_tmpl (?cf rho))"
    by (rule lpc_seg_projected_pending_child[OF af']) (use finite in \<open>simp only: ctxtD_def\<close>)
  obtain n :: "('g,string) term" where child_pr: "lp_iproject filtering
    (lpc_seg_role_value 1 is_cont c d (lp_ieval (lpc_seg_position_template vs child_out) rho)) n"
    using child_finite
    by (simp only: lpc_seg_has_projection_def lpc_seg_runtime_value_def
      lpc_seg_observation_eval child_template) blast
  have local: "(ctxtD (lpc_seg_runtime_value is_cont c d child_tmpl (?cf rho)),
      lpc_seg_runtime_value is_cont c d parent_tmpl (?pf rho))\<in>lpc_seg_projected_rel filtering R"
    using precise_seg_projected_actual_return[OF leave cont actual distinct child_vars parent_vars af captured_pr child_pr]
    by (simp only: ctxtD_def lpc_seg_runtime_value_def lpc_seg_observation_eval child_template parent_template)
  show "(A (ctxtD (lpc_seg_runtime_value is_cont c d child_tmpl (?cf rho))),
    A (lpc_seg_runtime_value is_cont c d parent_tmpl (?pf rho)))\<in>(lpc_seg_projected_rel filtering R)\<^sup>*"
    by (rule r_into_rtrancl[OF lpc_seg_projection_context_step[OF ambient local]])
qed


end
end
