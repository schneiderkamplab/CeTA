theory LP_Cut_Domain_SEG_Connection
 imports LP_Cut_Domain_SEG_Return_Bridge
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

theorem precise_seg_connection_contract:
  assumes inst: "lpc_seg_check_instance_boundary (LPCGoals pre) G guards vs observed
      child H guards' child_vars bindings swaps"
    and program: "lp_cut_source_program P"
    and known: "knowledge (set G) guards eta"
    and enter: "lpc_seg_check_encoded_pair 1 2 is_cont c d C R l (Fun u (child_in#captured))"
    and leave: "lpc_seg_check_encoded_pair 2 1 is_cont c d C R (Fun u (child_out#captured)) parent_out"
    and cont: "is_cont u"
    and finite: "lp_seg_ground (lp_ieval l eta)"
    and child_vars: "vars_term child_out \<subseteq> set vs"
    and parent_vars: "vars_term parent_out \<subseteq> set vs"
    and ground_check: "lpc_seg_check_return_ground P pre G vs child_out ground_program Fs modes"
    and child_template: "lpc_seg_compose_observation
      (map (lpc_seg_position_template vs) (map (lp_cut_instance_subst bindings) child_vars)) child_tmpl =
        lpc_seg_position_template vs child_out"
    and parent_template: "lpc_seg_compose_observation
      (map (lpc_seg_position_template vs) observed) parent_tmpl = lpc_seg_position_template vs parent_out"
    and ctxt_shape: "ctxtD=More (c u) [] \<box>
      (map (\<lambda>t. lpc_seg_finite_value (map_lp_iterm d id (lp_ieval t eta))) captured)"
    and child_contract: "precise_return_contract P
      (lpc_return_eval (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) eta)
        [(child,map Var child_vars)]) (qrstep False Q R)
      (A\<langle>ctxtD\<langle>lpc_seg_return_value is_cont c d child_in eta\<rangle>\<rangle>)
      (\<lambda>rho. A\<langle>ctxtD\<langle>lpc_seg_return_value is_cont c d child_tmpl rho\<rangle>\<rangle>)"
    and range: "range d \<subseteq> C"
    and roots: "\<And>q. q\<in>Q \<Longrightarrow> \<exists>g us. q=Fun g us \<and> g\<notin>C"
  shows "precise_return_contract P (lpc_return_eval eta [(LPCGoals pre,observed)]) (qrstep False Q R)
    (A\<langle>lpc_seg_return_value is_cont c d l eta\<rangle>)
    (\<lambda>rho. A\<langle>lpc_seg_return_value is_cont c d parent_tmpl rho\<rangle>)"
proof -
  have call: "lp_seg_ground (lp_ieval child_in eta) \<and>
    list_all (\<lambda>t. lp_seg_ground (lp_ieval t eta)) captured \<and>
    (lpc_seg_return_value is_cont c d l eta,ctxtD\<langle>lpc_seg_return_value is_cont c d child_in eta\<rangle>)\<in>qrstep False Q R"
    using lpc_seg_checked_call[where Q=Q, OF enter cont finite range roots]
    by (simp only: ctxt_shape lpc_seg_return_value_def)
  have entry_step: "(A\<langle>lpc_seg_return_value is_cont c d l eta\<rangle>,
    A\<langle>ctxtD\<langle>lpc_seg_return_value is_cont c d child_in eta\<rangle>\<rangle>)\<in>qrstep False Q R"
    by (rule qrstep.ctxt) (use call in blast)
  have distinct: "distinct vs" using inst by (simp add: lpc_seg_check_instance_boundary_def Let_def)
  have ground: "\<forall>x\<in>set G. lp_seg_ground (eta x)"
    using known by (simp add: knowledge_def)
  show ?thesis
  proof (rule precise_seg_checked_instance_contract[OF inst program known child_contract r_into_rtrancl[OF entry_step]])
    fix us tail rho
    assume path: "(lpc_return_eval eta [(LPCGoals pre,map Var vs)],us)\<in>(precise_answer_steps P)\<^sup>*"
      and event: "precise_answer_transition P us (Some rho) tail"
      and child_path: "(A\<langle>ctxtD\<langle>lpc_seg_return_value is_cont c d child_in eta\<rangle>\<rangle>,
        A\<langle>ctxtD\<langle>lpc_seg_return_value is_cont c d child_tmpl
          (lpc_seg_observe (map (lpc_seg_position_template vs)
            (map (lp_cut_instance_subst bindings) child_vars)) rho)\<rangle>\<rangle>)\<in>(qrstep False Q R)\<^sup>*"
    have actual: "precise_actual_return P (lpc_return_eval eta [(LPCGoals pre,map Var vs)]) rho"
      using path event by (auto simp: precise_actual_return_def)
    have child_finite: "lp_seg_ground (lp_ieval (lpc_seg_position_template vs child_out) rho)"
      by (rule precise_seg_checked_return_ground[OF ground_check ground actual])
    have captured: "list_all (\<lambda>t. lp_seg_ground (lp_ieval t eta)) captured" using call by blast
    have local: "(ctxtD\<langle>lpc_seg_return_value is_cont c d (lpc_seg_position_template vs child_out) rho\<rangle>,
      lpc_seg_return_value is_cont c d (lpc_seg_position_template vs parent_out) rho)\<in>qrstep False Q R"
      using precise_seg_checked_actual_return[where Q=Q, OF leave cont actual distinct child_vars parent_vars child_finite captured range roots]
      by (simp only: ctxt_shape lpc_seg_return_value_def)
    have lifted: "(A\<langle>ctxtD\<langle>lpc_seg_return_value is_cont c d (lpc_seg_position_template vs child_out) rho\<rangle>\<rangle>,
      A\<langle>lpc_seg_return_value is_cont c d (lpc_seg_position_template vs parent_out) rho\<rangle>)\<in>(qrstep False Q R)\<^sup>*"
      by (rule r_into_rtrancl[OF qrstep.ctxt[OF local]])
    show "(A\<langle>ctxtD\<langle>lpc_seg_return_value is_cont c d child_tmpl
        (lpc_seg_observe (map (lpc_seg_position_template vs)
          (map (lp_cut_instance_subst bindings) child_vars)) rho)\<rangle>\<rangle>,
      A\<langle>lpc_seg_return_value is_cont c d parent_tmpl
        (lpc_seg_observe (map (lpc_seg_position_template vs) observed) rho)\<rangle>)\<in>(qrstep False Q R)\<^sup>*"
      using lifted by (simp only: lpc_seg_return_value_def lpc_seg_observation_eval child_template parent_template)
  qed
qed


end
end
