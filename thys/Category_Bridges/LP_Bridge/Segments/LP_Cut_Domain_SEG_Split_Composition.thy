theory LP_Cut_Domain_SEG_Split_Composition
 imports LP_Cut_Domain_SEG_Split_Bridge
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

theorem precise_seg_split_composition:
  fixes P :: "('f,string) lp_cut_program"
  assumes program: "lp_cut_source_program P"
    and route: "lpc_check_return_route_goals bindings (map Var vs :: ('f lp_cut_symbol,string) term list) rest"
    and distinct: "distinct vs" and nonempty: "pre\<noteq>[]"
    and enter: "lpc_seg_check_encoded_pair 1 2 is_cont c d C R l (Fun u (first_in#caps))"
    and middle: "lpc_seg_check_encoded_pair 2 2 is_cont c d C R
      (Fun u (first_out#caps)) (Fun v (second_in#more_caps))"
    and leave: "lpc_seg_check_encoded_pair 2 1 is_cont c d C R
      (Fun v (second_out#more_caps)) final_out"
    and cont: "is_cont u" "is_cont v"
    and finite: "lp_seg_ground (lp_ieval l eta)"
    and vars: "vars_term first_out \<subseteq> set vs"
      "vars_term (Fun v (second_in#more_caps)) \<subseteq> set vs"
      "vars_term second_out \<subseteq> set vs" "vars_term final_out \<subseteq> set vs"
    and prefix: "precise_return_contract P (lpc_return_eval eta [(LPCGoals pre,map Var vs)]) (qrstep False Q R)
      (A\<langle>(lpc_seg_pending c d u caps eta)\<langle>lpc_seg_return_value is_cont c d first_in eta\<rangle>\<rangle>)
      (\<lambda>rho. A\<langle>(lpc_seg_pending c d u caps eta)\<langle>
        lpc_seg_return_value is_cont c d (lpc_seg_position_template vs first_out) rho\<rangle>\<rangle>)"
    and prefix_ground: "\<And>rho. precise_actual_return P (lpc_return_eval eta [(LPCGoals pre,map Var vs)]) rho \<Longrightarrow>
      lp_seg_ground (lp_ieval (lpc_seg_position_template vs first_out) rho)"
    and continuation: "\<And>rho theta.
      precise_actual_return P (lpc_return_eval eta [(LPCGoals pre,map Var vs)]) rho \<Longrightarrow>
      rho=lpc_return_env (map Var vs) theta \<Longrightarrow>
      (\<And>x. D (theta x)) \<Longrightarrow>
      (A\<langle>lpc_seg_return_value is_cont c d l eta\<rangle>,
        A\<langle>(lpc_seg_pending c d v more_caps theta)\<langle>lpc_seg_return_value is_cont c d second_in theta\<rangle>\<rangle>)
        \<in>(qrstep False Q R)\<^sup>+ \<Longrightarrow>
      precise_return_contract P (lpc_return_eval theta [(LPCGoals rest,map Var vs)]) (qrstep False Q R)
        (A\<langle>(lpc_seg_pending c d v more_caps theta)\<langle>lpc_seg_return_value is_cont c d second_in theta\<rangle>\<rangle>)
        (\<lambda>sigma. A\<langle>(lpc_seg_pending c d v more_caps theta)\<langle>
          lpc_seg_return_value is_cont c d (lpc_seg_position_template vs second_out) sigma\<rangle>\<rangle>)"
    and second_ground: "\<And>rho theta sigma.
      precise_actual_return P (lpc_return_eval eta [(LPCGoals pre,map Var vs)]) rho \<Longrightarrow>
      rho=lpc_return_env (map Var vs) theta \<Longrightarrow>
      precise_actual_return P (lpc_return_eval theta [(LPCGoals rest,map Var vs)]) sigma \<Longrightarrow>
      lp_seg_ground (lp_ieval (lpc_seg_position_template vs second_out) sigma)"
    and range: "range d \<subseteq> C"
    and roots: "\<And>q. q\<in>Q \<Longrightarrow> \<exists>g us. q=Fun g us \<and> g\<notin>C"
    and domains: "\<And>x. D (eta x)"
  shows "precise_return_contract P (lpc_return_eval eta [(LPCGoals (pre@rest),map Var vs)]) (qrstep False Q R)
    (A\<langle>lpc_seg_return_value is_cont c d l eta\<rangle>)
    (\<lambda>rho. A\<langle>lpc_seg_return_value is_cont c d (lpc_seg_position_template vs final_out) rho\<rangle>)"
proof -
  let ?rr = "qrstep False Q R"
  let ?ss = "lpc_return_eval eta [(LPCGoals pre,map Var vs)]"
  let ?rest = "map (lp_cut_map (map_term id (lpc_return_route bindings))) rest"
  let ?t = "A\<langle>lpc_seg_return_value is_cont c d l eta\<rangle>"
  let ?p = "A\<langle>(lpc_seg_pending c d u caps eta)\<langle>lpc_seg_return_value is_cont c d first_in eta\<rangle>\<rangle>"
  let ?ret = "\<lambda>rho. A\<langle>(lpc_seg_pending c d u caps eta)\<langle>
        lpc_seg_return_value is_cont c d (lpc_seg_position_template vs first_out) rho\<rangle>\<rangle>"
  let ?final = "\<lambda>rho. A\<langle>lpc_seg_return_value is_cont c d (lpc_seg_position_template vs final_out) rho\<rangle>"
  have call: "list_all (\<lambda>t. lp_seg_ground (lp_ieval t eta)) caps \<and> (?t,?p)\<in>?rr"
    using lpc_seg_checked_call[where Q=Q, OF enter cont(1) finite range roots]
    by (auto simp: lpc_seg_pending_def lpc_seg_return_value_def intro: qrstep.ctxt)
  have entry_step: "(?t,?p)\<in>?rr\<^sup>+" using call by auto
  have composed: "precise_return_contract P (lpc_attach_answers ?rest ?ss) ?rr ?p ?final"
  proof (rule precise_return_contract_compose_actual[OF program prefix])
    show "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ?ss"
      using nonempty by (simp add: lpc_return_eval_def lpc_clause_nonempty.simps)
    show "lpc_rest_scopes ?rest \<inter> set (lpc_barrier_ids (map fst ?ss))={}"
      by (simp add: lpc_return_eval_def)
  next
    fix rho assume actual: "precise_actual_return P ?ss rho"
    obtain theta where source: "precise_actual_return P
        [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) (LPCGoals pre),eta)] theta"
      and rho: "rho=lpc_return_env (map Var vs) theta"
      using precise_seg_observed_actual[OF actual] by blast
    have initial: "precise_environments [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) (LPCGoals pre),eta)]"
      using domains by (simp add: precise_environments_def)
    have thetaD: "\<And>x. D (theta x)"
      by (rule precise_actual_return_domain[OF initial source])
    have position: "lp_ieval (lpc_seg_position_template vs t) rho=lp_ieval t theta"
      if "vars_term t \<subseteq> set vs" for t
      unfolding rho by (rule lpc_seg_position_eval[OF distinct that])
    have more_position: "lp_ieval (lpc_seg_position_template vs t) rho=lp_ieval t theta"
      if "t\<in>set more_caps" for t
      by (rule position) (use vars(2) that in auto)
    have next_position: "lp_ieval (lpc_seg_position_template vs second_in) rho=lp_ieval second_in theta"
      by (rule position) (use vars(2) in auto)
    have more_values: "map (\<lambda>t. lpc_seg_finite_value (map_lp_iterm d id
        (lp_ieval (lpc_seg_position_template vs t) rho))) more_caps =
      map (\<lambda>t. lpc_seg_finite_value (map_lp_iterm d id (lp_ieval t theta))) more_caps"
      by (rule map_cong[OF refl]) (simp add: more_position)
    have bridge: "list_all (\<lambda>t. lp_seg_ground (lp_ieval t theta)) more_caps \<and>
      (?ret rho,A\<langle>(lpc_seg_pending c d v more_caps theta)\<langle>
        lpc_seg_return_value is_cont c d second_in theta\<rangle>\<rangle>)\<in>?rr"
      using precise_seg_checked_actual_continue[where Q=Q, OF middle cont actual distinct vars(1,2)
        prefix_ground[OF actual] conjunct1[OF call] range roots] vars(2)
      by (auto simp: lpc_seg_pending_def lpc_seg_return_value_def next_position more_values more_position list_all_iff intro: qrstep.ctxt)
    let ?v = "A\<langle>(lpc_seg_pending c d v more_caps theta)\<langle>lpc_seg_return_value is_cont c d second_in theta\<rangle>\<rangle>"
    have reached: "(?p,?ret rho)\<in>?rr\<^sup>*" by (rule precise_actual_return_residual[OF prefix actual])
    have strict: "(?t,?v)\<in>?rr\<^sup>+"
      using trancl_rtrancl_trancl[OF entry_step reached] bridge by auto
    have child: "precise_return_contract P (lpc_return_eval theta [(LPCGoals rest,map Var vs)]) ?rr ?v
      (\<lambda>sigma. A\<langle>(lpc_seg_pending c d v more_caps theta)\<langle>
        lpc_seg_return_value is_cont c d (lpc_seg_position_template vs second_out) sigma\<rangle>\<rangle>)"
      by (rule continuation[OF actual rho thetaD strict])
    have completed: "precise_return_contract P (lpc_return_eval theta [(LPCGoals rest,map Var vs)]) ?rr ?v ?final"
    proof (rule precise_return_contract_post_actual[OF child])
      fix sigma assume returned: "precise_actual_return P (lpc_return_eval theta [(LPCGoals rest,map Var vs)]) sigma"
      show "(A\<langle>(lpc_seg_pending c d v more_caps theta)\<langle>
          lpc_seg_return_value is_cont c d (lpc_seg_position_template vs second_out) sigma\<rangle>\<rangle>,?final sigma)\<in>?rr\<^sup>*"
        using precise_seg_checked_actual_return[where Q=Q, OF leave cont(2) returned distinct vars(3,4)
          second_ground[OF actual rho returned] conjunct1[OF bridge] range roots]
        by (auto simp: lpc_seg_pending_def lpc_seg_return_value_def intro: qrstep.ctxt)
    qed
    have source_equal: "[(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) ?rest),rho)] =
      lpc_return_eval theta [(LPCGoals rest,map Var vs)]"
      using lpc_return_route_goals[OF route, of theta]
      by (simp add: rho lpc_return_eval_def)
    show "precise_return_contract P [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) ?rest),rho)] ?rr (?ret rho) ?final"
      unfolding source_equal by (rule precise_return_contract_start[OF _ completed]) (use bridge in auto)
  qed
  have shape: "lpc_attach_answers ?rest ?ss=lpc_return_eval eta [(LPCGoals (pre@rest),map Var vs)]"
    using lpc_return_route_goals[OF route, of eta]
    by (simp add: lpc_return_eval_def lpc_attach_answers_def)
  show ?thesis unfolding shape[symmetric]
    by (rule precise_return_contract_start[OF _ composed]) (use call in auto)
qed


end
end
