theory LP_Cut_SEG_Projected_Split_Composition
  imports LP_Cut_SEG_Projected_Pending
begin

theorem lpc_seg_projected_split_composition:
  fixes P :: "('f,string) lp_cut_program" and filtering :: "'g afs"
  assumes program: "lp_cut_source_program P"
    and route: "lpc_check_return_route_goals bindings (map Var vs :: ('f lp_cut_symbol,string) term list) rest"
    and distinct: "distinct vs" and nonempty: "pre\<noteq>[]"
    and enter: "lpc_seg_check_projected_pair filtering 1 2 is_cont c d R l (Fun u (first_in#caps))"
    and middle: "lpc_seg_check_projected_pair filtering 2 2 is_cont c d R
      (Fun u (first_out#caps)) (Fun v (second_in#more_caps))"
    and leave: "lpc_seg_check_projected_pair filtering 2 1 is_cont c d R
      (Fun v (second_out#more_caps)) final_out"
    and cont: "is_cont u" "is_cont v"
    and keep: "lpc_seg_projected_continuation_filter filtering (c u) (Suc (length caps))"
      "lpc_seg_projected_continuation_filter filtering (c v) (Suc (length more_caps))"
    and finite: "lpc_seg_has_projection filtering (lpc_seg_runtime_value is_cont c d l eta)"
    and ambient: "lpc_seg_projection_context filtering A"
    and vars: "vars_term first_out \<subseteq> set vs"
      "vars_term (Fun v (second_in#more_caps)) \<subseteq> set vs"
      "vars_term second_out \<subseteq> set vs" "vars_term final_out \<subseteq> set vs"
    and prefix: "lpc_return_contract P (lpc_return_eval eta [(LPCGoals pre,map Var vs)]) (lpc_seg_projected_rel filtering R)
      (A (lpc_seg_runtime_pending c d u caps eta (lpc_seg_runtime_value is_cont c d first_in eta)))
      (\<lambda>rho. A (lpc_seg_runtime_pending c d u caps eta
        (lpc_seg_runtime_value is_cont c d (lpc_seg_position_template vs first_out) rho)))"
    and continuation: "\<And>rho theta.
      lpc_actual_return P (lpc_return_eval eta [(LPCGoals pre,map Var vs)]) rho \<Longrightarrow>
      rho=lpc_return_env (map Var vs) theta \<Longrightarrow>
      (A (lpc_seg_runtime_value is_cont c d l eta),
        A (lpc_seg_runtime_pending c d v more_caps theta (lpc_seg_runtime_value is_cont c d second_in theta)))
        \<in>(lpc_seg_projected_rel filtering R)\<^sup>+ \<Longrightarrow>
      lpc_seg_has_projection filtering (lpc_seg_runtime_value is_cont c d second_in theta) \<Longrightarrow>
      lpc_seg_projection_context filtering (\<lambda>x. A (lpc_seg_runtime_pending c d v more_caps theta x)) \<Longrightarrow>
      lpc_return_contract P (lpc_return_eval theta [(LPCGoals rest,map Var vs)]) (lpc_seg_projected_rel filtering R)
        (A (lpc_seg_runtime_pending c d v more_caps theta (lpc_seg_runtime_value is_cont c d second_in theta)))
        (\<lambda>sigma. A (lpc_seg_runtime_pending c d v more_caps theta
          (lpc_seg_runtime_value is_cont c d (lpc_seg_position_template vs second_out) sigma)))"
  shows "lpc_return_contract P (lpc_return_eval eta [(LPCGoals (pre@rest),map Var vs)]) (lpc_seg_projected_rel filtering R)
    (A (lpc_seg_runtime_value is_cont c d l eta))
    (\<lambda>rho. A (lpc_seg_runtime_value is_cont c d (lpc_seg_position_template vs final_out) rho))"
proof -
  let ?rr = "lpc_seg_projected_rel filtering R"
  let ?ss = "lpc_return_eval eta [(LPCGoals pre,map Var vs)]"
  let ?rest = "map (lp_cut_map (map_term id (lpc_return_route bindings))) rest"
  let ?t = "A (lpc_seg_runtime_value is_cont c d l eta)"
  let ?p = "A (lpc_seg_runtime_pending c d u caps eta (lpc_seg_runtime_value is_cont c d first_in eta))"
  let ?ret = "\<lambda>rho. A (lpc_seg_runtime_pending c d u caps eta
        (lpc_seg_runtime_value is_cont c d (lpc_seg_position_template vs first_out) rho))"
  let ?final = "\<lambda>rho. A (lpc_seg_runtime_value is_cont c d (lpc_seg_position_template vs final_out) rho)"
  have call: "(?t,?p)\<in>?rr"
    using lpc_seg_projected_call[OF enter cont(1) keep(1) finite ambient]
    by (auto simp: lpc_seg_runtime_pending_def)
  have entry_step: "(?t,?p)\<in>?rr\<^sup>+" using call by auto
  have p_observed: "lpc_seg_has_projection filtering ?p"
    using call by (auto simp: lpc_seg_projected_rel_def lpc_seg_has_projection_def)
  have composed: "lpc_return_contract P (lpc_attach_answers ?rest ?ss) ?rr ?p ?final"
  proof (rule lpc_return_contract_compose_actual[OF program prefix])
    show "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ?ss"
      using nonempty by (simp add: lpc_return_eval_def lpc_clause_nonempty.simps)
    show "lpc_rest_scopes ?rest \<inter> set (lpc_barrier_ids (map fst ?ss))={}"
      by (simp add: lpc_return_eval_def)
  next
    fix rho assume actual: "lpc_actual_return P ?ss rho"
    obtain theta where rho: "rho=lpc_return_env (map Var vs) theta"
      by (rule lpc_seg_observed_actual[OF actual]) assumption
    have position: "lp_ieval (lpc_seg_position_template vs t) rho=lp_ieval t theta"
      if "vars_term t \<subseteq> set vs" for t
      unfolding rho by (rule lpc_seg_position_eval[OF distinct that])
    have reached: "(?p,?ret rho)\<in>?rr\<^sup>*"
      by (rule lpc_actual_return_residual[OF prefix actual])
    have returned_projection: "lpc_seg_has_projection filtering
      (lpc_seg_runtime_pending c d u caps eta (lpc_seg_runtime_value is_cont c d (lpc_seg_position_template vs first_out) rho))"
      by (rule lpc_seg_projection_context_reflect[OF ambient lpc_seg_projected_reachable[OF reached p_observed]])
    let ?v = "A (lpc_seg_runtime_pending c d v more_caps theta (lpc_seg_runtime_value is_cont c d second_in theta))"
    have local: "(lpc_seg_runtime_pending c d u caps eta
        (lpc_seg_runtime_value is_cont c d (lpc_seg_position_template vs first_out) rho),
      lpc_seg_runtime_pending c d v more_caps theta (lpc_seg_runtime_value is_cont c d second_in theta))\<in>?rr"
      using lpc_seg_projected_pending_actual[OF middle cont(1) actual distinct vars(1,2) keep(1) returned_projection]
      by (simp only: position[OF vars(2)] lpc_seg_runtime_pending_role[where is_cont=is_cont and u=v, OF cont(2)])
    have bridge: "(?ret rho,?v)\<in>?rr"
      by (rule lpc_seg_projection_context_step[OF ambient local])
    have strict: "(?t,?v)\<in>?rr\<^sup>+"
      using trancl_rtrancl_trancl[OF entry_step reached] bridge by auto
    have next_projection: "lpc_seg_has_projection filtering
      (lpc_seg_runtime_pending c d v more_caps theta (lpc_seg_runtime_value is_cont c d second_in theta))"
      using local by (auto simp: lpc_seg_projected_rel_def lpc_seg_has_projection_def)
    have child_context: "lpc_seg_has_projection filtering (lpc_seg_runtime_value is_cont c d second_in theta) \<and>
      lpc_seg_projection_context filtering (\<lambda>x. A (lpc_seg_runtime_pending c d v more_caps theta x))"
      by (rule lpc_seg_projected_pending_context[OF keep(2) next_projection ambient])
    have child: "lpc_return_contract P (lpc_return_eval theta [(LPCGoals rest,map Var vs)]) ?rr ?v
      (\<lambda>sigma. A (lpc_seg_runtime_pending c d v more_caps theta
        (lpc_seg_runtime_value is_cont c d (lpc_seg_position_template vs second_out) sigma)))"
      by (rule continuation[OF actual rho strict conjunct1[OF child_context] conjunct2[OF child_context]])
    have v_observed: "lpc_seg_has_projection filtering ?v"
      using bridge by (auto simp: lpc_seg_projected_rel_def lpc_seg_has_projection_def)
    have completed: "lpc_return_contract P (lpc_return_eval theta [(LPCGoals rest,map Var vs)]) ?rr ?v ?final"
    proof (rule lpc_return_contract_post_actual[OF child])
      fix sigma assume returned: "lpc_actual_return P (lpc_return_eval theta [(LPCGoals rest,map Var vs)]) sigma"
      have observed: "lpc_seg_has_projection filtering (lpc_seg_runtime_pending c d v more_caps theta
        (lpc_seg_runtime_value is_cont c d (lpc_seg_position_template vs second_out) sigma))"
        by (rule lpc_seg_projection_context_reflect[OF ambient lpc_seg_projected_contract_answer[OF child v_observed returned]])
      have step: "(lpc_seg_runtime_pending c d v more_caps theta
        (lpc_seg_runtime_value is_cont c d (lpc_seg_position_template vs second_out) sigma),
        lpc_seg_runtime_value is_cont c d (lpc_seg_position_template vs final_out) sigma)\<in>?rr"
        using lpc_seg_projected_pending_actual[OF leave cont(2) returned distinct vars(3,4) keep(2) observed]
        by (simp only: lpc_seg_runtime_value_def)
      show "(A (lpc_seg_runtime_pending c d v more_caps theta
        (lpc_seg_runtime_value is_cont c d (lpc_seg_position_template vs second_out) sigma)),?final sigma)\<in>?rr\<^sup>*"
        by (rule r_into_rtrancl[OF lpc_seg_projection_context_step[OF ambient step]])
    qed
    have source_equal: "[(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) ?rest),rho)] =
      lpc_return_eval theta [(LPCGoals rest,map Var vs)]"
      using lpc_return_route_goals[OF route, of theta]
      by (simp add: rho lpc_return_eval_def)
    show "lpc_return_contract P [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) ?rest),rho)] ?rr (?ret rho) ?final"
      unfolding source_equal by (rule lpc_return_contract_start[OF _ completed]) (use bridge in auto)
  qed
  have shape: "lpc_attach_answers ?rest ?ss=lpc_return_eval eta [(LPCGoals (pre@rest),map Var vs)]"
    using lpc_return_route_goals[OF route, of eta]
    by (simp add: lpc_return_eval_def lpc_attach_answers_def)
  show ?thesis unfolding shape[symmetric]
    by (rule lpc_return_contract_start[OF _ composed]) (use call in auto)
qed

end
