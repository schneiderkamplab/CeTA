theory LP_Prolog_Checked_Split_Composition
 imports LP_Prolog_Finite_Continuation_Composition LP_Prolog_Module_Return_Interface
   LP_Cut_Return_Split_Shape
begin

text \<open>Use the shared executable Split shape check with the existing Prolog
answer semantics. Finite continuation transport and actual successful returns
remain explicit premises; termination of the prefix cannot supply them.\<close>

theorem lpp_checked_split_finite_actual_contract:
 assumes ss_def: "ss = lpc_return_eval eta [(LPCGoals pre,interface)]"
 and routed_def: "routed = map (lp_cut_map (map_term id (lpc_return_route bindings))) rest"
 and checked: "lpc_check_return_split_shape bindings indices pre rest interface original"
 and program: "lp_cut_source_program P"
 and prefix: "lp_answer_contract (lpp_domain_answers P B U D) ss R t ret"
 and valid: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ss"
 and separated: "lpc_rest_scopes routed \<inter> set (lpc_barrier_ids (map fst ss))={}"
 and initial: "lpp_finite_execution (lpc_attach_answers routed ss)"
 and preserve: "\<And>us ev vs. lpp_finite_execution (lpc_attach_answers routed us) \<Longrightarrow>
   (ss,us)\<in>(lp_answer_steps (lpp_domain_answers P B U D))\<^sup>* \<Longrightarrow>
   lpc_prefix_active us \<Longrightarrow>
   lpp_domain_answers P B U D (lpc_attach_answers routed us) ev (lpc_attach_answers routed vs) \<Longrightarrow>
   lpp_finite_execution (lpc_attach_answers routed vs)"
 and continuation: "\<And>rho. lp_actual_answer (lpp_domain_answers P B U D) ss rho \<Longrightarrow>
   lpp_finite_goals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) routed) \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P B U D)
    [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) routed),rho)] R (ret rho) extended"
 and bridge: "\<And>rho. lp_actual_answer (lpp_domain_answers P B U D)
   (lpc_attach_answers routed ss) rho \<Longrightarrow>
   (extended rho,final (lpc_project_interface indices rho))\<in>R\<^sup>*"
 shows "lp_answer_contract (lpp_domain_answers P B U D) (lpc_return_eval eta original) R t final"
proof -
 have composed: "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_attach_answers routed ss) R t extended"
  by (rule lpp_domain_contract_compose_finite_continuation[
    OF program prefix valid separated initial preserve continuation])
 have returned: "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_attach_answers routed ss) R t (\<lambda>rho. final (lpc_project_interface indices rho))"
  by (rule lp_answer_contract_post_actual[OF composed bridge])
 have projected: "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_reinterface (lpc_project_interface indices) (lpc_attach_answers routed ss)) R t final"
  by (rule lpp_domain_contract_project[OF lpc_project_interface_commutes returned]) simp
 show ?thesis using projected lpc_return_split_shape_sound[OF checked, of eta]
  by (simp add: ss_def routed_def)
qed

ML \<open>
val checked = @{thms lpp_checked_split_finite_actual_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted checked Split composition" else ();
\<close>
end
