theory LP_Prolog_Functor_Split_Invariant
 imports LP_Prolog_Functor_Split_Contract LP_Prolog_Domain_Invariant_Composition
begin

text \<open>Use the same Split routing and checked return projection, but allow
continuations to rely on an invariant retained by the attached full execution.
Standalone actual-return contracts remain separate premises.\<close>

theorem lpp_functor_split_invariant_contract:
 fixes vs :: "string list"
 and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes program: "lp_cut_source_program P"
 and shape: "lpc_check_return_split_shape bindings indices pre rest interface original"
 and arity: "length indices=arity"
 and projection: "lpc_check_return_projection_edge Q vs continuation_returned returned indices"
 and prefix: "lp_answer_contract
   (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_return_eval eta [(LPCGoals pre,interface)]) (lp_ild Q) t prefix_return"
 and initial: "I (lpc_return_eval eta [(LPCGoals pre,interface)])"
 and invariant_step: "\<And>us ev vs. I us \<Longrightarrow>
   (lpc_return_eval eta [(LPCGoals pre,interface)],us)\<in>(lp_answer_steps
     (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain))\<^sup>* \<Longrightarrow>
   lpc_prefix_active us \<Longrightarrow>
   lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
     (lpc_attach_answers (map (lp_cut_map (map_term id (lpc_return_route bindings))) rest) us) ev
     (lpc_attach_answers (map (lp_cut_map (map_term id (lpc_return_route bindings))) rest) vs) \<Longrightarrow> I vs"
 and invariant_tail: "\<And>rho vs. I ((LPCGoals [],rho)#vs) \<Longrightarrow> I vs"
 and returns: "\<And>rho. lp_actual_answer
   (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_return_eval eta [(LPCGoals pre,interface)]) rho \<Longrightarrow> H rho"
 and continuation: "\<And>rho remaining. lp_actual_answer
   (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_return_eval eta [(LPCGoals pre,interface)]) rho \<Longrightarrow>
   I ((LPCGoals [],rho)#remaining) \<Longrightarrow> H rho \<Longrightarrow> lp_answer_contract
    (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho))
       (map (lp_cut_map (map_term id (lpc_return_route bindings))) rest)),rho)]
    (lp_ild Q) (prefix_return rho) (\<lambda>theta. [(continuation_returned,map theta [0..<length vs])])"
 shows "lp_answer_contract
   (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_return_eval eta original) (lp_ild Q) t (\<lambda>rho. [(returned,map rho [0..<arity])])"
proof -
 let ?T = "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain"
 let ?gs = "map (lp_cut_map (map_term id (lpc_return_route bindings))) rest"
 let ?ss = "lpc_return_eval eta [(LPCGoals pre,interface)]"
 let ?cont = "\<lambda>rho. [(continuation_returned,map rho [0..<length vs])]"
 have valid: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ?ss"
   by (simp add: lpc_return_eval_def)
 have separated: "lpc_rest_scopes ?gs \<inter> set (lpc_barrier_ids (map fst ?ss)) = {}"
   by (simp add: lpc_return_eval_def)
 have composed: "lp_answer_contract ?T (lpc_attach_answers ?gs ?ss) (lp_ild Q) t ?cont"
 proof (rule lpp_domain_contract_compose_actual_invariant[where I=I and rest="?gs",
     OF program prefix valid separated initial invariant_step invariant_tail])
  fix rho remaining
  assume actual: "lp_actual_answer ?T ?ss rho" and invariant: "I ((LPCGoals [],rho)#remaining)"
  show "lp_answer_contract ?T [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) ?gs),rho)]
    (lp_ild Q) (prefix_return rho) ?cont"
    by (rule continuation[OF actual invariant returns[OF actual]])
 qed
 have bridge: "(?cont rho,[(returned,map (lpc_project_interface indices rho) [0..<arity])])\<in>(lp_ild Q)\<^sup>*"
   for rho :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  using lpc_return_projection_edge_sound[OF projection, of rho] arity by auto
 have projected: "lp_answer_contract ?T
   (lpc_reinterface (lpc_project_interface indices) (lpc_attach_answers ?gs ?ss))
   (lp_ild Q) t (\<lambda>rho. [(returned,map rho [0..<arity])])"
  by (rule lpp_domain_contract_project[where F="lpc_project_interface indices",
       OF lpc_project_interface_commutes composed bridge])
 show ?thesis using projected lpc_return_split_shape_sound[OF shape, of eta] by simp
qed

ML \<open>
val checked = @{thms lpp_functor_split_invariant_contract};
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
 exists (fn n => not (member (op =) inherited n)) (oracles checked)
 then error "Untrusted invariant functor Split" else ();
\<close>
end
