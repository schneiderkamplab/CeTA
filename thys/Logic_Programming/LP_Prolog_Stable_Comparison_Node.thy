theory LP_Prolog_Stable_Comparison_Node
 imports LP_Prolog_Stable_Representation
begin

theorem lpp_stable_comparison_node_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_comparison T yes_facts no_facts error_facts fuel Q nds states contexts Fs nd F ss source_context f comparison reversed a b gs active saved yes no error_edge"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and step: "lpp_answer_transition P lpp_builtin_signature (lpp_stable_source_builtin operation) (lpc_return_eval eta ss) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_stable_rep operation SP nds states contexts Fs (lpc_return_scope_word swaps tt) u)"
proof -
  let ?observation = "LPPOComparison comparison (if reversed then b else a) (if reversed then a else b)"
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs),active)#saved"
    and name: "lpp_comparison_descriptor f comparison reversed"
    using checked by (auto simp: lpp_check_evaluation_comparison_def)
  have raw: "lpp_answer_transition P lpp_builtin_signature (lpp_stable_source_builtin operation)
    ((LPCGoals (LPCAtom (LPIFun (LPCUser f) [lp_ieval a eta,lp_ieval b eta]) #
       map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),lpc_return_env active eta)#lpc_return_eval eta saved) event tt"
    using step by (simp add: shape lpc_return_eval_def lpp_finite_source_domain_def)
  have actual: "event=None \<and>
    ((tt=lpc_return_eval eta ((LPCGoals gs,active)#saved) \<and> lpp_stable_observation_holds operation eta ?observation)
      \<or> tt=lpc_return_eval eta saved \<or> tt=lpc_return_eval eta [])"
    using lpp_stable_comparison_step[OF name raw]
    by (auto simp: shape lpc_return_eval_def split: if_splits)
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  have yes_link: "lpp_check_evaluation_link T yes_facts fuel Q nds states contexts Fs nd ((LPCGoals gs,active)#saved)
    (lpcn_ground nd) (lpcn_guards nd) [] F (lpp_add_numeric_observation ?observation source_context) yes"
    and no_link: "lpp_check_evaluation_link T no_facts fuel Q nds states contexts Fs nd saved
    (lpcn_ground nd) (lpcn_guards nd) [] F source_context no"
    and error_link: "lpp_check_evaluation_link T error_facts fuel Q nds states contexts Fs nd []
    (lpcn_ground nd) (lpcn_guards nd) [] F source_context error_edge"
    using checked by (auto simp: lpp_check_evaluation_comparison_def)
  have yes_step: "lpp_stable_observation_holds operation eta ?observation \<Longrightarrow>
    \<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
      lpp_stable_rep operation SP nds states contexts Fs (lpc_return_scope_word swaps (lpc_return_eval eta ((LPCGoals gs,active)#saved))) u"
    using lpp_stable_link_sound[OF compatible program yes_link equations refl known free]
      lpp_stable_context_add_observation[OF observed] by blast
  show ?thesis using actual yes_step lpp_stable_link_sound[OF compatible program no_link equations refl known free observed]
    lpp_stable_link_sound[OF compatible program error_link equations refl known free observed] by blast
qed


lemma lpp_stable_comparison_node_domain:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_comparison T yes_facts no_facts error_facts fuel Q nds states contexts Fs nd F ss source_context f comparison reversed a b gs active saved yes no error_edge"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
  shows "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_finite_source_domain (map fst (lpc_return_eval eta ss))"
proof -
  have prior: "lpp_evaluation_context_holds (lpp_stable_scalar_evaluation operation) SP source_context eta"
    using observed by (simp add: lpp_stable_context_holds_def)
  show ?thesis
    by (rule lpp_evaluation_comparison_domain[where E="lpp_stable_scalar_evaluation operation",
      OF _ _ program checked known prior])
      (auto intro: lpp_stable_evaluation_integer_contract[OF compatible]
        dest: lpp_stable_scalar_evaluation_ground)
qed

ML \<open>
val checked = [@{thm lpp_stable_comparison_node_sound}, @{thm lpp_stable_comparison_node_domain}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable comparison node dependency" else ();
\<close>
end
