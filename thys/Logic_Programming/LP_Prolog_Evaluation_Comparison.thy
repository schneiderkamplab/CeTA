theory LP_Prolog_Evaluation_Comparison
 imports LP_Prolog_Evaluation_Cut_Actions LP_Prolog_Comparison_Failure
begin

lemma lpp_add_evaluation_numeric_holds:
  "lpp_evaluation_context_holds E SP source_context eta \<Longrightarrow>
   lpp_evaluation_observation_holds E eta observation \<Longrightarrow>
   lpp_evaluation_context_holds E SP (lpp_add_numeric_observation observation source_context) eta"
  by (cases source_context) (auto simp: lpp_evaluation_context_holds_def)

definition lpp_check_comparison_links where
  "lpp_check_comparison_links T yes_facts no_facts error_facts fuel Q nds states contexts Fs nd F ss source_context f comparison reversed a b gs active saved yes no error_edge =
    (ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs),active)#saved \<and>
     lpp_comparison_descriptor f comparison reversed \<and>
     lpp_check_evaluation_link T yes_facts fuel Q nds states contexts Fs nd ((LPCGoals gs,active)#saved)
       (lpcn_ground nd) (lpcn_guards nd) [] F
       (lpp_add_numeric_observation (LPPOComparison comparison (if reversed then b else a) (if reversed then a else b)) source_context) yes \<and>
     (lpp_check_evaluation_link T no_facts fuel Q nds states contexts Fs nd saved
       (lpcn_ground nd) (lpcn_guards nd) [] F source_context no \<or>
      lpp_check_evaluation_link T no_facts fuel Q nds states contexts Fs nd saved
       (lpcn_ground nd) (lpcn_guards nd) [] F
       (lpp_add_numeric_observation (LPPOComparison (lpp_comparison_complement comparison) (if reversed then a else b) (if reversed then b else a)) source_context) no) \<and>
     lpp_check_evaluation_link T error_facts fuel Q nds states contexts Fs nd []
       (lpcn_ground nd) (lpcn_guards nd) [] F source_context error_edge)"

definition lpp_check_evaluation_comparison where
  "lpp_check_evaluation_comparison T yes_facts no_facts error_facts fuel Q nds states contexts Fs nd F ss source_context f comparison reversed a b gs active saved yes no error_edge =
    (vars_term a \<union> vars_term b \<subseteq> set (lpcn_ground nd) \<union> lpp_source_context_ground source_context \<and>
     lpp_check_comparison_links T yes_facts no_facts error_facts fuel Q nds states contexts Fs nd F ss source_context f comparison reversed a b gs active saved yes no error_edge)"

lemma lpp_evaluation_comparison_domain:
  fixes SP :: "string lpp_success_clause list"
  assumes contract: "lpp_eval_integer_contract TYPE(string) E"
    and evaluation: "\<And>e t. E e t \<Longrightarrow> lp_seg_ground e \<and> lp_seg_ground t"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_comparison T yes_facts no_facts error_facts fuel Q nds states contexts Fs nd F ss source_context f comparison reversed a b gs active saved yes no error_edge"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and observed: "lpp_evaluation_context_holds E SP source_context eta"
  shows "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_finite_source_domain (map fst (lpc_return_eval eta ss))"
proof -
  let ?negative = "LPPOComparison (lpp_comparison_complement comparison) (if reversed then a else b) (if reversed then b else a)"
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs),active)#saved"
    and name: "lpp_comparison_descriptor f comparison reversed"
    and finite: "lp_seg_ground (lp_ieval a eta)" "lp_seg_ground (lp_ieval b eta)"
    using checked known lpp_evaluation_context_ground_sound[OF evaluation observed]
    by (auto simp: lpp_check_evaluation_comparison_def lpp_check_comparison_links_def lp_cut_knowledge_def lp_seg_ground_eval)
  have ni: "f\<noteq>''1:integer''" and ne: "f\<noteq>''2:is''"
    using name by (cases comparison; cases reversed; auto)+
  have descriptor: "lpp_source_comparison f=Some (comparison,reversed)"
    using name lpp_source_comparison_descriptor by blast
  have old_domain: "lpp_integer_source_domain f [lp_ieval a eta,lp_ieval b eta]"
    using finite by (simp only: lpp_integer_source_domain.simps ni ne descriptor if_False option.case; simp)
  have domain: "lpp_finite_source_domain f [lp_ieval a eta,lp_ieval b eta]"
    by (rule lpp_finite_source_domain_extends[OF old_domain])
  show ?thesis using domain by (simp add: shape lpc_return_eval_def)
qed

theorem lpp_evaluation_comparison_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes contract: "lpp_eval_integer_contract TYPE(string) E"
    and evaluation: "\<And>e t. E e t \<Longrightarrow> lp_seg_ground e \<and> lp_seg_ground t"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_comparison T yes_facts no_facts error_facts fuel Q nds states contexts Fs nd F ss source_context f comparison reversed a b gs active saved yes no error_edge"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_evaluation_context_holds E SP source_context eta"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_finite_source_builtin (lpc_return_eval eta ss) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_evaluation_rep E SP nds states contexts Fs (lpc_return_scope_word swaps tt) u)"
proof -
  let ?observation = "LPPOComparison comparison (if reversed then b else a) (if reversed then a else b)"
  let ?negative = "LPPOComparison (lpp_comparison_complement comparison) (if reversed then a else b) (if reversed then b else a)"
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs),active)#saved"
    and name: "lpp_comparison_descriptor f comparison reversed"
    using checked by (auto simp: lpp_check_evaluation_comparison_def lpp_check_comparison_links_def)
  have raw: "lpp_answer_transition P lpp_builtin_signature lpp_finite_source_builtin
    ((LPCGoals (LPCAtom (LPIFun (LPCUser f) [lp_ieval a eta,lp_ieval b eta]) #
       map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),lpc_return_env active eta)#lpc_return_eval eta saved) event tt"
    using step by (simp add: shape lpc_return_eval_def lpp_finite_source_domain_def)
  have actual: "event=None \<and>
    ((tt=lpc_return_eval eta ((LPCGoals gs,active)#saved) \<and> lpp_evaluation_observation_holds E eta ?observation)
      \<or> (tt=lpc_return_eval eta saved \<and> lpp_evaluation_observation_holds E eta ?negative) \<or> tt=lpc_return_eval eta [])"
    using lpp_finite_source_comparison_precise_step[OF name raw]
    by (auto simp: shape lpc_return_eval_def dest: lpp_finite_comparison_failure_complement split: if_splits)
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  have yes_link: "lpp_check_evaluation_link T yes_facts fuel Q nds states contexts Fs nd ((LPCGoals gs,active)#saved)
    (lpcn_ground nd) (lpcn_guards nd) [] F (lpp_add_numeric_observation ?observation source_context) yes"
    and no_link: "lpp_check_evaluation_link T no_facts fuel Q nds states contexts Fs nd saved
    (lpcn_ground nd) (lpcn_guards nd) [] F source_context no \<or>
    lpp_check_evaluation_link T no_facts fuel Q nds states contexts Fs nd saved
    (lpcn_ground nd) (lpcn_guards nd) [] F (lpp_add_numeric_observation ?negative source_context) no"
    and error_link: "lpp_check_evaluation_link T error_facts fuel Q nds states contexts Fs nd []
    (lpcn_ground nd) (lpcn_guards nd) [] F source_context error_edge"
    using checked by (auto simp: lpp_check_evaluation_comparison_def lpp_check_comparison_links_def)
  have yes_step: "lpp_evaluation_observation_holds E eta ?observation \<Longrightarrow>
    \<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
      lpp_evaluation_rep E SP nds states contexts Fs (lpc_return_scope_word swaps (lpc_return_eval eta ((LPCGoals gs,active)#saved))) u"
    using lpp_evaluation_link_sound[OF contract evaluation program yes_link equations refl known free]
      lpp_add_evaluation_numeric_holds[OF observed] by blast
  have no_step: "lpp_evaluation_observation_holds E eta ?negative \<Longrightarrow>
    \<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
      lpp_evaluation_rep E SP nds states contexts Fs (lpc_return_scope_word swaps (lpc_return_eval eta saved)) u"
  proof -
    assume negative: "lpp_evaluation_observation_holds E eta ?negative"
    have extended: "lpp_evaluation_context_holds E SP (lpp_add_numeric_observation ?negative source_context) eta"
      by (rule lpp_add_evaluation_numeric_holds[OF observed negative])
    from no_link show ?thesis
    proof
      assume old: "lpp_check_evaluation_link T no_facts fuel Q nds states contexts Fs nd saved
        (lpcn_ground nd) (lpcn_guards nd) [] F source_context no"
      show ?thesis by (rule lpp_evaluation_link_sound[OF contract evaluation program old equations refl known free observed])
    next
      assume refined: "lpp_check_evaluation_link T no_facts fuel Q nds states contexts Fs nd saved
        (lpcn_ground nd) (lpcn_guards nd) [] F (lpp_add_numeric_observation ?negative source_context) no"
      show ?thesis by (rule lpp_evaluation_link_sound[OF contract evaluation program refined equations refl known free extended])
    qed
  qed
  show ?thesis using actual yes_step no_step
    lpp_evaluation_link_sound[OF contract evaluation program error_link equations refl known free observed] by blast
qed


end
