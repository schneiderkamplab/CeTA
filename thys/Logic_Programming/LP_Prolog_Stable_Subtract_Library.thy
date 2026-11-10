theory LP_Prolog_Stable_Subtract_Library
 imports LP_Prolog_Stable_Constant LP_Prolog_Subtract_Library
begin

lemma lpp_stable_subtract_library_contract:
  assumes contract: "lp_answer_contract
    (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
    ((LPCGoals (LPCAtom (LPIFun (LPCUser lpp_subtract_library) [e,s,a])#gs),eta)#saved) R t ret"
  shows "lp_answer_contract
    (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
    ((LPCGoals (LPCAtom (LPIFun (LPCUser ''3:subtract'') [e,s,a])#gs),eta)#saved) R t ret"
proof (rule lp_answer_contract_intro)
  let ?T = "lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain"
  fix event tt assume step: "?T ((LPCGoals (LPCAtom (LPIFun (LPCUser ''3:subtract'') [e,s,a])#gs),eta)#saved) event tt"
  have actual: "lpp_answer_transition P lpp_builtin_signature (lpp_stable_source_builtin operation)
    ((LPCGoals (LPCAtom (LPIFun (LPCUser ''3:subtract'') [e,s,a])#gs),eta)#saved) event tt"
    using step by (auto simp: lpp_domain_answers_def lpp_finite_source_domain_def lpp_disequality_predicate_def)
  have empty: "lp_answer_contract ?T [] R t ret"
    by (rule lp_answer_contract_intro)
      (auto simp: lpp_domain_answers_def elim: lpp_answer_transition.cases lpc_answer_transition.cases)

  show "(\<forall>rho. event=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*) \<and> lp_answer_contract ?T tt R t ret"
    using lpp_subtract_library_step[OF lpp_stable_answer_transition_refines[OF actual]] contract empty by auto
qed
theorem lpp_stable_context_subtract_library_contract:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_subtract_library T fs fuel P Q nds states contexts Fs nd F ss source_context e s a gs active saved middle"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and invariant: "J (lpc_return_eval eta ss)"
    and frames: "\<And>xs ys. map snd xs=map snd ys \<Longrightarrow> J ys \<Longrightarrow> J xs"
    and lower: "\<And>rho. ([(lpcn_pred nd,map eta (lpcn_vars nd))],
        [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho \<Longrightarrow>
      lpc_free_knowledge (set (Fs!lpcl_target middle)) rho \<Longrightarrow>
      lpp_stable_context_holds operation SP (contexts!lpcl_target middle) rho \<Longrightarrow>
      J (lpc_return_eval rho (states!lpcl_target middle)) \<Longrightarrow>
      lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
        (lpc_return_eval rho (states!lpcl_target middle)) R t ret"
  shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
    (lpc_return_eval eta ss) R t ret"
proof -
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser ''3:subtract'') [e,s,a])#gs),active)#saved"
    and swaps: "lpcl_swaps middle=[]"
    and link: "lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd
       ((LPCGoals (LPCAtom (Fun (LPCUser lpp_subtract_library) [e,s,a])#gs),active)#saved)
       (lpcn_ground nd) (lpcn_guards nd) [] F source_context middle"
    using checked by (auto simp: lpp_check_subtract_library_def)
  let ?synthetic = "((LPCGoals (LPCAtom (Fun (LPCUser lpp_subtract_library) [e,s,a])#gs),active)#saved)"
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  have parent: "map eta (lpcn_vars nd)=map eta (lpcn_vars nd)" by simp
  obtain rho where same: "lpc_return_eval eta ?synthetic=lpc_return_eval rho (states!lpcl_target middle)"
    and knowledge: "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho"
    and child_free: "lpc_free_knowledge (set (Fs!lpcl_target middle)) rho"
    and child_context: "lpp_stable_context_holds operation SP (contexts!lpcl_target middle) rho"
    and edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],
      [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>lp_ild Q"
    using lpp_stable_link_witness[OF compatible program link equations parent known free observed] by (simp add: swaps) blast
  have frame_same: "map snd (lpc_return_eval eta ?synthetic)=map snd (lpc_return_eval eta ss)"
    by (simp add: shape lpc_return_eval_def)
  have child_invariant: "J (lpc_return_eval rho (states!lpcl_target middle))"
    using frames[OF frame_same invariant] same by simp
  have child: "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
    (lpc_return_eval rho (states!lpcl_target middle)) R t ret"
    by (rule lower[OF r_into_trancl[OF edge] knowledge child_free child_context child_invariant])
  have continuation: "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
    (lpc_return_eval eta ?synthetic) R t ret" using child same by simp
  have child_actual: "lp_answer_contract
      (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
      ((LPCGoals (LPCAtom (LPIFun (LPCUser lpp_subtract_library)
        [lp_ieval e eta,lp_ieval s eta,lp_ieval a eta])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
        lpc_return_env active eta)#lpc_return_eval eta saved) R t ret"
    using continuation by (simp add: lpc_return_eval_def)
  show ?thesis using lpp_stable_subtract_library_contract[OF child_actual]
    by (simp add: shape lpc_return_eval_def)
qed

end
