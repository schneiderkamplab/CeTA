theory LP_Prolog_Stable_Builtins
 imports LP_Prolog_Stable_Type_Identity LP_Prolog_Evaluation_Term_Test
   LP_Prolog_Evaluation_Ground_Disequality LP_Prolog_Evaluation_Rational_Disequality LP_Prolog_Evaluation_Probe
begin

lemma lpp_stable_context_ground_sound:
  assumes observed: "lpp_stable_context_holds operation P ctx eta"
  shows "\<forall>x\<in>lpp_source_context_ground ctx. lp_seg_ground (eta x)"
proof -
  have prior: "lpp_evaluation_context_holds (lpp_stable_scalar_evaluation operation) P ctx eta"
    using observed by (simp add: lpp_stable_context_holds_def)
  show ?thesis by (rule lpp_evaluation_context_ground_sound[where E="lpp_stable_scalar_evaluation operation", OF _ prior])
    (auto dest: lpp_stable_scalar_evaluation_ground)
qed

theorem lpp_stable_term_test_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_term_test T yes_facts no_facts fuel Q nds states contexts Fs nd F ss source_context f a gs active saved yes no"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and actual_step: "lpp_answer_transition P lpp_builtin_signature (lpp_stable_source_builtin operation) (lpc_return_eval eta ss) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_stable_rep operation SP nds states contexts Fs (lpc_return_scope_word swaps tt) u)"
proof -
  have step: "lpp_answer_transition P lpp_builtin_signature lpp_finite_source_builtin (lpc_return_eval eta ss) event tt"
    by (rule lpp_stable_answer_transition_refines[OF actual_step])
  let ?holds = "lpp_var_holds f (lp_ieval a eta)"
  let ?next = "if ?holds then (LPCGoals gs,active)#saved else saved"
  have name: "lpp_var_name f" and shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [a])#gs),active)#saved"
    using checked by (auto simp: lpp_check_evaluation_term_test_def)
  have coverage: "?holds\<in>set (lpp_var_outcomes f (lpcn_ground nd) a)"
    by (rule lpp_var_outcomes_cover[OF name known])
  have link: "lpp_check_evaluation_link T (if ?holds then yes_facts else no_facts)
    fuel Q nds states contexts Fs nd ?next (lpcn_ground nd) (lpcn_guards nd) [] F source_context
    (if ?holds then yes else no)"
    using checked coverage by (auto simp: lpp_check_evaluation_term_test_def list_all_iff)
  have actual: "event=None \<and> tt=lpc_return_eval eta ?next"
    using step by (auto simp: shape lpc_return_eval_def lpp_finite_term_test_step[OF name] split: if_splits)
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  show ?thesis using lpp_stable_link_sound[OF compatible program link equations refl known free observed] actual by auto
qed

theorem lpp_stable_ground_disequality_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_ground_disequality T yes_facts no_facts fuel Q nds states contexts Fs nd F ss source_context a b gs active saved yes no"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and actual_step: "lpp_answer_transition P lpp_builtin_signature (lpp_stable_source_builtin operation) (lpc_return_eval eta ss) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_stable_rep operation SP nds states contexts Fs (lpc_return_scope_word swaps tt) u)"
proof -
  have step: "lpp_answer_transition P lpp_builtin_signature lpp_finite_source_builtin (lpc_return_eval eta ss) event tt"
    by (rule lpp_stable_answer_transition_refines[OF actual_step])
  let ?holds = "lp_ieval a eta \<noteq> lp_ieval b eta"
  let ?next = "if ?holds then (LPCGoals gs,active)#saved else saved"
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser lpp_disequality_predicate) [a,b])#gs),active)#saved"
    and finite: "lp_seg_ground (lp_ieval a eta)" "lp_seg_ground (lp_ieval b eta)"
    using checked known lpp_stable_context_ground_sound[OF observed]
    by (auto simp: lpp_check_evaluation_ground_disequality_def lp_cut_knowledge_def lp_seg_ground_eval)
  have coverage: "?holds\<in>set [False,True]" by auto
  have link: "lpp_check_evaluation_link T (if ?holds then yes_facts else no_facts)
    fuel Q nds states contexts Fs nd ?next (lpcn_ground nd) (lpcn_guards nd) [] F source_context
    (if ?holds then yes else no)"
    using checked coverage by (auto simp: lpp_check_evaluation_ground_disequality_def list_all_iff)
  have actual: "event=None \<and> tt=lpc_return_eval eta ?next"
    using step by (auto simp: shape lpc_return_eval_def lpp_finite_ground_disequality_step[OF finite] split: if_splits)
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  show ?thesis using lpp_stable_link_sound[OF compatible program link equations refl known free observed] actual by auto
qed

theorem lpp_stable_rational_disequality_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_rational_disequality T yes_facts no_facts fuel Q nds states contexts Fs nd F ss source_context a b gs active saved yes no"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and actual_step: "lpp_answer_transition P lpp_builtin_signature (lpp_stable_source_builtin operation) (lpc_return_eval eta ss) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_stable_rep operation SP nds states contexts Fs (lpc_return_scope_word swaps tt) u)"
proof -
  have step: "lpp_answer_transition P lpp_builtin_signature lpp_finite_source_builtin (lpc_return_eval eta ss) event tt"
    by (rule lpp_stable_answer_transition_refines[OF actual_step])
  let ?holds = "\<not>(\<exists>sigma :: string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm. lp_isubst (lp_ieval a eta) sigma=lp_isubst (lp_ieval b eta) sigma)"
  let ?next = "if ?holds then (LPCGoals gs,active)#saved else saved"
  let ?guards = "lpcn_guards nd @ (if ?holds then [LPCEqGuard a b False] else [])"
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser lpp_disequality_predicate) [a,b])#gs),active)#saved"
    using checked by (simp add: lpp_check_evaluation_rational_disequality_def)
  have link: "lpp_check_evaluation_link T (if ?holds then yes_facts else no_facts)
    fuel Q nds states contexts Fs nd ?next (lpcn_ground nd) ?guards [] F source_context
    (if ?holds then yes else no)"
    using checked by (auto simp: lpp_check_evaluation_rational_disequality_def list_all_iff)
  have actual: "event=None \<and> tt=lpc_return_eval eta ?next"
    using step by (auto simp: shape lpc_return_eval_def lpp_rational_disequality_step split: if_splits)
  have extended: "lp_cut_knowledge (set (lpcn_ground nd)) ?guards eta"
    using known by (auto simp: lp_cut_knowledge_def split: if_splits)
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  show ?thesis using lpp_stable_link_sound[OF compatible program link equations refl extended free observed] actual by auto
qed

theorem lpp_stable_probe_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_probe T fs fuel Q nds states contexts Fs nd F ss source_context f g argv m n gs active saved e"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and actual_step: "lpp_answer_transition P lpp_builtin_signature (lpp_stable_source_builtin operation) (lpc_return_eval eta ss) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_stable_rep operation SP nds states contexts Fs (lpc_return_scope_word swaps tt) u)"
proof -
  have step: "lpp_answer_transition P lpp_builtin_signature lpp_finite_source_builtin (lpc_return_eval eta ss) event tt"
    by (rule lpp_stable_answer_transition_refines[OF actual_step])
  let ?next = "lpp_probe_stack (Fun (LPCUser g) argv) (f=''1:once'') m n gs active saved"
  have name: "lpp_probe_name f"
    and shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [Fun (LPCUser g) argv])#gs),active)#saved"
    and fm: "lp_cut_fresh m (LPCGoals gs#map fst saved)"
    and fn: "lp_cut_fresh n (LPCBarrier m#LPCGoals gs#map fst saved)"
    and link: "lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd ?next
      (lpcn_ground nd) (lpcn_guards nd) [] F source_context e"
    using checked by (auto simp only: lpp_check_evaluation_probe_def)
  obtain swaps where event: "event=None"
    and same: "tt=lpc_return_scope_word swaps (lpc_return_eval eta ?next)"
    using lpp_probe_checked_covers[OF name fm fn, where P=P and eta=eta and event=event and tt=tt and g=g and argv=argv and active=active] step
    by (auto simp only: shape)
  have child: "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_stable_rep operation SP nds states contexts Fs (lpc_return_scope_word swaps (lpc_return_eval eta ?next)) u"
    using lpp_stable_link_sound[OF compatible program link _ refl known free observed]
    by (simp add: lp_equations_def)
  show ?thesis using lpc_return_scoped_successor[OF same child] event by blast
qed
ML \<open>
val checked = [@{thm lpp_stable_term_test_sound}, @{thm lpp_stable_ground_disequality_sound}, @{thm lpp_stable_rational_disequality_sound}, @{thm lpp_stable_probe_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable builtin dependency" else ();
\<close>
end
