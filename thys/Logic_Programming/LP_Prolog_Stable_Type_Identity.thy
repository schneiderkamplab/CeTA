theory LP_Prolog_Stable_Type_Identity
 imports LP_Prolog_Stable_Cut_Actions LP_Prolog_Evaluation_Integer_Test
begin

lemma lpp_add_stable_integer_holds:
  "lpp_stable_context_holds operation P ctx eta \<Longrightarrow> lpp_is_integer (lp_ieval a eta) \<Longrightarrow>
    lpp_stable_context_holds operation P (lpp_add_integer_observation a ctx) eta"
  by (cases ctx) (auto simp: lpp_stable_context_holds_def lpp_evaluation_context_holds_def)

lemma lpp_add_stable_identity_holds:
  "lpp_stable_context_holds operation P ctx eta \<Longrightarrow>
    lpp_stable_context_holds operation P (lpp_add_identity_observation f a b ctx) eta"
  by (cases ctx) (auto simp: lpp_stable_context_holds_def lpp_evaluation_context_holds_def)

theorem lpp_stable_integer_test_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_integer_test T yes_facts no_facts fuel Q nds states contexts Fs nd F ss source_context a gs active saved yes no"
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
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser ''1:integer'') [a])#gs),active)#saved"
    using checked by (simp add: lpp_check_evaluation_integer_test_def)
  have exact: "\<And>outcome. lpp_finite_source_builtin ''1:integer'' [lp_ieval a eta] outcome =
    lpp_integer_test_outcome (lp_ieval a eta) outcome" by (simp add: lpp_finite_source_builtin_def)
  have actual: "event=None \<and> tt=(if lpp_is_integer (lp_ieval a eta)
    then lpc_return_eval eta ((LPCGoals gs,active)#saved) else lpc_return_eval eta saved)"
    using step by (simp add: shape lpc_return_eval_def lpp_integer_test_step_exact[where U=lpp_finite_source_builtin, OF exact])
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  show ?thesis
  proof (cases "lpp_is_integer (lp_ieval a eta)")
    case True
    have ground: "lp_seg_ground (lp_ieval a eta)"
      using True by (auto simp: lpp_is_integer_def lpp_integer_value_def)
    have extended: "lp_cut_knowledge (set (lpcn_ground nd@sorted_list_of_set (vars_term a))) (lpcn_guards nd) eta"
      using known ground by (auto simp: lp_cut_knowledge_def lp_seg_ground_eval)
    have facts: "lpp_stable_context_holds operation SP (lpp_add_integer_observation a source_context) eta"
      by (rule lpp_add_stable_integer_holds[OF observed True])
    have link: "lpp_check_evaluation_link T yes_facts fuel Q nds states contexts Fs nd ((LPCGoals gs,active)#saved)
      (lpcn_ground nd@sorted_list_of_set (vars_term a)) (lpcn_guards nd) [] F
      (lpp_add_integer_observation a source_context) yes"
      using checked by (simp add: lpp_check_evaluation_integer_test_def)
    show ?thesis using lpp_stable_link_sound[OF compatible program link equations refl extended free facts] actual True by simp
  next
    case False
    have link: "lpp_check_evaluation_link T no_facts fuel Q nds states contexts Fs nd saved
      (lpcn_ground nd) (lpcn_guards nd) [] F source_context no"
      using checked by (simp add: lpp_check_evaluation_integer_test_def)
    show ?thesis using lpp_stable_link_sound[OF compatible program link equations refl known free observed] actual False by simp
  qed
qed

theorem lpp_stable_identity_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_identity T yes_facts no_facts fuel Q nds states contexts Fs nd F ss source_context f a b gs active saved yes no"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and actual_step: "lpp_answer_transition P lpp_builtin_signature (lpp_stable_source_builtin operation) (lpc_return_eval eta ss) event tt"
  shows "event=None \<and> (\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_stable_rep operation SP nds states contexts Fs (lpc_return_scope_word swaps tt) u)"
proof -
  have step: "lpp_answer_transition P lpp_builtin_signature lpp_finite_source_builtin (lpc_return_eval eta ss) event tt"
    by (rule lpp_stable_answer_transition_refines[OF actual_step])
  let ?holds = "lpp_identity_holds f (lp_ieval a eta) (lp_ieval b eta)"
  let ?next = "if ?holds then (LPCGoals gs,active)#saved else saved"
  let ?eqs = "if ?holds=(f=''2:=='') then [(a,b)] else []"
  let ?context = "if ?holds then lpp_add_identity_observation f a b source_context else source_context"
  have name: "lpp_identity_name f" and shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs),active)#saved"
    using checked by (auto simp: lpp_check_evaluation_identity_def)
  have coverage: "?holds\<in>set (lpp_identity_outcomes f a b)"
    by (auto simp: lpp_identity_outcomes_def lpp_identity_holds_def)
  have eqs: "lp_equations ?eqs eta"
    using name by (auto simp: lp_equations_def lpp_identity_holds_def)
  have alternatives: "lpp_check_evaluation_link T (if ?holds then yes_facts else no_facts) fuel Q nds states contexts Fs nd ?next
    (lpcn_ground nd) (lpcn_guards nd) ?eqs F ?context (if ?holds then yes else no) \<or>
    lpp_check_evaluation_link T (if ?holds then yes_facts else no_facts) fuel Q nds states contexts Fs nd ?next
    (lpcn_ground nd) (lpcn_guards nd) [] F ?context (if ?holds then yes else no)"
    using checked coverage by (auto simp: lpp_check_evaluation_identity_def list_all_iff)
  let ?chosen = "if lpp_check_evaluation_link T (if ?holds then yes_facts else no_facts) fuel Q nds states contexts Fs nd ?next
    (lpcn_ground nd) (lpcn_guards nd) ?eqs F ?context (if ?holds then yes else no) then ?eqs else []"
  have valid: "lp_equations ?chosen eta"
    using eqs by (auto simp: lp_equations_def)
  have link: "lpp_check_evaluation_link T (if ?holds then yes_facts else no_facts) fuel Q nds states contexts Fs nd ?next
    (lpcn_ground nd) (lpcn_guards nd) ?chosen F ?context (if ?holds then yes else no)"
    using alternatives by (auto split: if_splits)
  have actual: "event=None \<and> tt=lpc_return_eval eta ?next"
    using step by (auto simp: shape lpc_return_eval_def lpp_finite_identity_step[OF name] split: if_splits)
  have facts: "lpp_stable_context_holds operation SP ?context eta"
    using observed lpp_add_stable_identity_holds[OF observed] by (auto split: if_splits)
  show ?thesis using lpp_stable_link_sound[OF compatible program link valid refl known free facts] actual by auto
qed
ML \<open>
val checked = [@{thm lpp_stable_integer_test_sound}, @{thm lpp_stable_identity_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable type/identity dependency" else ();
\<close>
end
