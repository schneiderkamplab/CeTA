theory LP_Prolog_Stable_Choice
 imports LP_Prolog_Stable_Builtins LP_Prolog_Evaluation_Choice
begin

theorem lpp_stable_choice_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_choice T fs fuel Q nds states contexts Fs nd F ss source_context a b left right gs active saved e"
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
  let ?next = "lpp_choice_stack left right gs active saved"
  have choice: "lpp_choice_source_left a"
    and lower: "lpp_branch_lower_term a=Some left" "lpp_branch_lower_term b=Some right"
    and shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:;'') [a,b])#gs),active)#saved"
    and link: "lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd ?next
      (lpcn_ground nd) (lpcn_guards nd) [] F source_context e"
    using checked by (auto simp only: lpp_check_evaluation_choice_def)
  have event: "event=None" and same: "tt=lpc_return_eval eta ?next"
    using lpp_choice_checked_covers[OF choice lower, where P=P and eta=eta and event=event and tt=tt and active=active] step
    by (auto simp only: shape)
  have child: "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_stable_rep operation SP nds states contexts Fs (lpc_return_scope_word swaps (lpc_return_eval eta ?next)) u"
    using lpp_stable_link_sound[OF compatible program link _ refl known free observed]
    by (simp add: lp_equations_def)
  show ?thesis using child event by (simp only: same)
qed

end
