theory LP_Prolog_Evaluation_Choice
 imports LP_Prolog_Finite_Choice LP_Prolog_Evaluation_Allocate
begin

definition lpp_choice_stack where
  "lpp_choice_stack left right gs active saved =
    (LPCGoals (left@gs),active)#(LPCGoals (right@gs),active)#saved"

lemma lpp_choice_checked_covers:
  assumes choice: "lpp_choice_source_left a"
    and lower: "lpp_branch_lower_term a=Some left" "lpp_branch_lower_term b=Some right"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_finite_source_builtin
      (lpc_return_eval eta ((LPCGoals (LPCAtom (Fun (LPCUser ''2:;'') [a,b])#gs),active)#saved)) event tt"
  shows "event=None \<and> tt=lpc_return_eval eta (lpp_choice_stack left right gs active saved)"
proof -
  have actual: "lpp_answer_transition P lpp_builtin_signature lpp_finite_source_builtin
    ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:;'') [lp_ieval a eta,lp_ieval b eta])#
      map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),lpc_return_env active eta)#
      lpc_return_eval eta saved) event tt"
    using step by (simp add: lpc_return_eval_def)
  show ?thesis using lpp_finite_choice_step[OF lpp_choice_source_left_sound[OF choice]
      lpp_branch_lower_term_sound[OF lower(1)] lpp_branch_lower_term_sound[OF lower(2)] actual]
    by (simp add: lpc_return_eval_def lpp_choice_stack_def)
qed

definition lpp_check_evaluation_choice where
  "lpp_check_evaluation_choice T fs fuel Q nds states contexts Fs nd F ss source_context a b left right gs active saved e =
    (lpp_choice_source_left a \<and> lpp_branch_lower_term a=Some left \<and> lpp_branch_lower_term b=Some right \<and>
     ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:;'') [a,b])#gs),active)#saved \<and>
     lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd
       (lpp_choice_stack left right gs active saved)
       (lpcn_ground nd) (lpcn_guards nd) [] F source_context e)"

theorem lpp_evaluation_choice_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes contract: "lpp_eval_integer_contract TYPE(string) E"
    and evaluation: "\<And>e t. E e t \<Longrightarrow> lp_seg_ground e \<and> lp_seg_ground t"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_choice T fs fuel Q nds states contexts Fs nd F ss source_context a b left right gs active saved e"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_evaluation_context_holds E SP source_context eta"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_finite_source_builtin (lpc_return_eval eta ss) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_evaluation_rep E SP nds states contexts Fs (lpc_return_scope_word swaps tt) u)"
proof -
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
    lpp_evaluation_rep E SP nds states contexts Fs (lpc_return_scope_word swaps (lpc_return_eval eta ?next)) u"
    using lpp_evaluation_link_sound[OF contract evaluation program link _ refl known free observed]
    by (simp add: lp_equations_def)
  show ?thesis using child event by (simp only: same)
qed

lemma lpp_evaluation_choice_domain:
  assumes checked: "lpp_check_evaluation_choice T fs fuel Q nds states contexts Fs nd F ss source_context a b left right gs active saved e"
  shows "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_finite_source_domain (map fst (lpc_return_eval eta ss))"
  using checked lpp_finite_choice_domain[of a left b right eta]
  by (auto simp: lpp_check_evaluation_choice_def lpc_return_eval_def)
end
