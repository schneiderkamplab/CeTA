theory LP_Prolog_Evaluation_Identity
 imports LP_Prolog_Evaluation_Comparison
begin

lemma lpp_add_evaluation_identity_holds:
  "lpp_evaluation_context_holds E SP source_context eta \<Longrightarrow>
   lpp_evaluation_context_holds E SP (lpp_add_identity_observation f a b source_context) eta"
  by (cases source_context) (auto simp: lpp_evaluation_context_holds_def)

definition lpp_check_evaluation_identity where
  "lpp_check_evaluation_identity T yes_facts no_facts fuel Q nds states contexts Fs nd F ss source_context f a b gs active saved yes no =
    (lpp_identity_name f \<and> ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs),active)#saved \<and>
     list_all (\<lambda>holds. (lpp_check_evaluation_link T (if holds then yes_facts else no_facts) fuel Q nds states contexts Fs nd
       (if holds then (LPCGoals gs,active)#saved else saved)
       (lpcn_ground nd) (lpcn_guards nd)
       (if holds=(f=''2:=='') then [(a,b)] else []) F
       (if holds then lpp_add_identity_observation f a b source_context else source_context)
       (if holds then yes else no) \<or>
       lpp_check_evaluation_link T (if holds then yes_facts else no_facts) fuel Q nds states contexts Fs nd
       (if holds then (LPCGoals gs,active)#saved else saved)
       (lpcn_ground nd) (lpcn_guards nd)
       [] F
       (if holds then lpp_add_identity_observation f a b source_context else source_context)
       (if holds then yes else no))) (lpp_identity_outcomes f a b))"

theorem lpp_evaluation_identity_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes contract: "lpp_eval_integer_contract TYPE(string) E"
    and evaluation: "\<And>e t. E e t \<Longrightarrow> lp_seg_ground e \<and> lp_seg_ground t"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_identity T yes_facts no_facts fuel Q nds states contexts Fs nd F ss source_context f a b gs active saved yes no"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_evaluation_context_holds E SP source_context eta"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_finite_source_builtin (lpc_return_eval eta ss) event tt"
  shows "event=None \<and> (\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_evaluation_rep E SP nds states contexts Fs (lpc_return_scope_word swaps tt) u)"
proof -
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
  have facts: "lpp_evaluation_context_holds E SP ?context eta"
    using observed lpp_add_evaluation_identity_holds[OF observed] by (auto split: if_splits)
  show ?thesis using lpp_evaluation_link_sound[OF contract evaluation program link valid refl known free facts] actual by auto
qed
end
