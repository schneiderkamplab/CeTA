theory LP_Prolog_Context_Identity
 imports LP_Prolog_Context_Table
begin

fun lpp_add_identity_observation where
  "lpp_add_identity_observation f a b (facts,guards,observations) =
    (facts,guards@[LPPSOpaque (Fun (LPCUser f) [a,b])],observations)"
lemma lpp_add_identity_observation_holds:
  "lpp_source_context_holds SP source_context eta \<Longrightarrow>
    lpp_source_context_holds SP (lpp_add_identity_observation f a b source_context) eta"
  by (cases source_context) (auto simp: lpp_path_context_holds_def)

lemma lpp_integer_identity_step:
  assumes name: "lpp_identity_name f"
  shows "lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin
      ((LPCGoals (LPCAtom (LPIFun (LPCUser f) [a,b])#gs),eta)#saved) event tt
    \<longleftrightarrow> event=None \<and>
      tt=(if lpp_identity_holds f a b then (LPCGoals gs,eta)#saved else saved)"
proof -
  have selected: "(f,length [a,b])\<in>lpp_builtin_signature"
    using lpp_identity_selected[OF name] by (simp add: numeral_2_eq_2)
  have exact: "\<And>outcome. lpp_integer_source_builtin f [a,b] outcome = lpp_test_builtin f [a,b] outcome"
    by (rule lpp_integer_source_legacy) (use name in auto)
  show ?thesis using lpp_selected_builtin_cong[where U=lpp_integer_source_builtin and V=lpp_test_builtin, OF selected exact]
    lpp_identity_step_exact[OF name] by blast
qed

lemma lpp_identity_source_domain:
  "lpp_identity_name f \<Longrightarrow> lpp_integer_source_domain f [a,b]"
proof -
  assume name: "lpp_identity_name f"
  have ni: "f\<noteq>''1:integer''" and ne: "f\<noteq>''2:is''"
    using name by (auto simp: lpp_identity_name_def)
  have nc: "lpp_source_comparison f=None"
    using name by (auto simp only: lpp_identity_name_def lpp_source_comparison_legacy_names)
  show ?thesis
    by (simp only: lpp_integer_source_domain.simps ni ne if_False nc option.case)
      (use name in simp)
qed
definition lpp_check_context_identity where
  "lpp_check_context_identity fuel Q nds states contexts nd ss source_context f a b gs active saved yes no =
    (lpp_identity_name f \<and> ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs),active)#saved \<and>
     list_all (\<lambda>holds. (lpp_check_context_table_link fuel Q nds states contexts nd
       (if holds then (LPCGoals gs,active)#saved else saved)
       (lpcn_ground nd) (lpcn_guards nd)
       (if holds=(f=''2:=='') then [(a,b)] else [])
       (if holds then lpp_add_identity_observation f a b source_context else source_context)
       (if holds then yes else no) \<or>
       lpp_check_context_table_link fuel Q nds states contexts nd
       (if holds then (LPCGoals gs,active)#saved else saved)
       (lpcn_ground nd) (lpcn_guards nd)
       []
       (if holds then lpp_add_identity_observation f a b source_context else source_context)
       (if holds then yes else no))) (lpp_identity_outcomes f a b))"

theorem lpp_context_identity_sound:
  assumes checked: "lpp_check_context_identity fuel Q nds states contexts nd ss source_context f a b gs active saved yes no"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and observed: "lpp_source_context_holds SP source_context eta"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin (lpc_return_eval eta ss) event tt"
  shows "event=None \<and> (\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_context_return_rep SP nds states contexts (lpc_return_scope_word swaps tt) u)"
proof -
  let ?holds = "lpp_identity_holds f (lp_ieval a eta) (lp_ieval b eta)"
  let ?next = "if ?holds then (LPCGoals gs,active)#saved else saved"
  let ?eqs = "if ?holds=(f=''2:=='') then [(a,b)] else []"
  let ?context = "if ?holds then lpp_add_identity_observation f a b source_context else source_context"
  have name: "lpp_identity_name f" and shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs),active)#saved"
    using checked by (auto simp: lpp_check_context_identity_def)
  have coverage: "?holds\<in>set (lpp_identity_outcomes f a b)"
    by (auto simp: lpp_identity_outcomes_def lpp_identity_holds_def)
  have eqs: "lp_equations ?eqs eta"
    using name by (auto simp: lp_equations_def lpp_identity_holds_def)
  have alternatives: "lpp_check_context_table_link fuel Q nds states contexts nd ?next
    (lpcn_ground nd) (lpcn_guards nd) ?eqs ?context (if ?holds then yes else no) \<or>
    lpp_check_context_table_link fuel Q nds states contexts nd ?next
    (lpcn_ground nd) (lpcn_guards nd) [] ?context (if ?holds then yes else no)"
    using checked coverage by (auto simp: lpp_check_context_identity_def list_all_iff)
  let ?chosen = "if lpp_check_context_table_link fuel Q nds states contexts nd ?next
    (lpcn_ground nd) (lpcn_guards nd) ?eqs ?context (if ?holds then yes else no) then ?eqs else []"
  have valid: "lp_equations ?chosen eta"
    using eqs by (auto simp: lp_equations_def)
  have link: "lpp_check_context_table_link fuel Q nds states contexts nd ?next
    (lpcn_ground nd) (lpcn_guards nd) ?chosen ?context (if ?holds then yes else no)"
    using alternatives by (auto split: if_splits)
  have actual: "event=None \<and> tt=lpc_return_eval eta ?next"
    using step by (auto simp: shape lpc_return_eval_def lpp_integer_identity_step[OF name] split: if_splits)
  have facts: "lpp_source_context_holds SP ?context eta"
    using observed lpp_add_identity_observation_holds[OF observed] by (auto split: if_splits)
  show ?thesis using lpp_context_table_link_sound[OF link valid refl known facts] actual by auto
qed
end
