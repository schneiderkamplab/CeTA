theory LP_Prolog_Context_Free_Source
 imports LP_Prolog_Context_Free_Identity LP_Prolog_Context_Free_Is_Constant LP_Prolog_Context_Free_Cut_Actions LP_Prolog_Context_Source_Actions
begin

fun lpp_context_cut_part where
  "lpp_context_cut_part (LPPCSPrimitive (LPPIRCut action)) = Some action"
| "lpp_context_cut_part _ = None"

definition lpp_check_context_free_ordinary where
  "lpp_check_context_free_ordinary fuel P Q nds states contexts Fs nd F ss source_context returned arity action =
    (case lpp_context_cut_part action of Some local_action \<Rightarrow>
       lpp_no_builtin_frame ss \<and>
       lpp_check_context_free_cut_action fuel P Q nds states contexts Fs nd F ss source_context returned arity local_action
     | None \<Rightarrow>
       length Fs=length nds \<and> list_all (\<lambda>xs. xs=[]) Fs \<and>
       lpp_check_context_source_action fuel P Q nds states contexts nd ss source_context returned arity action)"

lemma lpp_context_rep_empty_free:
  assumes rep: "lpp_context_return_rep SP nds states contexts ss t"
    and length: "length Fs=length nds"
    and empty: "list_all (\<lambda>xs. xs=[]) Fs"
  shows "lpp_context_free_rep SP nds states contexts Fs ss t"
proof -
  obtain i eta where index: "i<length nds" and state: "i<length states"
    and context_bound: "i<length contexts" and shape: "ss=lpc_return_eval eta (states!i)"
    and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
    and observed: "lpp_source_context_holds SP (contexts!i) eta"
    and t: "t=[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]"
    using rep by (auto simp: lpp_context_return_rep_def)
  have bound: "i<length Fs" using index length by simp
  have member: "Fs!i\<in>set Fs" by (rule nth_mem[OF bound])
  have nil: "Fs!i=[]" using empty member by (auto simp: list_all_iff)
  have free: "lpc_free_knowledge (set (Fs!i)) eta"
    by (simp add: nil lpc_free_knowledge_def)
  show ?thesis unfolding lpp_context_free_rep_def
    by (rule exI[of _ i], rule exI[of _ eta])
      (use index state context_bound shape known observed t free length in auto)
qed

theorem lpp_context_free_ordinary_sound:
  assumes checked: "lpp_check_context_free_ordinary fuel P Q nds states contexts Fs nd F ss source_context returned arity action"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_source_context_holds SP source_context eta"
    and integers: "lpp_integer_known (lpp_context_source_types action) eta"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin (lpc_return_eval eta ss) event tt"
  shows "(\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
      lpp_context_free_rep SP nds states contexts Fs (lpc_return_scope_word swaps tt) u) \<and>
    (\<forall>rho. event=Some rho \<longrightarrow>
      ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*)"
proof (cases "lpp_context_cut_part action")
  case (Some local_action)
  have clear: "lpp_no_builtin_frame ss"
    and check: "lpp_check_context_free_cut_action fuel P Q nds states contexts Fs nd F ss source_context returned arity local_action"
    using checked Some by (auto simp: lpp_check_context_free_ordinary_def)
  show ?thesis by (rule lpp_context_free_cut_action_sound[OF check known free observed
    lpp_integer_source_nonbuiltin_base[OF clear step]])
next
  case None
  have check: "lpp_check_context_source_action fuel P Q nds states contexts nd ss source_context returned arity action"
    and length: "length Fs=length nds" and empty: "list_all (\<lambda>xs. xs=[]) Fs"
    using checked None by (auto simp: lpp_check_context_free_ordinary_def)
  show ?thesis using lpp_context_source_action_sound[OF check known observed integers step]
    lpp_context_rep_empty_free[OF _ length empty] by blast
qed

lemma lpp_context_free_ordinary_domain:
  assumes checked: "lpp_check_context_free_ordinary fuel P Q nds states contexts Fs nd F ss source_context returned arity action"
    and integers: "lpp_integer_known (lpp_context_source_types action) eta"
  shows "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_integer_source_domain (map fst (lpc_return_eval eta ss))"
proof (cases "lpp_context_cut_part action")
  case (Some local_action)
  have "lpp_no_builtin_frame ss" using checked Some by (simp add: lpp_check_context_free_ordinary_def)
  then show ?thesis by (auto dest: lpp_no_builtin_frame_sound lpp_no_builtin_domain_bad)
next
  case None
  have check: "lpp_check_context_source_action fuel P Q nds states contexts nd ss source_context returned arity action"
    using checked None by (simp add: lpp_check_context_free_ordinary_def)
  show ?thesis by (rule lpp_context_source_action_domain[OF check integers])
qed

fun lpp_check_context_free_source where
  "lpp_check_context_free_source fuel P Q nds states contexts Fs nd F ss source_context returned arity
    (LPPCSPrimitive action) =
      lpp_check_context_free_ordinary fuel P Q nds states contexts Fs nd F ss source_context returned arity (LPPCSPrimitive action)"
| "lpp_check_context_free_source fuel P Q nds states contexts Fs nd F ss source_context returned arity
    (LPPCSStagedIs K evidence a e gs active saved result_var middle action) =
      lpp_check_context_free_is_staged fuel P Q nds states contexts Fs nd F ss source_context K evidence a e gs active saved result_var middle returned arity action"

| "lpp_check_context_free_source fuel P Q nds states contexts Fs nd F ss source_context returned arity
    (LPPCSConstantIs evidence a e gs active saved middle action) =
      lpp_check_context_free_is_constant fuel P Q nds states contexts Fs nd F ss source_context evidence a e gs active saved middle returned arity action"

| "lpp_check_context_free_source fuel P Q nds states contexts Fs nd F ss source_context returned arity
    (LPPCSIdentity f a b gs active saved yes no) = lpp_check_context_free_identity fuel Q nds states contexts Fs nd F ss source_context f a b gs active saved yes no"

theorem lpp_context_free_source_sound:
  assumes checked: "lpp_check_context_free_source fuel P Q nds states contexts Fs nd F ss source_context returned arity action"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_source_context_holds SP source_context eta"
    and integers: "lpp_integer_known (lpp_context_source_types action) eta"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin (lpc_return_eval eta ss) event tt"
  shows "(\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
      lpp_context_free_rep SP nds states contexts Fs (lpc_return_scope_word swaps tt) u) \<and>
    (\<forall>rho. event=Some rho \<longrightarrow>
      ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*)"
proof (cases action)
  case (LPPCSPrimitive primitive)
  have check: "lpp_check_context_free_ordinary fuel P Q nds states contexts Fs nd F ss source_context returned arity (LPPCSPrimitive primitive)"
    and typed: "lpp_integer_known (lpp_context_source_types (LPPCSPrimitive primitive)) eta"
    using checked integers LPPCSPrimitive by simp_all
  show ?thesis by (rule lpp_context_free_ordinary_sound[OF check known free observed typed step])
next
  case (LPPCSStagedIs K evidence a e gs active saved result_var middle primitive)
  have check: "lpp_check_context_free_is_staged fuel P Q nds states contexts Fs nd F ss source_context K evidence a e gs active saved result_var middle returned arity primitive"
    and typed: "lpp_integer_known K eta"
    using checked integers LPPCSStagedIs by simp_all
  show ?thesis using lpp_context_free_is_staged_sound[OF check known free observed typed step] by auto
next
  case (LPPCSConstantIs evidence a e gs active saved middle primitive)
  have check: "lpp_check_context_free_is_constant fuel P Q nds states contexts Fs nd F ss source_context evidence a e gs active saved middle returned arity primitive"
    using checked LPPCSConstantIs by simp
  show ?thesis using lpp_context_free_is_constant_sound[OF check known free observed step] by auto
next
  case (LPPCSIdentity f a b gs active saved yes no)
  have check: "lpp_check_context_free_identity fuel Q nds states contexts Fs nd F ss source_context f a b gs active saved yes no"
    using checked LPPCSIdentity by simp
  show ?thesis using lpp_context_free_identity_sound[OF check known free observed step] by auto
qed

lemma lpp_context_free_source_domain:
  assumes checked: "lpp_check_context_free_source fuel P Q nds states contexts Fs nd F ss source_context returned arity action"
    and integers: "lpp_integer_known (lpp_context_source_types action) eta"
  shows "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_integer_source_domain (map fst (lpc_return_eval eta ss))"
proof (cases action)
  case (LPPCSPrimitive primitive)
  show ?thesis by (rule lpp_context_free_ordinary_domain)
    (use checked integers LPPCSPrimitive in auto)
next
  case (LPPCSStagedIs K evidence a e gs active saved result_var middle primitive)
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved"
    and expr: "e=lpp_expression_term evidence" and typed: "lpp_expression_check K evidence"
    and known: "lpp_integer_known K eta"
    using checked integers LPPCSStagedIs by (auto simp: lpp_check_context_free_is_staged_def)
  obtain n where "lpp_integer_evaluation (lp_ieval e eta) n"
    using lpp_checked_expression_finishes[OF typed known] expr by blast
  then show ?thesis by (auto simp: shape lpc_return_eval_def)
next
  case (LPPCSConstantIs evidence a e gs active saved middle primitive)
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved"
    and expr: "e=lpp_expression_term evidence" and typed: "lpp_expression_check [] evidence"
    using checked LPPCSConstantIs by (auto simp: lpp_check_context_free_is_constant_def)
  have evaluated: "lpp_integer_evaluation (lp_ieval e eta) (lpp_expression_value evidence (\<lambda>_. 0))"
    unfolding expr by (rule lpp_expression_evaluation[OF typed]) simp
  then show ?thesis by (auto simp: shape lpc_return_eval_def)
next
  case (LPPCSIdentity f a b gs active saved yes no)
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs),active)#saved"
    and name: "lpp_identity_name f"
    using checked LPPCSIdentity by (auto simp: lpp_check_context_free_identity_def)
  have domain: "lpp_integer_source_domain f [lp_ieval a eta,lp_ieval b eta]"
    by (rule lpp_identity_source_domain[OF name])
  show ?thesis using domain
    by (simp add: shape lpc_return_eval_def del: lpp_integer_source_domain.simps)
qed

end
