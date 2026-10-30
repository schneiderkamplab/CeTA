theory LP_Prolog_Context_Source_Actions
  imports LP_Prolog_Context_Is_Constant LP_Prolog_Context_Identity
begin

datatype lpp_context_source_action = LPPCSPrimitive lpp_integer_return_action
  | LPPCSStagedIs "string list" "string lpp_integer_expression" "string lpc_term" "string lpc_term"
      "string lpc_term lp_cut_goal list" "string lpc_term list" "string lpc_return_state"
      string "string lpc_link" "string lpc_return_action"
  | LPPCSConstantIs "string lpp_integer_expression" "string lpc_term" "string lpc_term"
      "string lpc_term lp_cut_goal list" "string lpc_term list" "string lpc_return_state"
      "string lpc_link" "string lpc_return_action"
  | LPPCSIdentity string "string lpc_term" "string lpc_term"
      "string lpc_term lp_cut_goal list" "string lpc_term list" "string lpc_return_state"
      "string lpc_link" "string lpc_link"
fun lpp_context_source_types where
  "lpp_context_source_types (LPPCSPrimitive action) = lpp_integer_action_types action"
| "lpp_context_source_types (LPPCSStagedIs K evidence a e gs active saved result_var middle action) = K"
| "lpp_context_source_types (LPPCSConstantIs evidence a e gs active saved middle action) = []"
| "lpp_context_source_types (LPPCSIdentity f a b gs active saved yes no) = []"
fun lpp_check_context_source_action where
  "lpp_check_context_source_action fuel P Q nds states contexts nd ss source_context returned arity (LPPCSPrimitive action) =
    lpp_check_context_action fuel P Q nds states contexts nd ss source_context returned arity action"
| "lpp_check_context_source_action fuel P Q nds states contexts nd ss source_context returned arity
    (LPPCSStagedIs K evidence a e gs active saved result_var middle action) =
    lpp_check_context_is_staged fuel P Q nds states contexts nd ss source_context K evidence a e gs active saved result_var middle returned arity action"

| "lpp_check_context_source_action fuel P Q nds states contexts nd ss source_context returned arity
    (LPPCSConstantIs evidence a e gs active saved middle action) =
    lpp_check_context_is_constant fuel P Q nds states contexts nd ss source_context evidence a e gs active saved middle returned arity action"

| "lpp_check_context_source_action fuel P Q nds states contexts nd ss source_context returned arity
    (LPPCSIdentity f a b gs active saved yes no) = lpp_check_context_identity fuel Q nds states contexts nd ss source_context f a b gs active saved yes no"

theorem lpp_context_source_action_sound:
  assumes checked: "lpp_check_context_source_action fuel P Q nds states contexts nd ss source_context returned arity action"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and observed: "lpp_source_context_holds SP source_context eta"
    and integers: "lpp_integer_known (lpp_context_source_types action) eta"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin (lpc_return_eval eta ss) event tt"
  shows "(\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
      lpp_context_return_rep SP nds states contexts (lpc_return_scope_word swaps tt) u) \<and>
    (\<forall>rho. event=Some rho \<longrightarrow>
      ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*)"
proof (cases action)
  case (LPPCSPrimitive primitive)
  show ?thesis using lpp_context_action_sound[OF _ known observed _ step] checked integers LPPCSPrimitive by simp
next
  case (LPPCSStagedIs K evidence a e gs active saved result_var middle primitive)
  have check: "lpp_check_context_is_staged fuel P Q nds states contexts nd ss source_context K evidence a e gs active saved result_var middle returned arity primitive"
    and typed: "lpp_integer_known K eta" using checked integers LPPCSStagedIs by simp_all
  show ?thesis using lpp_context_is_staged_sound[OF check known observed typed step] by auto
next
  case (LPPCSConstantIs evidence a e gs active saved middle primitive)
  have check: "lpp_check_context_is_constant fuel P Q nds states contexts nd ss source_context evidence a e gs active saved middle returned arity primitive"
    using checked LPPCSConstantIs by simp
  show ?thesis using lpp_context_is_constant_sound[OF check known observed step] by auto
next
  case (LPPCSIdentity f a b gs active saved yes no)
  have check: "lpp_check_context_identity fuel Q nds states contexts nd ss source_context f a b gs active saved yes no"
    using checked LPPCSIdentity by simp
  show ?thesis using lpp_context_identity_sound[OF check known observed step] by auto
qed

lemma lpp_context_source_action_domain:
  assumes checked: "lpp_check_context_source_action fuel P Q nds states contexts nd ss source_context returned arity action"
    and integers: "lpp_integer_known (lpp_context_source_types action) eta"
  shows "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_integer_source_domain (map fst (lpc_return_eval eta ss))"
proof (cases action)
  case (LPPCSPrimitive primitive)
  have check: "lpp_check_context_action fuel P Q nds states contexts nd ss source_context returned arity primitive"
    and typed: "lpp_integer_known (lpp_integer_action_types primitive) eta"
    using checked integers LPPCSPrimitive by simp_all
  show ?thesis by (rule lpp_context_action_domain[OF check typed])
next
  case (LPPCSStagedIs K evidence a e gs active saved result_var middle primitive)
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved"
    and expr: "e=lpp_expression_term evidence" and typed: "lpp_expression_check K evidence"
    and known: "lpp_integer_known K eta"
    using checked integers LPPCSStagedIs by (auto simp: lpp_check_context_is_staged_def)
  obtain n where "lpp_integer_evaluation (lp_ieval e eta) n"
    using lpp_checked_expression_finishes[OF typed known] expr by blast
  then show ?thesis by (auto simp: shape lpc_return_eval_def)
next
  case (LPPCSConstantIs evidence a e gs active saved middle primitive)
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved"
    and expr: "e=lpp_expression_term evidence" and typed: "lpp_expression_check [] evidence"
    using checked LPPCSConstantIs by (auto simp: lpp_check_context_is_constant_def)
  have evaluated: "lpp_integer_evaluation (lp_ieval e eta) (lpp_expression_value evidence (\<lambda>_. 0))"
    unfolding expr by (rule lpp_expression_evaluation[OF typed]) simp
  then show ?thesis by (auto simp: shape lpc_return_eval_def)
next
  case (LPPCSIdentity f a b gs active saved yes no)
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs),active)#saved"
    and name: "lpp_identity_name f"
    using checked LPPCSIdentity by (auto simp: lpp_check_context_identity_def)
  have domain: "lpp_integer_source_domain f [lp_ieval a eta,lp_ieval b eta]"
    by (rule lpp_identity_source_domain[OF name])
  show ?thesis using domain
    by (simp add: shape lpc_return_eval_def del: lpp_integer_source_domain.simps)
qed
end
