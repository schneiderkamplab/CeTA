theory LP_Prolog_Stopped_Action_Dispatch
  imports LP_Prolog_Stopped_Module_Action LP_Prolog_Shape_Refutation LP_Prolog_Stopped_Integer_Result_Is
begin

datatype lpp_stopped_action = LPPSControl lpp_evaluation_action | LPPSUndefined
  | LPPSRefutedShape nat "string lpc_term"
  | LPPSIntegerResultIs "string lpp_integer_result_receipt" "string lpc_term" "string lpc_term"
      "string lpc_term lp_cut_goal list" "string lpc_term list" "string lpc_return_state"
      string "string lpc_link" lpp_link_types

fun lpp_check_stopped_module_action where
  "lpp_check_stopped_module_action T fuel P Q nds states contexts Fs nd F ss source_context returned arity (LPPSControl action) =
    (lpp_stopped_action_supported action \<and>
      lpp_check_evaluation_module_action T fuel P Q nds states contexts Fs nd F ss source_context returned arity action)"
| "lpp_check_stopped_module_action T fuel P Q nds states contexts Fs nd F ss source_context returned arity LPPSUndefined =
    lpp_check_undefined_frame P lpp_builtin_signature ss"

| "lpp_check_stopped_module_action T fuel P Q nds states contexts Fs nd F ss source_context returned arity (LPPSRefutedShape i pattern) =
    lpp_check_shape_refutation fuel source_context i pattern"

| "lpp_check_stopped_module_action T fuel P Q nds states contexts Fs nd F ss source_context returned arity
    (LPPSIntegerResultIs domain_receipt a e gs active saved result_var middle fs) =
    lpp_check_integer_result_is domain_receipt T fs fuel P Q nds states contexts Fs nd F ss source_context a e gs active saved result_var middle"

theorem lpp_stopped_module_action_contract:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_stopped_module_action T fuel P Q nds states contexts Fs nd F ss source_context returned arity action"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and invariant: "J (lpc_return_eval eta ss)"
    and stable: "\<And>xs ev ys. lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature) xs ev ys \<Longrightarrow> J xs \<Longrightarrow> J ys"
    and frames: "\<And>xs ys. map snd xs=map snd ys \<Longrightarrow> J ys \<Longrightarrow> J xs"
    and subset: "\<And>xs ys. set xs\<subseteq> set ys \<Longrightarrow> J ys \<Longrightarrow> J xs"
    and lower: "\<And>vs v. ([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      lpp_stable_module_rep operation SP nds states contexts Fs vs v \<Longrightarrow> J vs \<Longrightarrow> lp_answer_contract (lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature)) vs R t ret"
    and emit: "\<And>rho tt. lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature) (lpc_return_eval eta ss) (Some rho) tt \<Longrightarrow> (t,ret rho)\<in>R\<^sup>*"
  shows "lp_answer_contract (lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature)) (lpc_return_eval eta ss) R t ret"
proof (cases action)
  case (LPPSControl control)
  have check: "lpp_check_evaluation_module_action T fuel P Q nds states contexts Fs nd F ss source_context returned arity control"
    and supported: "lpp_stopped_action_supported control"
    using checked LPPSControl by auto
  show ?thesis
    by (rule lpp_stopped_control_action[where J=J, OF compatible transfer check supported known free observed invariant])
      (fact stable, fact frames, fact subset, fact lower, fact emit)
next
  case LPPSUndefined
  have check: "lpp_check_undefined_frame P lpp_builtin_signature ss"
    using checked LPPSUndefined by simp
  show ?thesis by (rule lpp_undefined_frame_contract[OF check])
next
  case (LPPSRefutedShape i pattern)
  have check: "lpp_check_shape_refutation fuel source_context i pattern"
    using checked LPPSRefutedShape by simp
  show ?thesis using lpp_stable_shape_refutation_sound[OF check observed] by blast
next
  case (LPPSIntegerResultIs domain_receipt a e gs active saved result_var middle fs)
  have check: "lpp_check_integer_result_is domain_receipt T fs fuel P Q nds states contexts Fs nd F ss source_context a e gs active saved result_var middle"
    using checked LPPSIntegerResultIs by simp
  have bounds: "lpcl_target middle<length nds \<and> lpcl_target middle<length states \<and>
    lpcl_target middle<length contexts \<and> lpcl_target middle<length Fs"
    using check by (auto simp: lpp_check_integer_result_is_def lpp_check_evaluation_link_def lpc_check_return_table_link_def lpc_check_return_link_def lpc_check_link_def)
  show ?thesis
  proof (rule lpp_stopped_integer_result_is_contract[where J=J, OF compatible transfer check known free observed invariant frames])
    fix rho
    assume edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],
      [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>(lp_ild Q)\<^sup>+"
      and knowledge: "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho"
      and child_free: "lpc_free_knowledge (set (Fs!lpcl_target middle)) rho"
      and child_context: "lpp_stable_context_holds operation SP (contexts!lpcl_target middle) rho"
      and inv: "J (lpc_return_eval rho (states!lpcl_target middle))"
    have represented: "lpp_stable_module_rep operation SP nds states contexts Fs
      (lpc_return_eval rho (states!lpcl_target middle))
      [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))]"
      unfolding lpp_stable_module_rep_def lpp_stable_rep_def
      by (rule exI[of _ "[]"], rule exI[of _ "lpcl_target middle"], rule exI[of _ rho])
        (use bounds knowledge child_free child_context in auto)
    show "lp_answer_contract (lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature))
      (lpc_return_eval rho (states!lpcl_target middle)) R t ret"
      by (rule lower[OF edge represented inv])
  qed
qed

ML \<open>
val checked = [@{thm lpp_stopped_module_action_contract}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stopped action dispatch dependency" else ();
\<close>
end
