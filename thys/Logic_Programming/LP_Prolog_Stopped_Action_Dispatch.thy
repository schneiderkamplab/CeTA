theory LP_Prolog_Stopped_Action_Dispatch
  imports LP_Prolog_Stopped_Module_Action LP_Prolog_Shape_Refutation
begin

datatype lpp_stopped_action = LPPSControl lpp_evaluation_action | LPPSUndefined
  | LPPSRefutedShape nat "string lpc_term"

fun lpp_check_stopped_module_action where
  "lpp_check_stopped_module_action T fuel P Q nds states contexts Fs nd F ss source_context returned arity (LPPSControl action) =
    (lpp_stopped_action_supported action \<and>
      lpp_check_evaluation_module_action T fuel P Q nds states contexts Fs nd F ss source_context returned arity action)"
| "lpp_check_stopped_module_action T fuel P Q nds states contexts Fs nd F ss source_context returned arity LPPSUndefined =
    lpp_check_undefined_frame P lpp_builtin_signature ss"

| "lpp_check_stopped_module_action T fuel P Q nds states contexts Fs nd F ss source_context returned arity (LPPSRefutedShape i pattern) =
    lpp_check_shape_refutation fuel source_context i pattern"

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
qed

ML \<open>
val checked = [@{thm lpp_stopped_module_action_contract}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stopped action dispatch dependency" else ();
\<close>
end
