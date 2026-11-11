theory LP_Prolog_Stopped_Module_Action
  imports LP_Prolog_Stopped_Constant LP_Prolog_Stopped_Observed_Is
    LP_Prolog_Stopped_Modular LP_Prolog_Undefined_Frame
begin

text \<open>The existing action witnesses and source graph are retained. Unsupported
stopped contracts remain explicit obligations; they are never erased.\<close>

fun lpp_stopped_action_supported where
  "lpp_stopped_action_supported (LPPEFiniteLength a e gs active saved result_var middle fs) = False"
| "lpp_stopped_action_supported (LPPESubtractLibrary e s a gs active saved middle fs) = False"
| "lpp_stopped_action_supported _ = True"

theorem lpp_stopped_control_action:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_module_action T fuel P Q nds states contexts Fs nd F ss source_context returned arity action"
    and supported: "lpp_stopped_action_supported action"
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
  case (LPPEEquationRewrite a b gs active saved e fs)
  have shape: "ss=(LPCGoals (LPCAtom a#gs),active)#saved"
    and rewrite: "lpp_check_equation_rewrite source_context a b"
    and link: "lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd
      ((LPCGoals (LPCAtom b#gs),active)#saved) (lpcn_ground nd) (lpcn_guards nd) [] F source_context e"
    using checked LPPEEquationRewrite by auto
  obtain v swaps where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+"
    and rep: "lpp_stable_rep operation SP nds states contexts Fs
      (lpc_return_scope_word swaps (lpc_return_eval eta ss)) v"
    using lpp_stable_equation_rewrite_link_sound[OF compatible transfer rewrite link known free observed]
    by (auto simp only: shape)
  show ?thesis by (rule lower[OF strict _ invariant])
    (use rep in \<open>auto simp: lpp_stable_module_rep_def\<close>)
next
  case (LPPEClauseEquationRewrite a b gs c m active saved e fs)
  have shape: "ss=(LPCClause (LPCAtom a#gs) c m,active)#saved"
    and rewrite: "lpp_check_equation_rewrite source_context a b"
    and link: "lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd
      ((LPCClause (LPCAtom b#gs) c m,active)#saved) (lpcn_ground nd) (lpcn_guards nd) [] F source_context e"
    using checked LPPEClauseEquationRewrite by auto
  obtain v swaps where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+"
    and rep: "lpp_stable_rep operation SP nds states contexts Fs
      (lpc_return_scope_word swaps (lpc_return_eval eta ss)) v"
    using lpp_stable_clause_equation_rewrite_link_sound[OF compatible transfer rewrite link known free observed]
    by (auto simp only: shape)
  show ?thesis by (rule lower[OF strict _ invariant])
    (use rep in \<open>auto simp: lpp_stable_module_rep_def\<close>)
next
  case (LPPEEvaluationError a e gs active saved)
  have check: "lpp_check_finite_evaluation_error nd F ss source_context a e gs active saved"
    using checked LPPEEvaluationError by simp
  show ?thesis by (rule lp_answer_stop_contract, rule lpp_stable_contract_from_finite, rule lpp_finite_evaluation_error_contract[OF check known free
    lpp_stable_context_finite_envelope[OF compatible observed]])
next
  case (LPPEComparisonError f comparison reversed a b gs active saved)
  have check: "lpp_check_finite_comparison_error nd F ss source_context f comparison reversed a b gs active saved"
    using checked LPPEComparisonError by simp
  show ?thesis by (rule lp_answer_stop_contract, rule lpp_stable_contract_from_finite, rule lpp_finite_comparison_error_contract[OF check known free
    lpp_stable_context_finite_envelope[OF compatible observed]])
next
  case (LPPEFiniteIs a e gs active saved result_var middle fs)
  have check: "lpp_check_finite_observed_is T fs fuel P Q nds states contexts Fs nd F ss source_context a e gs active saved result_var middle"
    using checked LPPEFiniteIs by simp
  have bounds: "lpcl_target middle<length nds \<and> lpcl_target middle<length states \<and>
    lpcl_target middle<length contexts \<and> lpcl_target middle<length Fs"
    using check by (auto simp: lpp_check_finite_observed_is_def lpp_check_evaluation_link_def lpc_check_return_table_link_def lpc_check_return_link_def lpc_check_link_def)
  show ?thesis
  proof (rule lpp_stopped_observed_is_contract[where J=J, OF compatible transfer check known free observed invariant frames])
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
next
  case (LPPEFiniteLength a e gs active saved result_var middle fs)
  then show ?thesis using supported by simp
next
  case (LPPESubtractLibrary e s a gs active saved middle fs)
  then show ?thesis using supported by simp
next
  case (LPPEConstantIs evidence a e gs active saved middle fs)
  have check: "lpp_check_finite_context_constant T fs fuel P Q nds states contexts Fs nd F ss source_context evidence a e gs active saved middle"
    using checked LPPEConstantIs by simp
  have bounds: "lpcl_target middle<length nds \<and> lpcl_target middle<length states \<and>
    lpcl_target middle<length contexts \<and> lpcl_target middle<length Fs"
    using check by (auto simp: lpp_check_finite_context_constant_def lpp_check_evaluation_link_def lpc_check_return_table_link_def lpc_check_return_link_def lpc_check_link_def)
  show ?thesis
  proof (rule lpp_stopped_context_constant_contract[where J=J, OF compatible transfer check known free observed invariant frames])
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
next
  case (LPPEPrimitive action)
  have check: "lpp_check_evaluation_primitive T fuel P Q nds states contexts Fs nd F ss source_context returned arity action"
    using checked LPPEPrimitive by simp
  show ?thesis
    by (rule lpp_stopped_primitive_contract[where J=J, OF compatible transfer check known free observed invariant])
      (fact stable, fact lower, fact emit)
next
  case (LPPETrim successor barriers e fs)
  have shape: "ss=successor@barriers" and barriers: "lp_cut_barriers (map fst barriers)"
    and link: "lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd successor (lpcn_ground nd) (lpcn_guards nd) [] F source_context e"
    using checked LPPETrim by auto
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  obtain v swaps where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+"
    and rep: "lpp_stable_rep operation SP nds states contexts Fs (lpc_return_scope_word swaps (lpc_return_eval eta successor)) v"
    using lpp_stable_link_sound[OF compatible transfer link equations refl known free observed] by blast
  have child: "lp_answer_contract (lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature)) (lpc_return_eval eta successor) R t ret"
    by (rule lower[OF strict _ subset[OF _ invariant]])
      (use rep in \<open>auto simp: lpp_stable_module_rep_def shape lpc_return_eval_def\<close>)
  have suffix: "lp_cut_barriers (map fst (lpc_return_eval eta barriers))"
    using barriers by (simp add: lpc_return_eval_erases lp_cut_state_map_def list_all_iff lp_cut_barrier_entry_map)
  show ?thesis using lpp_stopped_contract_append_barriers[OF child suffix]
    by (simp add: shape lpc_return_eval_def)
next
  case (LPPEParallel links factss)
  show ?thesis
  proof (rule lpp_stopped_contract_singletons)
    fix e assume member: "e\<in>set (lpc_return_eval eta ss)"
    obtain i where index: "i<length ss" and e: "[e]=lpc_return_eval eta [ss!i]"
      using member by (auto simp: lpc_return_eval_def in_set_conv_nth)
    have link: "lpp_check_evaluation_link T (factss!i) fuel Q nds states contexts Fs nd [ss!i] (lpcn_ground nd) (lpcn_guards nd) [] F source_context (links!i)"
      using checked LPPEParallel index by (auto simp: list_all_iff)
    have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
    obtain v swaps where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+"
      and rep: "lpp_stable_rep operation SP nds states contexts Fs (lpc_return_scope_word swaps (lpc_return_eval eta [ss!i])) v"
      using lpp_stable_link_sound[OF compatible transfer link equations refl known free observed] by blast
    show "lp_answer_contract (lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature)) [e] R t ret"
      unfolding e by (rule lower[OF strict _ subset[OF _ invariant]])
        (use rep member in \<open>auto simp: lpp_stable_module_rep_def e[symmetric]\<close>)
  qed
next
  case (LPPERefuted i k bindings)
  have "lp_cut_check_refuted_guard fuel (lpcn_guards nd) i k bindings"
    using checked LPPERefuted by simp
  then show ?thesis using lp_cut_checked_refuted_guard[OF _ known] by blast
qed
ML \<open>
val checked = [@{thm lpp_stopped_control_action}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stopped module action dependency" else ();
\<close>
end
