theory LP_Prolog_Stopped_Primitive
  imports LP_Prolog_Stopped_Answers LP_Prolog_Stable_Module_Action
begin

text \<open>Reuse the established action checker and its context transport.
All child and invariant assumptions refer to the stopped relation; no child
contract is unsoundly lifted back to ordinary backtracking semantics.\<close>

theorem lpp_stopped_primitive_contract:
  fixes SP :: "string lpp_success_clause list" and P and operation
  defines "A \<equiv> lp_answer_stop
    (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
    (lpp_undefined_answer_stop P lpp_builtin_signature)"
  assumes compatible: "lpp_stable_integer_operations operation"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_primitive T fuel P Q nds states contexts Fs nd F ss source_context returned arity action"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and invariant: "J (lpc_return_eval eta ss)"
    and stable: "\<And>xs ev ys. A xs ev ys \<Longrightarrow> J xs \<Longrightarrow> J ys"
    and lower: "\<And>vs v. ([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      lpp_stable_module_rep operation SP nds states contexts Fs vs v \<Longrightarrow> J vs \<Longrightarrow>
      lp_answer_contract A vs R t ret"
    and emit: "\<And>rho tt. A (lpc_return_eval eta ss) (Some rho) tt \<Longrightarrow> (t,ret rho)\<in>R\<^sup>*"
  shows "lp_answer_contract A (lpc_return_eval eta ss) R t ret"
proof (cases "lpp_undefined_answer_stop P lpp_builtin_signature (lpc_return_eval eta ss)")
  case True
  show ?thesis unfolding A_def by (rule lp_answer_stop_error_contract) (rule True)
next
  case False
  show ?thesis
  proof (rule lp_answer_contract_intro)
    fix event tt assume step: "A (lpc_return_eval eta ss) event tt"
    have original: "lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation)
      lpp_finite_source_domain (lpc_return_eval eta ss) event tt"
      using step False by (simp add: A_def lp_answer_stop_def)
    have supported: "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_finite_source_domain
      (map fst (lpc_return_eval eta ss))"
      by (rule lpp_stable_primitive_domain[OF compatible transfer checked known observed])
    have actual: "lpp_answer_transition P lpp_builtin_signature (lpp_stable_source_builtin operation)
      (lpc_return_eval eta ss) event tt"
      using original supported by (simp add: lpp_domain_answers_def)
    obtain u swaps where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+"
      and rep: "lpp_stable_rep operation SP nds states contexts Fs (lpc_return_scope_word swaps tt) u"
      using lpp_stable_primitive_sound[OF compatible transfer checked known free observed actual] by blast
    have child: "lp_answer_contract A tt R t ret"
      by (rule lower[OF strict _ stable[OF step invariant]])
        (use rep in \<open>auto simp: lpp_stable_module_rep_def\<close>)
    show "(\<forall>rho. event=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*) \<and> lp_answer_contract A tt R t ret"
      using child step emit by blast
  qed
qed

ML \<open>
val audited = [@{thm lpp_stopped_primitive_contract}];
val names = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = names [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof audited orelse
  exists (fn n => not (member (op =) inherited n)) (names audited)
  then error "Untrusted stopped action dependency" else ();
\<close>
end
