theory LP_Prolog_Finite_Direct_Action
 imports LP_Prolog_Finite_Direct_Observed_Is LP_Prolog_Stable_Module_Action
   LP_Prolog_Finite_Direct_Comparison
begin

fun lpp_check_finite_direct_action where
 "lpp_check_finite_direct_action T fuel P Q nds states contexts Fs nd F ss source_context returned arity
   (LPPEFiniteIs a e gs active saved result_var middle fs) =
    lpp_check_observed_evaluation_link T fs fuel P Q nds states contexts Fs nd F ss source_context a e gs active saved result_var middle"
| "lpp_check_finite_direct_action T fuel P Q nds states contexts Fs nd F ss source_context returned arity
   (LPPEEvaluationError a e gs active saved) =
    (ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved \<and>
     (case e of Fun f ts \<Rightarrow> 2<length ts | _ \<Rightarrow> False))"
| "lpp_check_finite_direct_action T fuel P Q nds states contexts Fs nd F ss source_context returned arity
   (LPPEFiniteLength a e gs active saved result_var middle fs) = False"
| "lpp_check_finite_direct_action T fuel P Q nds states contexts Fs nd F ss source_context returned arity
   (LPPESubtractLibrary e s a gs active saved middle fs) = False"
| "lpp_check_finite_direct_action T fuel P Q nds states contexts Fs nd F ss source_context returned arity
   (LPPEConstantIs evidence a e gs active saved middle fs) = False"
| "lpp_check_finite_direct_action T fuel P Q nds states contexts Fs nd F ss source_context returned arity
   (LPPEPrimitive prim) =
    lpp_check_finite_direct_primitive T fuel P Q nds states contexts Fs nd F ss source_context returned arity prim"
| "lpp_check_finite_direct_action T fuel P Q nds states contexts Fs nd F ss source_context returned arity action =
    lpp_check_evaluation_module_action T fuel P Q nds states contexts Fs nd F ss source_context returned arity action"

theorem lpp_finite_direct_control_action_invariant:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_finite_direct_action T fuel P Q nds states contexts Fs nd F ss source_context returned arity action"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and invariant: "lpp_finite_direct_invariant A (lpc_return_eval eta ss)"
    and extra: "K (lpc_return_eval eta ss)"
    and frames: "\<And>xs ys. map snd xs=map snd ys \<Longrightarrow> K ys \<Longrightarrow> K xs"
    and extra_stable: "\<And>ev ys. lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain (lpc_return_eval eta ss) ev ys \<Longrightarrow> K ys"
    and extra_subset: "\<And>xs ys. set xs\<subseteq> set ys \<Longrightarrow> K ys \<Longrightarrow> K xs"
    and stable: "\<And>ev ys. lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain (lpc_return_eval eta ss) ev ys \<Longrightarrow> lpp_finite_direct_invariant A ys"
    and subset: "\<And>(xs::((string lp_cut_symbol,string) lp_iterm lp_cut_entry \<times> (nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm)) list) ys. set xs\<subseteq> set ys \<Longrightarrow> lpp_finite_direct_invariant A ys \<Longrightarrow> lpp_finite_direct_invariant A xs"
    and lower: "\<And>vs v. ([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      lpp_stable_module_rep operation SP nds states contexts Fs vs v \<Longrightarrow> lpp_finite_direct_invariant A vs \<Longrightarrow> K vs \<Longrightarrow> lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) vs R t ret"
    and emit: "\<And>rho tt. lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain (lpc_return_eval eta ss) (Some rho) tt \<Longrightarrow> (t,ret rho)\<in>R\<^sup>*"
  shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpc_return_eval eta ss) R t ret"
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
  show ?thesis by (rule lower[OF strict _ invariant extra])
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
  show ?thesis by (rule lower[OF strict _ invariant extra])
    (use rep in \<open>auto simp: lpp_stable_module_rep_def\<close>)
next
  case (LPPEEvaluationError a e gs active saved)
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved"
    and arity: "case e of Fun f ts \<Rightarrow> 2<length ts | _ \<Rightarrow> False"
    using checked LPPEEvaluationError by auto
  obtain f ts where expr: "e=Fun f ts" and large: "2<length ts"
    using arity by (cases e) auto
  have finite: "lpp_finite_term (lp_ieval e eta)"
    using invariant by (auto simp: shape lpc_return_eval_def
      lpp_finite_direct_invariant_def lpp_finite_direct_state_def)
  show ?thesis using lpp_finite_large_arity_error_contract[OF finite[unfolded expr lp_ieval.simps]] large
    by (simp add: shape expr lpc_return_eval_def)

next
  case (LPPEComparisonError f comparison reversed a b gs active saved)
  have check: "lpp_check_finite_comparison_error nd F ss source_context f comparison reversed a b gs active saved"
    using checked LPPEComparisonError by simp
  show ?thesis by (rule lpp_stable_contract_from_finite, rule lpp_finite_comparison_error_contract[OF check known free
    lpp_stable_context_finite_envelope[OF compatible observed]])
next
  case (LPPEFiniteIs a e gs active saved result_var middle fs)
  have check: "lpp_check_observed_evaluation_link T fs fuel P Q nds states contexts Fs nd F ss source_context a e gs active saved result_var middle"
    using checked LPPEFiniteIs by simp
  have bounds: "lpcl_target middle<length nds \<and> lpcl_target middle<length states \<and>
    lpcl_target middle<length contexts \<and> lpcl_target middle<length Fs"
    using check by (auto simp: lpp_check_observed_evaluation_link_def lpp_check_evaluation_link_def lpc_check_return_table_link_def lpc_check_return_link_def lpc_check_link_def)
  show ?thesis
  proof (rule lpp_finite_direct_observed_is_invariant_contract[where K=K, OF compatible transfer check known free observed invariant extra frames])
    fix rho
    assume edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],
      [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>(lp_ild Q)\<^sup>+"
      and knowledge: "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho"
      and child_free: "lpc_free_knowledge (set (Fs!lpcl_target middle)) rho"
      and child_context: "lpp_stable_context_holds operation SP (contexts!lpcl_target middle) rho"
      and inv: "lpp_finite_direct_invariant A (lpc_return_eval rho (states!lpcl_target middle))"
      and child_extra: "K (lpc_return_eval rho (states!lpcl_target middle))"
    have represented: "lpp_stable_module_rep operation SP nds states contexts Fs
      (lpc_return_eval rho (states!lpcl_target middle))
      [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))]"
      unfolding lpp_stable_module_rep_def lpp_stable_rep_def
      by (rule exI[of _ "[]"], rule exI[of _ "lpcl_target middle"], rule exI[of _ rho])
        (use bounds knowledge child_free child_context in auto)
    show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
      (lpc_return_eval rho (states!lpcl_target middle)) R t ret"
      by (rule lower[OF edge represented inv child_extra])
  qed
next
  case (LPPEFiniteLength a e gs active saved result_var middle fs)
  then show ?thesis using checked by simp
next
  case (LPPESubtractLibrary e s a gs active saved middle fs)
  then show ?thesis using checked by simp
next
  case (LPPEConstantIs evidence a e gs active saved middle fs)
  then show ?thesis using checked by simp
next
  case (LPPEPrimitive primitive)
  have check: "lpp_check_finite_direct_primitive T fuel P Q nds states contexts Fs nd F ss source_context returned arity primitive"
    using checked LPPEPrimitive by simp
  show ?thesis
  proof (rule lp_answer_contract_intro)
    fix event tt
    assume step: "lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain (lpc_return_eval eta ss) event tt"
    have supported: "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_finite_source_domain (map fst (lpc_return_eval eta ss))"
      by (rule lpp_finite_direct_primitive_domain[OF compatible transfer check known observed invariant])
    have actual: "lpp_answer_transition P lpp_builtin_signature (lpp_stable_source_builtin operation) (lpc_return_eval eta ss) event tt"
      using step supported by (simp add: lpp_domain_answers_def)
    obtain u swaps where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+"
      and rep: "lpp_stable_rep operation SP nds states contexts Fs (lpc_return_scope_word swaps tt) u"
      using lpp_finite_direct_primitive_sound[OF compatible transfer check known free observed actual] by blast
    have child: "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) tt R t ret"
      by (rule lower[OF strict _ stable[OF step] extra_stable[OF step]])
        (use rep in \<open>auto simp: lpp_stable_module_rep_def\<close>)
    show "(\<forall>rho. event=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*) \<and>
      lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) tt R t ret"
      using child step emit by blast
  qed
next
  case (LPPETrim successor barriers e fs)
  have shape: "ss=successor@barriers" and barriers: "lp_cut_barriers (map fst barriers)"
    and link: "lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd successor (lpcn_ground nd) (lpcn_guards nd) [] F source_context e"
    using checked LPPETrim by auto
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  obtain v swaps where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+"
    and rep: "lpp_stable_rep operation SP nds states contexts Fs (lpc_return_scope_word swaps (lpc_return_eval eta successor)) v"
    using lpp_stable_link_sound[OF compatible transfer link equations refl known free observed] by blast
  have child: "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpc_return_eval eta successor) R t ret"
    by (rule lower[OF strict _ subset[OF _ invariant] extra_subset[OF _ extra]])
      (use rep in \<open>auto simp: lpp_stable_module_rep_def shape lpc_return_eval_def\<close>)
  have suffix: "lp_cut_barriers (map fst (lpc_return_eval eta barriers))"
    using barriers by (simp add: lpc_return_eval_erases lp_cut_state_map_def list_all_iff lp_cut_barrier_entry_map)
  show ?thesis using lpp_domain_contract_append_barriers[OF child suffix]
    by (simp add: shape lpc_return_eval_def)
next
  case (LPPEParallel links factss)
  show ?thesis
  proof (rule lpp_domain_contract_singletons)
    fix e assume member: "e\<in>set (lpc_return_eval eta ss)"
    obtain i where index: "i<length ss" and e: "[e]=lpc_return_eval eta [ss!i]"
      using member by (auto simp: lpc_return_eval_def in_set_conv_nth)
    have link: "lpp_check_evaluation_link T (factss!i) fuel Q nds states contexts Fs nd [ss!i] (lpcn_ground nd) (lpcn_guards nd) [] F source_context (links!i)"
      using checked LPPEParallel index by (auto simp: list_all_iff)
    have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
    obtain v swaps where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+"
      and rep: "lpp_stable_rep operation SP nds states contexts Fs (lpc_return_scope_word swaps (lpc_return_eval eta [ss!i])) v"
      using lpp_stable_link_sound[OF compatible transfer link equations refl known free observed] by blast
    show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) [e] R t ret"
      unfolding e by (rule lower[OF strict _ subset[OF _ invariant] extra_subset[OF _ extra]])
        (use rep member in \<open>auto simp: lpp_stable_module_rep_def e[symmetric]\<close>)
  qed
next
  case (LPPERefuted i k bindings)
  have "lp_cut_check_refuted_guard fuel (lpcn_guards nd) i k bindings"
    using checked LPPERefuted by simp
  then show ?thesis using lp_cut_checked_refuted_guard[OF _ known] by blast
qed

theorem lpp_finite_direct_control_action_local:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_finite_direct_action T fuel P Q nds states contexts Fs nd F ss source_context returned arity action"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and invariant: "lpp_finite_direct_invariant A (lpc_return_eval eta ss)"
    and stable: "\<And>ev ys. lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain (lpc_return_eval eta ss) ev ys \<Longrightarrow> lpp_finite_direct_invariant A ys"
    and subset: "\<And>(xs::((string lp_cut_symbol,string) lp_iterm lp_cut_entry \<times> (nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm)) list) ys. set xs\<subseteq> set ys \<Longrightarrow> lpp_finite_direct_invariant A ys \<Longrightarrow> lpp_finite_direct_invariant A xs"
    and lower: "\<And>vs v. ([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      lpp_stable_module_rep operation SP nds states contexts Fs vs v \<Longrightarrow> lpp_finite_direct_invariant A vs \<Longrightarrow> lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) vs R t ret"
    and emit: "\<And>rho tt. lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain (lpc_return_eval eta ss) (Some rho) tt \<Longrightarrow> (t,ret rho)\<in>R\<^sup>*"
  shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpc_return_eval eta ss) R t ret"
 by (rule lpp_finite_direct_control_action_invariant[where K="\<lambda>_. True",
       OF compatible transfer checked known free observed invariant])
    (use stable subset lower emit in auto)

theorem lpp_finite_direct_control_action:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_finite_direct_action T fuel P Q nds states contexts Fs nd F ss source_context returned arity action"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and invariant: "lpp_finite_direct_invariant A (lpc_return_eval eta ss)"
    and stable: "\<And>(xs::((string lp_cut_symbol,string) lp_iterm lp_cut_entry \<times> (nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm)) list) ev ys. lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain xs ev ys \<Longrightarrow> lpp_finite_direct_invariant A xs \<Longrightarrow> lpp_finite_direct_invariant A ys"
    and subset: "\<And>(xs::((string lp_cut_symbol,string) lp_iterm lp_cut_entry \<times> (nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm)) list) ys. set xs\<subseteq> set ys \<Longrightarrow> lpp_finite_direct_invariant A ys \<Longrightarrow> lpp_finite_direct_invariant A xs"
    and lower: "\<And>vs v. ([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      lpp_stable_module_rep operation SP nds states contexts Fs vs v \<Longrightarrow> lpp_finite_direct_invariant A vs \<Longrightarrow> lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) vs R t ret"
    and emit: "\<And>rho tt. lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain (lpc_return_eval eta ss) (Some rho) tt \<Longrightarrow> (t,ret rho)\<in>R\<^sup>*"
  shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpc_return_eval eta ss) R t ret"
 by (rule lpp_finite_direct_control_action_local[OF compatible transfer checked known free observed invariant _ subset lower emit])
   (rule stable[OF _ invariant], assumption)

ML \<open>
val checked = [@{thm lpp_finite_direct_control_action_invariant},
 @{thm lpp_finite_direct_control_action},
 @{thm lpp_finite_direct_control_action_local}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite direct action" else ();
\<close>
end
