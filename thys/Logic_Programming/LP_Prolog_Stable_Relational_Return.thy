theory LP_Prolog_Stable_Relational_Return
 imports LP_Prolog_Finite_Relational_Return LP_Prolog_Stable_Return_Receipts
begin

lemma lpp_stable_inline_builtin_model:
  assumes checked: "lpp_inline_builtin_check F SP"
    and reachable: "f\<in>F"
    and outcome: "lpp_stable_source_builtin operation f ts (LPPBuiltinSuccess sigma)"
  shows "lpp_inline_return_model SP (lpp_stable_scalar_evaluation operation)
    (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
proof (cases "f=''2:is''")
  case True
  have length: "length ts=2" and success: "lpp_stable_is_outcome operation (ts!0) (ts!1) (LPPBuiltinSuccess sigma)"
    using outcome by (auto simp: lpp_stable_source_builtin_def lpp_finite_source_builtin_def True)
  have result: "(lpp_stable_scalar_evaluation operation) (ts!1) (lp_isubst (ts!0) sigma)"
    and fixed: "lp_isubst (ts!1) sigma=ts!1"
    using lpp_stable_is_success_evidence[OF success] by auto
  show ?thesis using result fixed by (simp add: True length)
next
  case no_is: False
  show ?thesis
  proof (cases "f=''1:integer''")
    case True
    have old: "lpp_integer_source_builtin ''1:integer'' ts (LPPBuiltinSuccess sigma)"
      using lpp_stable_source_refines_finite[OF outcome] by (simp add: lpp_finite_source_builtin_def True)
    show ?thesis using old
      by (auto simp: True lpp_integer_test_outcome_def split: if_splits)
  next
    case no_integer: False
    let ?us = "map (\<lambda>t. lp_isubst t sigma) ts"
    let ?eta = "\<lambda>v. ?us!(length v-1)"
    have selected: "(f,length ts)\<in>lpp_builtin_signature"
      by (rule lpp_finite_source_selected[OF lpp_stable_source_refines_finite[OF outcome]])
    obtain guards where clause: "((f,lpp_return_builtin_args (length ts)),[],guards)\<in>set SP"
      and holds: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) ?eta) guards"
    proof (cases "((f,lpp_return_builtin_args (length ts)),[],[])\<in>set SP")
      case True
      show ?thesis by (rule that[OF True]) simp
    next
      case False
      have name: "f=''2:length''" and arity: "length ts=2"
        and typed: "((f,lpp_return_builtin_args 2),[],[LPPSInteger (Var ''xx'')])\<in>set SP"
        using checked selected reachable no_is no_integer False
        by (auto simp: lpp_inline_builtin_check_def)
      have success: "lpp_finite_length_outcome (ts!0) (ts!1) (LPPBuiltinSuccess sigma)"
        using lpp_stable_source_refines_finite[OF outcome] by (simp add: lpp_finite_source_builtin_def name)
      have integer: "lpp_is_integer (lp_isubst (ts!1) sigma)"
        by (rule lpp_finite_length_success_integer[OF success])
      have guard: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) ?eta)
        [LPPSInteger (Var ''xx'')]" using integer arity by simp
      show ?thesis using that[of "[LPPSInteger (Var ''xx'')]"] typed arity guard by simp
    qed
    have success: "lpp_guarded_success SP (lpp_stable_scalar_evaluation operation)
      (lpp_success_atom_eval (f,lpp_return_builtin_args (length ts)) ?eta)"
      by (rule lpp_guarded_success.clause[OF clause holds]) simp
    have instantiated: "map (\<lambda>t. lp_ieval t ?eta) (lpp_return_builtin_args (length ts))=?us"
      using lpp_return_builtin_args_eval[of ?us] by simp
    have result: "lpp_guarded_success SP (lpp_stable_scalar_evaluation operation) (f,?us)"
      using success by (simp only: lpp_success_atom_eval_def fst_conv snd_conv instantiated)
    show ?thesis using result by (simp add: no_is no_integer)
  qed
qed

lemma lpp_stable_inline_no_probe:
  "lpp_inline_builtin_check F SP \<Longrightarrow> f\<in>F \<Longrightarrow>
    \<not>lpp_stable_source_builtin operation f ts (LPPBuiltinProbe a keep)"
  using lpp_inline_no_probe lpp_stable_source_refines_finite by blast

lemma lpp_stable_inline_no_call:
  "lpp_inline_builtin_check F SP \<Longrightarrow> f\<in>F \<Longrightarrow>
    \<not>lpp_stable_source_builtin operation f ts (LPPBuiltinCall a)"
  using lpp_inline_no_call lpp_stable_source_refines_finite by blast

lemma lpp_stable_inline_no_branch:
  "lpp_inline_builtin_check F SP \<Longrightarrow> f\<in>F \<Longrightarrow>
    \<not>lpp_stable_source_builtin operation f ts (LPPBuiltinBranch cs ys ns)"
  using lpp_inline_no_branch lpp_stable_source_refines_finite by blast

lemma lpp_stable_inline_no_choice:
  "lpp_inline_builtin_check F SP \<Longrightarrow> f\<in>F \<Longrightarrow>
    \<not>lpp_stable_source_builtin operation f ts (LPPBuiltinChoice left right)"
  using lpp_inline_no_choice lpp_stable_source_refines_finite by blast

theorem lpp_inline_stable_relational_return:
  fixes P :: "(string,string) lp_cut_program"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes program: "lpp_inline_return_program_check P F SP"
    and builtins: "lpp_inline_builtin_check F SP"
    and selected: "f\<in>F" and ordinary: "f\<noteq>''2:is''" "f\<noteq>''1:integer''"
    and actual: "lpp_stable_actual_return operation P
      [(LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) ts) eta)],eta)] rho"
  shows "lpp_guarded_success SP (lpp_stable_scalar_evaluation operation) (lpp_success_atom_eval (f,ts) rho)"
  by (rule lpp_inline_relational_actual_return[where E="lpp_stable_scalar_evaluation operation",
    OF program lpp_stable_inline_builtin_model[OF builtins] lpp_stable_inline_no_probe[OF builtins] lpp_stable_inline_no_call[OF builtins] lpp_stable_inline_no_branch[OF builtins] lpp_stable_inline_no_choice[OF builtins]
      lpp_stable_scalar_evaluation_subst selected ordinary actual])

lemma lpp_stable_add_success:
  "lpp_stable_context_holds operation SP incoming_context eta \<Longrightarrow>
   lpp_guarded_success SP (lpp_stable_scalar_evaluation operation) (lpp_success_atom_eval atom eta) \<Longrightarrow>
   lpp_stable_context_holds operation SP (lpp_context_add_success incoming_context atom) eta"
  by (cases incoming_context) (simp add: lpp_stable_context_holds_def lpp_evaluation_context_holds_def)

theorem lpp_stable_relational_return_context:
  fixes P :: "(string,string) lp_cut_program"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes program: "lpp_inline_return_program_check P F SP"
    and builtins: "lpp_inline_builtin_check F SP"
    and selected: "f\<in>F" and ordinary: "f\<noteq>''2:is''" "f\<noteq>''1:integer''"
    and observed: "lpp_stable_context_holds operation SP incoming_context eta"
    and actual: "lpp_stable_actual_return operation P
      [(LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) ts) eta)],eta)] rho"
  shows "lpp_stable_context_holds operation SP (lpp_context_add_success incoming_context (f,ts)) rho"
proof -
  have preserved: "lpp_stable_context_holds operation SP incoming_context rho"
    by (rule lpp_stable_actual_return_preserves_context[OF actual]) (use observed in simp)
  have returned: "lpp_guarded_success SP (lpp_stable_scalar_evaluation operation) (lpp_success_atom_eval (f,ts) rho)"
    by (rule lpp_inline_stable_relational_return[OF program builtins selected ordinary actual])
  show ?thesis by (rule lpp_stable_add_success[OF preserved returned])
qed


text \<open>The saved return frame and the helper execution use different
 environments. Recover the actual helper environment before adding its relation;
 the continuation interface retains responsibility for transporting that context.\<close>

lemma lpp_stable_relational_receipt_return:
  fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes program: "lpp_inline_return_program_check P F SP"
    and builtins: "lpp_inline_builtin_check F SP"
    and selected: "f\<in>F" and ordinary: "f\<noteq>''2:is''" "f\<noteq>''1:integer''"
    and pre: "pre=[LPCAtom (Fun (LPCUser f) ts)]"
    and known: "lp_cut_knowledge (set G) guards eta"
    and observed: "lpp_stable_context_holds operation SP incoming_context eta"
    and actual: "lpp_stable_actual_return operation P
      (lpc_return_eval eta [(LPCGoals pre,map Var vs)]) rho"
  shows "\<exists>theta. rho=lpc_return_env (map Var vs) theta \<and>
    lp_cut_knowledge (set G) [] theta \<and>
    lpp_stable_context_holds operation SP
      (lpp_context_add_success incoming_context (f,ts)) theta"
proof -
  obtain theta where source: "lpp_stable_actual_return operation P
      [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) (LPCGoals pre),eta)] theta"
    and rho: "rho=lpc_return_env (map Var vs) theta"
    using lpp_stable_seg_observed_actual[OF actual] by blast
  have returned_context: "lpp_stable_context_holds operation SP
      (lpp_context_add_success incoming_context (f,ts)) theta"
    by (rule lpp_stable_relational_return_context[OF program builtins selected ordinary observed])
      (use source in \<open>simp add: pre\<close>)
  have gr: "\<forall>x\<in>set G. lp_seg_ground (eta x)"
    using known by (simp add: lp_cut_knowledge_def)
  have captured: "theta x=eta x" if x: "x\<in>set G" for x
    using lpp_stable_seg_captured_term[OF source, of "Var x"] gr x by simp
  have ground: "lp_cut_knowledge (set G) [] theta"
    using gr captured by (auto simp: lp_cut_knowledge_def)
  show ?thesis using rho ground returned_context by blast
qed

ML \<open>
val checked = [@{thm lpp_stable_inline_builtin_model}, @{thm lpp_inline_stable_relational_return},
  @{thm lpp_stable_relational_return_context}, @{thm lpp_stable_relational_receipt_return}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable relational return dependency" else ();
\<close>
end
