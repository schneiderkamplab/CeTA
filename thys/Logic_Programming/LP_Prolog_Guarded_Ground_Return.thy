theory LP_Prolog_Guarded_Ground_Return
  imports LP_Prolog_Inline_Ground_Return
begin

text \<open>Successful evaluation guards establish finite groundness without
establishing integer typing. The existing ground-mode flow checks every body
and every clause; induction is on actual finite successful derivations.\<close>

fun lpp_guard_ground_vars where
  "lpp_guard_ground_vars (LPPSInteger t) = vars_term t"
| "lpp_guard_ground_vars (LPPSEvaluates e t) = vars_term e \<union> vars_term t"
| "lpp_guard_ground_vars (LPPSOpaque t) = {}"

definition lpp_guards_ground where
  "lpp_guards_ground gs = Union (set (map lpp_guard_ground_vars gs))"

lemma lpp_guards_ground_sound:
  assumes guards: "list_all (lpp_success_guard_holds E eta) gs"
    and evaluation: "\<And>e t. E e t \<Longrightarrow> lp_seg_ground e \<and> lp_seg_ground t"
  shows "\<forall>x\<in>lpp_guards_ground gs. lp_seg_ground (eta x)"
proof -
  have "\<forall>x\<in>lpp_guard_ground_vars g. lp_seg_ground (eta x)" if "g\<in>set gs" for g
  proof -
    have holds: "lpp_success_guard_holds E eta g"
      using guards that by (simp add: list_all_iff)
    show ?thesis using holds
      by (cases g) (auto simp: lp_seg_ground_eval dest: evaluation lpp_integer_ground_vars)
  qed
  then show ?thesis by (auto simp: lpp_guards_ground_def)
qed

definition lpp_guarded_ground_check where
  "lpp_guarded_ground_check P modes =
    (list_all lp_ground_valid_mode modes \<and>
     list_all (\<lambda>m. list_all (\<lambda>(h,bs,gs).
       \<not>lp_ground_matches m (lpp_lift_atom h) \<or>
       lp_ground_vars (lpp_lift_atom h) (lp_ground_outputs m) \<subseteq>
       lp_ground_flow modes (map lpp_lift_atom bs)
         (lp_ground_vars (lpp_lift_atom h) (lp_ground_inputs m) \<union> lpp_guards_ground gs)) P) modes)"

lemma lpp_guarded_ground_check_model:
  assumes checked: "lpp_guarded_ground_check P modes"
    and evaluation: "\<And>e t. E e t \<Longrightarrow> lp_seg_ground e \<and> lp_seg_ground t"
    and success: "lpp_guarded_success P E a"
  shows "\<forall>m\<in>set modes. lp_ground_contract m (lpp_lift_iatom a)"
  using success
proof (induct rule: lpp_guarded_success.induct)
  case (clause h bs gs eta)
  have valid: "list_all lp_ground_valid_mode modes"
    using checked by (simp add: lpp_guarded_ground_check_def)
  have observed: "\<forall>x\<in>lpp_guards_ground gs. lp_seg_ground (eta x)"
    by (rule lpp_guards_ground_sound[OF clause.hyps(2) evaluation])
  have lift: "lpp_lift_iatom (lpp_success_atom_eval b eta)=lp_atom_eval (lpp_lift_atom b) eta" for b
    by (cases b) (simp add: lpp_lift_iatom_def lpp_success_atom_eval_def lpp_lift_atom_def lp_atom_eval_def)
  show ?case unfolding lift
  proof (intro ballI, unfold lp_ground_contract_def, intro impI)
    fix m assume m: "m\<in>set modes"
      and match: "lp_ground_matches m (lp_atom_eval (lpp_lift_atom h) eta)"
      and inputs: "lp_ground_positions (lp_atom_eval (lpp_lift_atom h) eta) (lp_ground_inputs m)"
    have bounds: "\<forall>i\<in>set (lp_ground_inputs m). i<length (snd (lpp_lift_atom h))"
      "\<forall>i\<in>set (lp_ground_outputs m). i<length (snd (lpp_lift_atom h))"
      using valid m match by (cases m; auto simp: list_all_iff lp_atom_eval_def)+
    have known: "\<forall>x\<in>lp_ground_vars (lpp_lift_atom h) (lp_ground_inputs m) \<union> lpp_guards_ground gs.
      lp_seg_ground (eta x)"
      using observed inputs by (auto simp: lp_ground_positions_eval[OF bounds(1)])
    have body: "\<forall>b\<in>set (map lpp_lift_atom bs). \<forall>m\<in>set modes. lp_ground_contract m (lp_atom_eval b eta)"
      using clause.hyps by (auto simp: list_all_iff lift)
    have flow: "\<forall>x\<in>lp_ground_flow modes (map lpp_lift_atom bs)
        (lp_ground_vars (lpp_lift_atom h) (lp_ground_inputs m) \<union> lpp_guards_ground gs).
      lp_seg_ground (eta x)"
      by (rule lp_ground_flow_sound[OF valid body known])
    have allowed: "lp_ground_vars (lpp_lift_atom h) (lp_ground_outputs m) \<subseteq>
      lp_ground_flow modes (map lpp_lift_atom bs)
        (lp_ground_vars (lpp_lift_atom h) (lp_ground_inputs m) \<union> lpp_guards_ground gs)"
      using checked m clause.hyps(1) match
      by (force simp: lpp_guarded_ground_check_def list_all_iff)
    show "lp_ground_positions (lp_atom_eval (lpp_lift_atom h) eta) (lp_ground_outputs m)"
      using flow allowed by (auto simp: lp_ground_positions_eval[OF bounds(2)])
  qed
qed

theorem lpp_inline_guarded_ground_return:
  fixes P :: "(string,string) lp_cut_program"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes program: "lpp_inline_return_program_check P F SP"
    and builtins: "lpp_inline_builtin_check F SP"
    and selected: "f\<in>F" and ordinary: "f\<noteq>''2:is''" "f\<noteq>''1:integer''"
    and modes: "lpp_guarded_ground_check SP contracts"
    and known: "\<forall>x\<in>G. lp_seg_ground (eta x)"
    and actual: "lp_actual_answer (lpp_domain_answers P lpp_builtin_signature
      lpp_finite_source_builtin lpp_finite_source_domain)
      [(LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) ts) eta)],eta)] rho"
  shows "\<forall>x\<in>lp_ground_flow contracts [(LPCUser f,ts)] G. lp_seg_ground (rho x)"
proof -
  let ?M = "lpp_inline_return_model SP lpp_finite_evaluation_result :: (string lp_cut_symbol,string) lp_iterm \<Rightarrow> bool"
  let ?gs = "[LPCAtom (lp_ieval (Fun (LPCUser f) ts) eta)]"
  let ?H = "lp_ground_flow contracts [(LPCUser f,ts)] G"
  let ?property = "\<lambda>nu. \<forall>x\<in>?H. lp_seg_ground (nu x)"
  have modeled: "lpc_scoped_model_program P F ?M"
    by (rule lpp_inline_return_program_sound[OF program])
  have initial: "lpc_model_goals ?M ?property ?gs eta"
  proof (unfold lpc_model_goals_def, intro conjI allI impI)
    show "list_all lpc_model_safe_goal ?gs" by simp
  next
    fix sigma assume model: "list_all (lpc_model_goal ?M)
      (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ?gs)"
    let ?nu = "\<lambda>x. lp_isubst (eta x) sigma"
    have success: "lpp_guarded_success SP lpp_finite_evaluation_result
      (lpp_success_atom_eval (f,ts) ?nu)"
      using model by (simp add: ordinary lpp_success_atom_eval_def lp_ieval_subst map_map o_def)
    have valid: "list_all lp_ground_valid_mode contracts"
      using modes by (simp add: lpp_guarded_ground_check_def)
    have contracts: "\<forall>a\<in>set [(LPCUser f,ts)]. \<forall>m\<in>set contracts.
      lp_ground_contract m (lp_atom_eval a ?nu)"
      using lpp_guarded_ground_check_model[OF modes lpp_finite_evaluation_ground success]
      by (simp add: lpp_lift_iatom_def lpp_success_atom_eval_def lp_atom_eval_def)
    have preserved: "\<forall>x\<in>G. lp_seg_ground (?nu x)"
      using known by (simp add: lp_seg_ground_subst)
    show "?property ?nu" by (rule lp_ground_flow_sound[OF valid contracts preserved])
  qed
  have frames: "list_all (lpc_scoped_model_frame F ?M ?property) [(LPCGoals ?gs,eta)]"
    using selected initial by simp
  show ?thesis by (rule lpp_scoped_model_actual_return[OF modeled
    lpp_inline_builtin_model[OF builtins] lpp_inline_return_model_subst[where E=lpp_finite_evaluation_result, OF lpp_finite_evaluation_subst] frames actual])
qed

ML \<open>
val checked = [@{thm lpp_guarded_ground_check_model}, @{thm lpp_inline_guarded_ground_return}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted guarded ground-return dependency" else ();
\<close>
end
