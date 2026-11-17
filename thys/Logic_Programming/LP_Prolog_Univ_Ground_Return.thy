theory LP_Prolog_Univ_Ground_Return
 imports LP_Prolog_Univ_Source LP_Prolog_Guarded_Ground_Return
begin

lemma lpp_inline_univ_builtin_model:
 assumes checked: "lpp_inline_builtin_check F SP"
 and reachable: "f\<in>F"
 and outcome: "lpp_univ_source_builtin names operation f ts (LPPBuiltinSuccess sigma)"
 shows "lpp_inline_return_model SP lpp_finite_evaluation_result
   (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
proof (cases "f=''2:=..''")
 case False
 have old: "lpp_finite_source_builtin f ts (LPPBuiltinSuccess sigma)"
  using outcome False by (auto simp: lpp_univ_source_builtin_def dest: lpp_stable_source_refines_finite)
 show ?thesis by (rule lpp_inline_builtin_model[OF checked reachable old])
next
 case True
 have arity: "length ts=2" using outcome True by (simp add: lpp_univ_source_builtin_def)
 have selected: "(f,2)\<in>lpp_builtin_signature"
  using lpp_univ_source_selected[OF outcome] arity by simp
 have clause: "((f,lpp_return_builtin_args 2),[],[])\<in>set SP"
  using checked reachable selected True by (auto simp: lpp_inline_builtin_check_def)
 let ?us = "map (\<lambda>t. lp_isubst t sigma) ts"
 let ?eta = "\<lambda>v. ?us!(length v-1)"
 have success: "lpp_guarded_success SP lpp_finite_evaluation_result
    (lpp_success_atom_eval (f,lpp_return_builtin_args 2) ?eta)"
  by (rule lpp_guarded_success.clause[OF clause]) simp_all
 have instantiated: "map (\<lambda>t. lp_ieval t ?eta) (lpp_return_builtin_args 2)=?us"
  using lpp_return_builtin_args_eval[of ?us] arity by simp
 have result: "lpp_guarded_success SP lpp_finite_evaluation_result (f,?us)"
  using success by (simp only: lpp_success_atom_eval_def fst_conv snd_conv instantiated)
 show ?thesis using result True by simp
qed

lemma lpp_univ_view_no_control:
 "\<not>lpp_univ_view_outcome names input_value requested (LPPBuiltinProbe a keep)"
 "\<not>lpp_univ_view_outcome names input_value requested (LPPBuiltinCall a)"
 "\<not>lpp_univ_view_outcome names input_value requested (LPPBuiltinBranch cs ys ns)"
 "\<not>lpp_univ_view_outcome names input_value requested (LPPBuiltinChoice left right)"
 by (cases input_value; simp add: lpp_univ_decompose_outcome_def)+

lemma lpp_inline_univ_no_probe:
 assumes checked: "lpp_inline_builtin_check F SP" and member: "f\<in>F"
 shows "\<not>lpp_univ_source_builtin names operation f ts (LPPBuiltinProbe a keep)"
 using lpp_inline_no_probe[OF checked member] lpp_univ_view_no_control(1)
 by (auto simp: lpp_univ_source_builtin_def dest: lpp_stable_source_refines_finite)

lemma lpp_inline_univ_no_call:
 assumes checked: "lpp_inline_builtin_check F SP" and member: "f\<in>F"
 shows "\<not>lpp_univ_source_builtin names operation f ts (LPPBuiltinCall a)"
 using lpp_inline_no_call[OF checked member] lpp_univ_view_no_control(2)
 by (auto simp: lpp_univ_source_builtin_def dest: lpp_stable_source_refines_finite)

lemma lpp_inline_univ_no_branch:
 assumes checked: "lpp_inline_builtin_check F SP" and member: "f\<in>F"
 shows "\<not>lpp_univ_source_builtin names operation f ts (LPPBuiltinBranch cs ys ns)"
 using lpp_inline_no_branch[OF checked member] lpp_univ_view_no_control(3)
 by (auto simp: lpp_univ_source_builtin_def dest: lpp_stable_source_refines_finite)

lemma lpp_inline_univ_no_choice:
 assumes checked: "lpp_inline_builtin_check F SP" and member: "f\<in>F"
 shows "\<not>lpp_univ_source_builtin names operation f ts (LPPBuiltinChoice left right)"
 using lpp_inline_no_choice[OF checked member] lpp_univ_view_no_control(4)
 by (auto simp: lpp_univ_source_builtin_def dest: lpp_stable_source_refines_finite)

theorem lpp_inline_univ_guarded_ground_return:
  fixes P :: "(string,string) lp_cut_program"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes program: "lpp_inline_return_program_check P F SP"
    and builtins: "lpp_inline_builtin_check F SP"
    and selected: "f\<in>F" and ordinary: "f\<noteq>''2:is''" "f\<noteq>''1:integer''"
    and modes: "lpp_guarded_ground_check SP contracts"
    and known: "\<forall>x\<in>G. lp_seg_ground (eta x)"
    and actual: "lp_actual_answer (lpp_domain_answers P lpp_builtin_signature
      (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
      [(LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) ts) eta)],eta)] rho"
  shows "\<forall>x\<in>lp_ground_flow contracts [(LPCUser f,ts)] G. lp_seg_ground (rho x)"
 by (rule lpp_inline_guarded_ground_return_parameterized[OF program
   lpp_inline_univ_builtin_model[OF builtins] lpp_inline_univ_no_probe[OF builtins]
   lpp_inline_univ_no_call[OF builtins] lpp_inline_univ_no_branch[OF builtins]
   lpp_inline_univ_no_choice[OF builtins] lpp_finite_evaluation_subst
   lpp_finite_evaluation_ground selected ordinary modes known actual])

lemma lpp_inline_univ_missing_clause_rejected:
 assumes reachable: "''2:=..''\<in>F"
 and absent: "((''2:=..'',lpp_return_builtin_args 2),[],[])\<notin>set SP"
 shows "\<not>lpp_inline_builtin_check F SP"
proof -
 have selected: "(''2:=..'',2)\<in>lpp_builtin_signature"
  by (simp add: lpp_builtin_signature_def)
 show ?thesis using selected reachable absent
  by (auto simp: lpp_inline_builtin_check_def)
qed

ML \<open>
val checked = @{thms lpp_inline_univ_guarded_ground_return lpp_inline_univ_missing_clause_rejected};
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
 exists (fn n => not (member (op =) inherited n)) (oracles checked)
 then error "Untrusted univ ground return" else ();
\<close>
end
