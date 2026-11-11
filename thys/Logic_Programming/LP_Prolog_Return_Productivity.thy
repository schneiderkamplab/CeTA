theory LP_Prolog_Return_Productivity
  imports LP_Return_Productivity LP_Prolog_Control_Shape_Return
begin

lemma lpp_guarded_nonproductive_return:
  assumes checked: "lp_return_nonproductive_check (lpp_shape_program P) blocked"
    and success: "lpp_guarded_success P E a"
  shows "lp_return_signature (lpp_lift_iatom a)\<notin>set blocked"
  by (rule lp_return_nonproductive_sound[OF checked
    lpp_guarded_success_shape_model[OF success]])

lemma lpp_guarded_productive_shape_contracts:
  fixes P :: "'v lpp_success_clause list"
    and a :: "string \<times> (string lp_cut_symbol,'v) lp_iterm list"
  assumes checked: "lp_return_nonproductive_check (lpp_shape_program P) blocked"
    and shapes: "lp_return_shape_program_check fuel G modes
      (lp_return_productive_program (lpp_shape_program P) blocked)"
    and success: "lpp_guarded_success P E a"
  shows "lp_return_contracts G modes (lpp_lift_iatom a)"
  using lp_return_productive_shapes[OF checked lp_return_shape_program_check_sound[OF shapes]]
    lpp_guarded_success_shape_model[OF success]
  by (cases "lpp_lift_iatom a") (auto simp: lp_return_shape_model_def)

theorem lpp_control_stable_productive_shapes:
  fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes program: "lpp_control_return_program_check fuel P F SP"
    and builtins: "lpp_open_builtin_check F SP"
    and selected: "f\<in>F"
    and ordinary: "f\<noteq>''2:is''" "f\<noteq>''1:integer''" "f\<noteq>''2:;''" "f\<noteq>''3:subtract''"
    and checked: "lp_return_nonproductive_check (lpp_shape_program SP) blocked"
    and shapes: "lp_return_shape_program_check shape_fuel G modes
      (lp_return_productive_program (lpp_shape_program SP) blocked)"
    and actual: "lpp_stable_actual_return operation P
      [(LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) ts) eta)],eta)] rho"
  shows "lp_return_contracts G modes (lpp_lift_iatom (lpp_success_atom_eval (f,ts) rho))"
  by (rule lpp_guarded_productive_shape_contracts[OF checked shapes
    lpp_control_stable_relational_return[OF program builtins selected ordinary actual]])

theorem lpp_control_nonproductive_no_actual_return:
  fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes program: "lpp_control_return_program_check fuel P F SP"
    and builtins: "lpp_open_builtin_check F SP"
    and selected: "f\<in>F"
    and ordinary: "f\<noteq>''2:is''" "f\<noteq>''1:integer''" "f\<noteq>''2:;''" "f\<noteq>''3:subtract''"
    and checked: "lp_return_nonproductive_check (lpp_shape_program SP) blocked"
    and member: "(LPCUser f,length ts)\<in>set blocked"
  shows "\<not>lpp_stable_actual_return operation P
      [(LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) ts) eta)],eta)] rho"
proof
  assume actual: "lpp_stable_actual_return operation P
      [(LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) ts) eta)],eta)] rho"
  have absent: "lp_return_signature (lpp_lift_iatom (lpp_success_atom_eval (f,ts) rho))\<notin>set blocked"
    by (rule lpp_guarded_nonproductive_return[OF checked
      lpp_control_stable_relational_return[OF program builtins selected ordinary actual]])
  show False using absent member
    by (simp add: lp_return_signature_def lpp_lift_iatom_def lpp_success_atom_eval_def)
qed

theorem lpp_control_stable_productive_shape_transfer:
  fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes program: "lpp_control_return_program_check fuel P F SP"
    and builtins: "lpp_open_builtin_check F SP"
    and selected: "f\<in>F"
    and ordinary: "f\<noteq>''2:is''" "f\<noteq>''1:integer''" "f\<noteq>''2:;''" "f\<noteq>''3:subtract''"
    and checked: "lp_return_nonproductive_check (lpp_shape_program SP) blocked"
    and shapes: "lp_return_shape_program_check shape_fuel G modes
      (lp_return_productive_program (lpp_shape_program SP) blocked)"
    and seeds: "lp_return_shape_known G inputs eta"
    and flow: "lp_return_shape_transfer shape_fuel G modes (LPCUser f,ts) (Some inputs)=Some outputs"
    and actual: "lpp_stable_actual_return operation P
      [(LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) ts) eta)],eta)] rho"
  shows "lp_return_shape_known G outputs rho"
proof -
  have preserved: "lp_return_shape_known G inputs rho"
    by (rule lpp_actual_return_substitution_property[where F="lp_return_shape_known G inputs", OF _ actual])
      (auto intro: lp_return_shape_known_subst simp: seeds)
  have contract: "lp_return_contracts G modes (lp_atom_eval (LPCUser f,ts) rho)"
    using lpp_control_stable_productive_shapes[OF program builtins selected ordinary checked shapes actual]
    by (simp add: lpp_lift_iatom_def lpp_success_atom_eval_def lp_atom_eval_def)
  have valid: "lp_return_facts_valid G rho
      (lp_return_shape_transfer shape_fuel G modes (LPCUser f,ts) (Some inputs))"
    by (rule lp_return_shape_transfer_sound[OF contract])
      (use preserved in \<open>simp add: lp_return_facts_valid_def\<close>)
  show ?thesis using valid[unfolded flow] by (simp add: lp_return_facts_valid_def)
qed

ML \<open>
val checked = [@{thm lpp_control_stable_productive_shapes}, @{thm lpp_control_stable_productive_shape_transfer},
  @{thm lpp_control_nonproductive_no_actual_return}];
val names = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = names [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (names checked)
  then error "Untrusted source return-productivity dependency" else ();
\<close>
end
