theory LP_Prolog_Control_Shape_Return
 imports LP_Prolog_Control_Stable_Return LP_Prolog_Inline_Shape_Return LP_Prolog_Stable_Return_Context
begin

text \<open>Conditional helper returns expose the existing shared regular-shape
contract algebra. Grammars may constrain a list spine without constraining its
elements. No termination premise or whole-value groundness is introduced.\<close>

theorem lpp_control_stable_shape_contracts:
  fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes program: "lpp_control_return_program_check fuel P F SP"
    and builtins: "lpp_open_builtin_check F SP"
    and selected: "f\<in>F"
    and ordinary: "f\<noteq>''2:is''" "f\<noteq>''1:integer''" "f\<noteq>''2:;''" "f\<noteq>''3:subtract''"
    and contracts: "lp_return_shape_program_check shape_fuel G modes (lpp_shape_program SP)"
    and actual: "lpp_stable_actual_return operation P
      [(LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) ts) eta)],eta)] rho"
  shows "lp_return_contracts G modes (lpp_lift_iatom (lpp_success_atom_eval (f,ts) rho))"
  by (rule lpp_guarded_return_shape_contracts[OF contracts
    lpp_control_stable_relational_return[OF program builtins selected ordinary actual]])


theorem lpp_control_stable_shape_transfer:
  fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes program: "lpp_control_return_program_check fuel P F SP"
    and builtins: "lpp_open_builtin_check F SP"
    and selected: "f\<in>F"
    and ordinary: "f\<noteq>''2:is''" "f\<noteq>''1:integer''" "f\<noteq>''2:;''" "f\<noteq>''3:subtract''"
    and contracts: "lp_return_shape_program_check shape_fuel G modes (lpp_shape_program SP)"
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
    using lpp_control_stable_shape_contracts[OF program builtins selected ordinary contracts actual]
    by (simp add: lpp_lift_iatom_def lpp_success_atom_eval_def lp_atom_eval_def)
  have valid: "lp_return_facts_valid G rho
      (lp_return_shape_transfer shape_fuel G modes (LPCUser f,ts) (Some inputs))"
    by (rule lp_return_shape_transfer_sound[OF contract])
      (use preserved in \<open>simp add: lp_return_facts_valid_def\<close>)
  show ?thesis using valid[unfolded flow] by (simp add: lp_return_facts_valid_def)
qed

end
