theory LP_Prolog_Control_Return_Regression
 imports LP_Prolog_Control_Return_Cover
begin

abbreviation control_reg_x where "control_reg_x \<equiv> Var ''X'' :: string lpc_term"
abbreviation control_reg_y where "control_reg_y \<equiv> Var ''Y'' :: string lpc_term"
abbreviation control_reg_a where "control_reg_a \<equiv> Fun (LPCUser ''0:a'') [] :: string lpc_term"
abbreviation control_reg_b where "control_reg_b \<equiv> Fun (LPCUser ''0:b'') [] :: string lpc_term"
abbreviation control_reg_eq where "control_reg_eq a b \<equiv> (lpp_control_equality,[a,b])"

definition control_reg_program :: "(string,string) lp_cut_program" where
  "control_reg_program = [(Fun (LPCUser ''2:choose'') [control_reg_x,control_reg_y],
    [LPCAtom (Fun (LPCUser ''2:;'') [Fun (LPCUser ''2:->'')
      [Fun LPCEquals [control_reg_x,control_reg_a],
       Fun LPCEquals [control_reg_y,control_reg_x]],
       Fun LPCEquals [control_reg_y,control_reg_b]])])]"

definition control_reg_yes :: "string lpp_success_clause" where
  "control_reg_yes = ((''2:choose'',[control_reg_x,control_reg_y]),
    [control_reg_eq control_reg_x control_reg_a,control_reg_eq control_reg_y control_reg_x,
     control_reg_eq control_reg_x control_reg_a,control_reg_eq control_reg_y control_reg_x],[])"
definition control_reg_no :: "string lpp_success_clause" where
  "control_reg_no = ((''2:choose'',[control_reg_x,control_reg_y]),
    [control_reg_eq control_reg_y control_reg_b,control_reg_eq control_reg_y control_reg_b],[])"

lemma control_branch_shared_symbols:
  "lpp_branch_lower_term (Fun LPCComma
    [Fun LPCEquals [control_reg_x,control_reg_y],Fun LPCTruth []]) =
     Some [LPCUnify control_reg_x control_reg_y,LPCTrue]"
  by code_simp
lemma control_branch_cut_rejected:
  "lpp_branch_lower_term (Fun LPCBang []) = None"
  by code_simp
lemma control_branch_dynamic_rejected:
  "lpp_branch_lower_term (Fun LPCComma [Fun LPCTruth [],control_reg_x]) = None"
  by code_simp

lemma control_return_complete_cover:
  "lpp_control_return_program_check 8 control_reg_program {''2:choose'',lpp_control_equality}
    [lpp_control_equality_clause,control_reg_yes,control_reg_no]"
  by code_simp
lemma control_return_missing_else_rejected:
  "\<not>lpp_control_return_program_check 8 control_reg_program {''2:choose'',lpp_control_equality}
    [lpp_control_equality_clause,control_reg_yes]"
  by code_simp
lemma control_return_missing_then_rejected:
  "\<not>lpp_control_return_program_check 8 control_reg_program {''2:choose'',lpp_control_equality}
    [lpp_control_equality_clause,control_reg_no]"
  by code_simp
lemma control_return_missing_equality_rejected:
  "\<not>lpp_control_return_program_check 8 control_reg_program {''2:choose'',lpp_control_equality}
    [control_reg_yes,control_reg_no]"
  by code_simp
lemma control_return_missing_dependency_rejected:
  "\<not>lpp_control_return_program_check 8 control_reg_program {''2:choose''}
    [lpp_control_equality_clause,control_reg_yes,control_reg_no]"
  by code_simp

ML \<open>
val checked = [@{thm control_branch_shared_symbols},@{thm control_branch_cut_rejected},
  @{thm control_branch_dynamic_rejected},@{thm control_return_complete_cover},@{thm control_return_missing_else_rejected},
  @{thm control_return_missing_then_rejected},@{thm control_return_missing_equality_rejected},
  @{thm control_return_missing_dependency_rejected}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted control return regressions" else ();
\<close>
end
