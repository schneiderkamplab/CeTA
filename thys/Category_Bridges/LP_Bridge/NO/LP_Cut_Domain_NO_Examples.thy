theory LP_Cut_Domain_NO_Examples
  imports LP_Cut_Domain_NO_Checker
begin

text \<open>The nullary program p :- p grows an invocation barrier on every
iteration. This exercises the checked pumping rule, not merely an exact cycle
of stack states. Its empty solved substitution is valid in both domains.\<close>
definition cut_loop_program where
  "cut_loop_program p = [(Fun (LPCUser p) [],[LPCAtom (Fun (LPCUser p) [])])]"
definition cut_loop_trace where
  "cut_loop_trace p =
    [(LPCNOCase 0,[LPCClause [LPCAtom (Fun (LPCUser p) [])] 0 0,LPCBarrier 0]),
     (LPCNOResolve 0 [] [],[LPCGoals [LPCAtom (Fun (LPCUser p) [])],LPCBarrier 0])]"
lemma cut_loop_certificate:
  "lpc_no_check_source 4 (cut_loop_program p) p [] [] (Fun (LPCUser p) [])
    [] [LPCBarrier 0] [] (cut_loop_trace p)"
  by (simp add: cut_loop_program_def cut_loop_trace_def lpc_no_check_source_def
    lp_cut_source_program_def lp_cut_check_case_def lp_cut_fresh_def lp_cut_slice_def
    lpc_no_resolve_def lp_cut_short_goals_def lpc_check_mgu_def
    lp_cut_normalize_def lpc_mgu_substitution_def lp_atom_subst_def lp_normalize_goals_code)

lemma cut_loop_finite_nontermination:
  "\<not> lp_cut_finite_terminates
    [(SFun (LogicUser p) [],[LogicAtom (SFun (LogicUser p) [])])] p []"
  using finite_cut.canonical_no_certificate[OF cut_loop_certificate[of p]]
  by (simp add: lp_cut_finite_terminates_def cut_finite_domain_iff
    cut_program_back_def cut_loop_program_def)
lemma cut_loop_rational_nontermination:
  "\<not> lp_cut_rational_terminates
    [(SFun (LogicUser p) [],[LogicAtom (SFun (LogicUser p) [])])] p []"
  using rational_cut.canonical_no_certificate[OF cut_loop_certificate[of p]]
  by (simp add: lp_cut_rational_terminates_def cut_rational_runtime_def
    cut_program_back_def cut_loop_program_def)

end
