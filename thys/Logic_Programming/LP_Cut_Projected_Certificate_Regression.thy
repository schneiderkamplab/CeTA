theory LP_Cut_Projected_Certificate_Regression
  imports LP_Cut_Projected_XML LP_Cut_Projected_Residual_Regression
begin

lemma projected_clause_positive:
  "lpc_check_projected_clauses (the (afs_of []))
    [(Fun (LPCUser ''f'') [Var ''X''],Fun (LPCUser ''g'') [Var ''X''])]
    [((LPCUser ''f'',[Var ''X'']),[(LPCUser ''g'',[Var ''X''])])]"
  by eval

lemma projected_clause_missing_rule_rejected:
  "\<not>lpc_check_projected_clauses (the (afs_of [])) []
    [((LPCUser ''f'',[Var ''X'']),[(LPCUser ''g'',[Var ''X''])])]"
  by eval

lemma projected_clause_fresh_output_rejected:
  "\<not>lpc_check_projected_clauses (the (afs_of []))
    [(Fun (LPCUser ''f'') [Var ''X''],Fun (LPCUser ''g'') [Var ''Y''])]
    [((LPCUser ''f'',[Var ''X'']),[(LPCUser ''g'',[Var ''Y''])])]"
  by eval

lemma projected_clause_conjunction_rejected:
  "\<not>lpc_check_projected_clauses (the (afs_of []))
    [(Fun (LPCUser ''f'') [Var ''X''],Fun (LPCUser ''g'') [Var ''X''])]
    [((LPCUser ''f'',[Var ''X'']),[(LPCUser ''g'',[Var ''X'']),(LPCUser ''h'',[])])]"
  by eval

lemma projected_nested_exhausted_rejected:
  "\<not>lpc_check_projected_nested fuel 0 P filtering R Q modules actions i"
  by simp

lemma projected_nested_missing_module_rejected:
  "\<not>lpc_check_projected_nested fuel (Suc k) P filtering R Q [] actions i"
  by simp

ML \<open>
val audited = [@{thm check_lpc_projected_xml_sound}];
val names = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = names [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof audited orelse
  exists (fn n => not (member (op =) inherited n)) (names audited)
  then error "Untrusted projected graph certificate dependency" else ();
\<close>

end
