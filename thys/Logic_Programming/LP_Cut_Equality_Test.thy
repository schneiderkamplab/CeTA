theory LP_Cut_Equality_Test
  imports LP_Cut_Equality LP_Cut_Resolution_Test LP_Cut_Scopes
begin

definition cut_eq_constant :: "(string lp_cut_symbol,string) term" where
  "cut_eq_constant = Fun (LPCUser ''a'') []"

lemma cut_equality_regressions:
  "lp_cut_check_unify 50 2 4 [] [] (Var ''X'') cut_eq_constant
    [LPCAtom (Fun (LPCUser ''q'') [Var ''X''])] cut_test_saved
    [LPCAtom (Fun (LPCUser ''q'') [cut_eq_constant])] \<and>
   \<not>lp_cut_check_unify 50 2 4 [] [] (Var ''X'') cut_eq_constant
    [LPCAtom (Fun (LPCUser ''q'') [Var ''X''])] cut_test_saved
    [LPCAtom (Fun (LPCUser ''q'') [Var ''X''])] \<and>
   \<not>lp_cut_check_equality 50 (Var ''X'')
    (Fun (LPCUser ''f'') [Var ''X'']) LPCAlwaysFailure \<and>
   \<not>lp_cut_check_equality 50 (Var ''X'') cut_eq_constant LPCAlwaysSuccess"
  by eval

lemma equality_substitutes_active_not_saved:
  "lp_cut_check_unify 50 2 4 [] [] (Var ''X'') cut_eq_constant
    [LPCAtom (Fun (LPCUser ''q'') [Var ''X''])] cut_test_saved
    [LPCAtom (Fun (LPCUser ''q'') [cut_eq_constant])]"
  using cut_equality_regressions by blast

lemma equality_wrong_active_value_rejected:
  "\<not>lp_cut_check_unify 50 2 4 [] [] (Var ''X'') cut_eq_constant
    [LPCAtom (Fun (LPCUser ''q'') [Var ''X''])] cut_test_saved
    [LPCAtom (Fun (LPCUser ''q'') [Var ''X''])]"
  using cut_equality_regressions by blast

lemma equality_cyclic_equation_not_declared_failure:
  "\<not>lp_cut_check_equality 50 (Var ''X'')
    (Fun (LPCUser ''f'') [Var ''X'']) LPCAlwaysFailure"
  using cut_equality_regressions by blast

lemma equality_unknown_is_not_universal_success:
  "\<not>lp_cut_check_equality 50 (Var ''X'') cut_eq_constant LPCAlwaysSuccess"
  using cut_equality_regressions by blast

end
