theory LP_Cut_Resolution_Test
  imports LP_Cut_Resolution_Check
begin

definition cut_test_program :: "(string,string) lp_cut_program" where
  "cut_test_program = [(Fun (LPCUser ''p'') [Fun (LPCUser ''f'') [Var ''Y'']],
    [LPCAtom (Fun (LPCUser ''q'') [Var ''Y''])])]"

definition cut_test_call where
  "cut_test_call = Fun (LPCUser ''p'') [Var ''X'']"

definition cut_test_saved where
  "cut_test_saved = [LPCGoals [LPCAtom (Fun (LPCUser ''saved'') [Var ''X''])]]"

definition cut_test_next where
  "cut_test_next = [LPCAtom (Fun (LPCUser ''q'') [Var ''$$$$Y''])]"

definition cut_test_anchor where
  "cut_test_anchor = [Fun (LPCUser ''f'') [Var ''$$$$Y'']]"

lemma normalized_resolution_is_accepted:
  "lp_cut_check_resolution cut_test_program 50 2 4 [''X''] [''X''] []
    cut_test_call [] 0 3 cut_test_saved cut_test_next cut_test_anchor"
  by eval

lemma changed_continuation_is_rejected:
  "\<not>lp_cut_check_resolution cut_test_program 50 2 4 [''X''] [''X''] []
    cut_test_call [] 0 3 cut_test_saved
    [LPCAtom (Fun (LPCUser ''q'') [Var ''Z''])] cut_test_anchor"
  by eval

lemma forged_ground_anchor_is_rejected:
  "\<not>lp_cut_check_resolution cut_test_program 50 2 4 [''X''] [''X''] []
    cut_test_call [] 0 3 cut_test_saved cut_test_next [Var ''Z'']"
  by eval

lemma claiming_unknown_input_as_ground_is_rejected:
  "\<not>lp_cut_check_resolution cut_test_program 50 2 4 [''X''] [''Z''] []
    cut_test_call [] 0 3 cut_test_saved cut_test_next [Var ''Z'']"
  by eval

lemma overlapping_namespaces_are_rejected:
  "\<not>lp_cut_check_resolution cut_test_program 50 2 2 [''X''] [''X''] []
    cut_test_call [] 0 3 cut_test_saved cut_test_next cut_test_anchor"
  by eval

lemma nonexistent_source_clause_is_rejected:
  "\<not>lp_cut_check_resolution cut_test_program 50 2 4 [''X''] [''X''] []
    cut_test_call [] 1 3 cut_test_saved cut_test_next cut_test_anchor"
  by eval

end
