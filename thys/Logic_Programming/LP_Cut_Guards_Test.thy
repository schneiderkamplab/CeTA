theory LP_Cut_Guards_Test
  imports LP_Cut_Guards
begin

lemma symbolic_unifier_does_not_remove_failure:
  "\<not>lp_cut_check_coverage 50 2 (Fun ''p'' [Var ''X''])
     (Fun ''p'' [Fun ''a'' []]) [] LPCAlwaysSuccess"
  by eval

lemma general_head_covers_every_instance:
  "lp_cut_check_coverage 50 2 (Fun ''p'' [Var ''X''])
     (Fun ''p'' [Var ''Y'']) [(''Y'',Var ''X'')] LPCAlwaysSuccess"
  by eval

lemma constructor_clash_is_valid:
  "lp_cut_check_coverage 50 2 (Fun ''p'' [Fun ''a'' []])
     (Fun ''p'' [Fun ''b'' []]) [] LPCAlwaysFailure"
  by eval

lemma repeated_head_variable_does_not_imply_success:
  "\<not>lp_cut_check_coverage 50 2 (Fun ''p'' [Var ''X'',Var ''Y''])
     (Fun ''p'' [Var ''Z'',Var ''Z'']) [(''Z'',Var ''X'')] LPCAlwaysSuccess"
  by eval

lemma shared_call_covers_repeated_head:
  "lp_cut_check_coverage 50 2 (Fun ''p'' [Var ''X'',Var ''X''])
     (Fun ''p'' [Var ''Z'',Var ''Z'']) [(''Z'',Var ''X'')] LPCAlwaysSuccess"
  by eval

lemma cyclic_unifier_is_not_a_clash:
  "\<not>lp_cut_check_coverage 10 2
    (Fun ''p'' [Var ''X'',Fun ''f'' [Var ''X'']])
    (Fun ''p'' [Fun ''f'' [Var ''Y''],Var ''Y'']) [] LPCAlwaysFailure"
  by eval

lemma no_aliasing_of_clause_variables:
  "\<not>lp_cut_check_coverage 50 0 (Fun ''p'' [Var ''X''])
     (Fun ''p'' [Fun ''a'' []]) [] LPCAlwaysFailure"
  by eval

lemma exhausted_normalizer_is_not_a_clash:
  "\<not>lp_cut_check_coverage 0 2 (Fun ''p'' [Fun ''a'' []])
     (Fun ''p'' [Fun ''b'' []]) [] LPCAlwaysFailure"
  by eval

lemma equality_sharing_proves_clash:
  "lp_cut_check_equality 50 (Fun ''p'' [Var ''X'',Var ''X''])
     (Fun ''p'' [Fun ''a'' [],Fun ''b'' []]) LPCAlwaysFailure"
  by eval

lemma cyclic_equality_is_not_failure:
  "\<not>lp_cut_check_equality 50 (Var ''X'') (Fun ''f'' [Var ''X'']) LPCAlwaysFailure"
  by eval

lemma equality_instance_does_not_remove_failure:
  "\<not>lp_cut_check_equality 50 (Var ''X'') (Fun ''a'' []) LPCAlwaysSuccess"
  by eval

lemma reflexive_equality_covers_all_values:
  "lp_cut_check_equality 0 (Var ''X'' :: (string,string) term) (Var ''X'') LPCAlwaysSuccess"
  by eval

end
