theory Relative_ADP_Checker_Tests
  imports Relative_ADP_Checker_Adapter
begin

definition test_relative_adp :: "(string, string) adp" where
  "test_relative_adp =
    (plain_adp_term (Fun ''f'' [Fun ''s'' [Var ''x'']]),
     plain_adp_term (Fun ''f'' [Var ''x'']))"

definition test_relative_adp_order :: "string redtriple_impl" where
  "test_relative_adp_order = Int_carrier
    [(( ''f'', 1), (0, [1])), (( ''s'', 1), (1, [1]))]"

lemma test_relative_adp_residual:
  "relative_adp_erasure_residual
      [test_relative_adp] [] [test_relative_adp] =
    ([], [erase_annotations_adp test_relative_adp])"
  by eval

lemma test_relative_adp_empty_selection_rejected:
  "\<not> isOK (check_relative_adp_erasure_redpair
    test_relative_adp_order [test_relative_adp] [] [])"
  by (simp add: test_relative_adp_order_def test_relative_adp_def
      check_relative_adp_erasure_redpair_def)

end
