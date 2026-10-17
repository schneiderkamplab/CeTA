theory Outermost_RZ_Checker_Tests
  imports Outermost_RZ_Checker
begin

text \<open>Universal guard regressions, separate from genuine replay coverage.\<close>

lemma rz_rejects_quasi_left_linearity:
  assumes "\<not> rz_quasi_left_linear_check R"
  shows "\<not> isOK (check_outermost_rz_termination_proof I J i R
    (Outermost_RZ_Transformation top_sym up_sym down block c flats patterns child))"
  using assms by (auto simp: Let_def)

lemma rz_rejects_grounding_freshness:
  assumes "(c,0) \<in> set (remdups (funas_trs_list R))"
  shows "\<not> isOK (check_outermost_rz_termination_proof I J i R
    (Outermost_RZ_Transformation top_sym up_sym down block c flats patterns child))"
  using assms by (auto simp: Let_def)

lemma rz_rejects_marker_freshness:
  assumes "(block,0) \<in> set (remdups ((c,0) # remdups (funas_trs_list R)))"
  shows "\<not> isOK (check_outermost_rz_termination_proof I J i R
    (Outermost_RZ_Transformation top_sym up_sym down block c flats patterns child))"
  using assms by (auto simp: Let_def)

lemma rz_rejects_flat_map:
  assumes "\<not> rz_flat_map_check (remdups ((c,0) # remdups (funas_trs_list R))) flats"
  shows "\<not> isOK (check_outermost_rz_termination_proof I J i R
    (Outermost_RZ_Transformation top_sym up_sym down block c flats patterns child))"
  using assms by (auto simp: Let_def)

lemma rz_rejects_patterns:
  assumes "\<not> rz_pattern_check (remdups ((c,0) # remdups (funas_trs_list R))) patterns"
  shows "\<not> isOK (check_outermost_rz_termination_proof I J i R
    (Outermost_RZ_Transformation top_sym up_sym down block c flats patterns child))"
  using assms by (auto simp: Let_def)

lemma rz_rejects_cover:
  assumes "\<not> rz_cover_check (remdups ((c,0) # remdups (funas_trs_list R))) block ''__rz_cover'' (rz_linear_lhss R @ patterns)"
  shows "\<not> isOK (check_outermost_rz_termination_proof I J i R
    (Outermost_RZ_Transformation top_sym up_sym down block c flats patterns child))"
  using assms by (auto simp: Let_def)

end
