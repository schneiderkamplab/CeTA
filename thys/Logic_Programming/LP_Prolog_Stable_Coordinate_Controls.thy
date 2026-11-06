theory LP_Prolog_Stable_Coordinate_Controls
 imports LP_Prolog_Stable_Coordinates LP_Prolog_Scalar_Bound_Controls
begin

lemma lpp_stable_float_counter_rejected:
  "\<not> lpp_stable_coordinate_value operation LPPStableInteger (lpp_binary64_value bits) k"
  by (simp add: lpp_binary64_not_integer)

lemma lpp_stable_uninitialized_bound_rejected:
  "\<not> lpp_stable_coordinate_value operation LPPStableUpperBound (LPIVar x) k"
  by (auto elim: lp_seg_ground.cases)

lemma lpp_stable_integer_expression_bound:
  "lpp_stable_expression_bound operation (lpp_integer_value k)=k"
  by (simp add: lpp_stable_expression_bound_exact[OF lpp_stable_integer_literal]
    lpp_scalar_floor_exact[OF lpp_integer_scalar_observation])

lemma lpp_stable_uninitialized_expression_bound:
  "lpp_stable_expression_bound operation (LPIVar x)=0"
proof -
  have "\<not> lpp_stable_scalar_evaluation operation (LPIVar x) v" for v
    by (auto dest: lpp_stable_scalar_evaluation_ground elim: lp_seg_ground.cases)
  then show ?thesis by (simp add: lpp_stable_expression_bound_def)
qed

text \<open>Dropping the groundness premise would make bound transport false:
an uninitialized variable can later become a different numeric bound.\<close>
lemma lpp_stable_bound_without_ground_changes:
  "lpp_stable_expression_bound operation (LPIVar x) \<noteq>
    lpp_stable_expression_bound operation (lp_isubst (LPIVar x) (\<lambda>_. lpp_integer_value 1))"
  by (simp add: lpp_stable_uninitialized_expression_bound lpp_stable_integer_expression_bound)

ML \<open>
val checked = [@{thm lpp_stable_float_counter_rejected}, @{thm lpp_stable_uninitialized_bound_rejected},
  @{thm lpp_stable_integer_expression_bound}, @{thm lpp_stable_bound_without_ground_changes}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable coordinate control dependency" else ();
\<close>
end
