theory LP_Prolog_Finite_Numeric_Projection_Regression
 imports LP_Prolog_Finite_Numeric_Projection
begin

lemma numeric_projection_keeps_selected_order:
  "lpp_select_arguments [2,0] [a,b,c] = [c,a]"
  by (simp add: lpp_select_arguments_def)

lemma numeric_projection_rejects_missing_argument:
  "\<not>lpp_check_call_projection (\<lambda>_. [2]) (p,[a,b])"
  by (simp add: lpp_check_call_projection_def)

lemma numeric_projection_rejects_repeated_argument:
  "\<not>lpp_check_call_projection (\<lambda>_. [0,0]) (p,[a])"
  by (simp add: lpp_check_call_projection_def)

lemma numeric_projection_keeps_guards_and_helpers:
  "lpp_project_observed_triple positions ((h,ps,b,gs),os) =
    ((lpp_project_call positions h,ps,lpp_project_call positions b,gs),os)"
  by simp

lemma numeric_projection_cannot_remove_self_call:
  assumes "(a,a)\<in>lpp_finite_observed_calls D P"
  shows "(lpp_project_call positions a,lpp_project_call positions a)\<in>
    lpp_finite_observed_calls (lpp_project_observed_triple positions ` D) P"
  by (rule lpp_finite_observed_call_projection[OF assms])

lemma numeric_projection_empty_still_has_call:
  "lpp_project_call (\<lambda>_. []) (p,xs) = (p,[])"
  by (simp add: lpp_project_call_def lpp_select_arguments_def)

end
