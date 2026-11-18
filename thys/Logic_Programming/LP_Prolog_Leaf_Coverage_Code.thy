theory LP_Prolog_Leaf_Coverage_Code
 imports LP_Prolog_Leaf_Table_Check
begin

text \<open>Traverse finite source goal lists directly. No equality or comparison
instance for operational goals is needed to collect their variable support.\<close>

fun lpp_leaf_terms_variables where
 "lpp_leaf_terms_variables [] = {}"
| "lpp_leaf_terms_variables (t#ts) = vars_term t \<union> lpp_leaf_terms_variables ts"

fun lpp_leaf_goals_variables where
 "lpp_leaf_goals_variables [] = {}"
| "lpp_leaf_goals_variables (g#gs) = lpp_leaf_terms_variables (lp_cut_terms g) \<union> lpp_leaf_goals_variables gs"

lemma lpp_leaf_terms_variables_correct:
 "lpp_leaf_terms_variables ts = (\<Union>t\<in>set ts. vars_term t)"
 by (induct ts) auto

lemma lpp_leaf_goals_variables_correct:
 "lpp_leaf_goals_variables gs = (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 by (induct gs) (auto simp: lpp_leaf_terms_variables_correct)

declare lpp_check_relational_leaf_coverage_def[code del]
declare lpp_check_ground_relational_leaf_coverage_def[code del]

lemma lpp_check_relational_leaf_coverage_code[code]:
 "lpp_check_relational_leaf_coverage facts slots payload call gs =
   list_all (\<lambda>slot. slot < length payload \<and>
    vars_term (payload!slot) \<subseteq> lpp_functor_support_closure facts
     (vars_term call \<union> lpp_leaf_goals_variables gs)) slots"
 by (simp add: lpp_check_relational_leaf_coverage_def list_all_iff lpp_leaf_goals_variables_correct)

lemma lpp_check_ground_relational_leaf_coverage_code[code]:
 "lpp_check_ground_relational_leaf_coverage G facts slots payload call gs =
   list_all (\<lambda>slot. slot < length payload \<and>
    vars_term (payload!slot) \<subseteq> lpp_functor_support_closure facts
     (G \<union> vars_term call \<union> lpp_leaf_goals_variables gs)) slots"
 by (simp add: lpp_check_ground_relational_leaf_coverage_def list_all_iff lpp_leaf_goals_variables_correct)

ML \<open>
val checked = @{thms lpp_leaf_terms_variables_correct lpp_leaf_goals_variables_correct
 lpp_check_relational_leaf_coverage_code lpp_check_ground_relational_leaf_coverage_code};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted leaf coverage equations" else ();
\<close>
end
