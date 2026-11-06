theory LP_Prolog_Stable_Bound_Row
 imports LP_Prolog_Stable_Coordinate_Tuples LP_Prolog_Stable_Call_Projection
begin

datatype 'v lpp_stable_numeric_key =
    LPPIntegerKey 'v
  | LPPBoundKey "(string lp_cut_symbol,'v) term"

fun lpp_check_stable_upper_observation where
  "lpp_check_stable_upper_observation K (LPPOComparison c a b) expression bound_term =
    ((c=LPPIntLess \<or> c=LPPIntLessEqual) \<and>
      a=lpp_expression_term expression \<and> lpp_expression_check K expression \<and> b=bound_term)"
| "lpp_check_stable_upper_observation K observation expression bound_term = False"

definition lpp_stable_upper_condition where
  "lpp_stable_upper_condition expression bound_term =
    (LPPIntLessEqual, map_lpp_integer_expression LPPIntegerKey expression,
      LPPEVariable (LPPBoundKey bound_term))"

text \<open>The two key constructors keep integer inputs and observed bounds
separate even if they originate from the same source variable. Bound expressions
are preserved in the receipt; no claim of integer typing is made for them.\<close>

lemma lpp_checked_stable_upper_condition:
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_stable_upper_observation K observation expression bound_term"
    and observed: "lpp_stable_observation_holds operation eta observation"
    and typed: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (rho (LPPIntegerKey x))"
    and bound_value: "rho (LPPBoundKey bound_term)=lpp_stable_expression_bound operation (lp_ieval bound_term eta)"
  shows "lpp_numeric_condition_holds rho (lpp_stable_upper_condition expression bound_term)"
proof -
  obtain c a b where shape: "observation=LPPOComparison c a b"
    and ordered: "c=LPPIntLess \<or> c=LPPIntLessEqual"
    and expression: "a=lpp_expression_term expression"
    and check: "lpp_expression_check K expression" and bound_term: "b=bound_term"
    using checked by (cases observation) auto
  have integer: "lpp_integer_evaluation (lp_ieval a eta)
    (lpp_expression_value expression (rho o LPPIntegerKey))"
    unfolding expression by (rule lpp_expression_evaluation[OF check]) (use typed in auto)
  have success: "lpp_stable_compare_outcome operation c (lp_ieval a eta) (lp_ieval b eta)
    (LPPBuiltinSuccess LPIVar)"
    using observed by (simp add: shape)
  have inequality: "lpp_expression_value expression (rho o LPPIntegerKey) \<le>
    lpp_stable_expression_bound operation (lp_ieval b eta)"
    by (rule lpp_stable_expression_bound_comparison[OF compatible integer ordered success])
  show ?thesis using inequality bound_value
    by (simp add: lpp_stable_upper_condition_def lpp_expression_rename_value bound_term)
qed

definition lpp_check_stable_upper_row_guard where
  "lpp_check_stable_upper_row_guard K observation expression bound_term bindings formula =
    (lpp_check_stable_upper_observation K observation expression bound_term \<and>
      distinct (map fst bindings) \<and>
      list_all (\<lambda>x. map_of bindings (LPPIntegerKey x)\<noteq>None) K \<and>
      map_of bindings (LPPBoundKey bound_term)\<noteq>None \<and>
      formula=lpp_numeric_condition_formula
        (lpp_rename_numeric_condition (lpp_numeric_rename bindings) (lpp_stable_upper_condition expression bound_term)))"

theorem lpp_check_stable_upper_row_guard_sound:
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_stable_upper_row_guard K observation expression bound_term bindings formula"
    and observed: "lpp_stable_observation_holds operation eta observation"
    and typed: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (rho (lpp_numeric_rename bindings (LPPIntegerKey x)))"
    and bound_value: "rho (lpp_numeric_rename bindings (LPPBoundKey bound_term))=
      lpp_stable_expression_bound operation (lp_ieval bound_term eta)"
  shows "IA4.satisfies (lpp_integer_assignment rho) formula" "IA4.formula formula"
proof -
  have check: "lpp_check_stable_upper_observation K observation expression bound_term"
    and formula: "formula=lpp_numeric_condition_formula
      (lpp_rename_numeric_condition (lpp_numeric_rename bindings) (lpp_stable_upper_condition expression bound_term))"
    using checked by (auto simp: lpp_check_stable_upper_row_guard_def)
  have truth: "lpp_numeric_condition_holds (rho o lpp_numeric_rename bindings)
    (lpp_stable_upper_condition expression bound_term)"
    by (rule lpp_checked_stable_upper_condition[OF compatible check observed])
      (use typed bound_value in auto)
  have renamed: "lpp_numeric_condition_holds rho
    (lpp_rename_numeric_condition (lpp_numeric_rename bindings) (lpp_stable_upper_condition expression bound_term))"
    using truth by (simp only: lpp_rename_numeric_condition_holds)
  show "IA4.satisfies (lpp_integer_assignment rho) formula"
    using renamed by (simp add: formula lpp_stable_upper_condition_def lpp_comparison_typed_assignment lpp_expression_typed_assignment algebra.eval.simps)
  show "IA4.formula formula"
    by (simp add: formula lpp_stable_upper_condition_def lpp_comparison_its_type lpp_expression_its_type less_Suc_eq)
qed

ML \<open>
val checked = [@{thm lpp_checked_stable_upper_condition}] @ @{thms lpp_check_stable_upper_row_guard_sound};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable bound_term row dependency" else ();
\<close>
end
