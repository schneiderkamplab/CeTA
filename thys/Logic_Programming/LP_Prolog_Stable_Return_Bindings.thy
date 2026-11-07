theory LP_Prolog_Stable_Return_Bindings
 imports LP_Prolog_Stable_Return_Formula
begin

definition lpp_check_return_bindings where
  "lpp_check_return_bindings summaries ps bindings row_constraints formula =
    (list_all (lpp_check_return_constraint summaries ps) row_constraints \<and>
      list_all (\<lambda>c. list_all (\<lambda>t. LPPMagnitudeKey t\<in>set (map fst bindings))
        (lpp_return_terms ps c)) row_constraints \<and>
      formula=Conjunction (map (lpp_return_formula (lpp_numeric_rename bindings o LPPMagnitudeKey) ps) row_constraints))"

lemma lpp_check_return_bindings_typed:
  "lpp_check_return_bindings summaries ps bindings row_constraints formula \<Longrightarrow> IA4.formula formula"
  by (auto simp: lpp_check_return_bindings_def list_all_iff lpp_return_formula_typed)

theorem lpp_check_return_bindings_sound:
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_magnitude_program summaries P receipts"
    and checked: "lpp_check_return_bindings summaries ps bindings row_constraints formula"
    and success: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation))
      (map (\<lambda>a. lpp_success_atom_eval a eta) ps)"
    and assigned: "\<And>numeric_key. numeric_key\<in>set (map fst bindings) \<Longrightarrow>
      rho (lpp_numeric_rename bindings numeric_key)=lpp_stable_key_value operation eta source_values numeric_key"
  shows "IA4.satisfies (lpp_integer_assignment rho) formula"
proof -
  have each: "IA4.satisfies (lpp_integer_assignment rho)
    (lpp_return_formula (lpp_numeric_rename bindings o LPPMagnitudeKey) ps c)"
    if member: "c\<in>set row_constraints" for c
  proof (rule lpp_checked_return_formula[OF compatible program _ success])
    show "lpp_check_return_constraint summaries ps c"
      using checked member by (auto simp: lpp_check_return_bindings_def list_all_iff)
    fix t assume term_member: "t\<in>set (lpp_return_terms ps c)"
    have bound: "LPPMagnitudeKey t\<in>set (map fst bindings)"
      using checked member term_member by (auto simp: lpp_check_return_bindings_def list_all_iff)
    show "rho ((lpp_numeric_rename bindings o LPPMagnitudeKey) t)=
      abs (lpp_stable_scaled_bound operation (lp_ieval t eta))"
      using assigned[OF bound] by simp
  qed
  show ?thesis using checked each
    by (auto simp: lpp_check_return_bindings_def list_all_iff)
qed

ML \<open>
val checked = [@{thm lpp_check_return_bindings_sound}, @{thm lpp_check_return_bindings_typed}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted return bindings dependency" else ();
\<close>
end
