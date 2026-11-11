theory LP_Prolog_Stable_Natural_Return_Context
 imports LP_Prolog_Stable_Type_Identity LP_Prolog_Natural_Return_Context
begin

lemma lpp_stable_natural_comparison:
  assumes compatible: "lpp_stable_integer_operations operation" and bound: "0\<le>n"
  shows "lpp_stable_compare_outcome operation LPPIntLessEqual (lpp_integer_value 0)
    (lpp_integer_value n) (LPPBuiltinSuccess LPIVar)"
  using bound
  by (simp only: lpp_stable_compare_integer_exact[OF compatible lpp_integer_evaluation.literal lpp_integer_evaluation.literal]
    lpp_integer_compare_outcome_exact[OF lpp_integer_evaluation.literal lpp_integer_evaluation.literal]) simp

lemma lpp_add_stable_natural_holds:
  assumes compatible: "lpp_stable_integer_operations operation"
    and held: "lpp_stable_context_holds operation P ctx eta"
    and result: "lp_ieval a eta=lpp_integer_value n" and bound: "0\<le>n"
  shows "lpp_stable_context_holds operation P (lpp_add_natural_observation a ctx) eta"
  using held lpp_add_evaluation_natural_holds[of "lpp_stable_scalar_evaluation operation" P ctx eta a n]
    lpp_stable_natural_comparison[OF compatible bound] result bound
  by (cases ctx) (auto simp: lpp_stable_context_holds_def lpp_add_natural_observation_def lpp_is_integer_def)

ML \<open>
val checked = [@{thm lpp_add_stable_natural_holds}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted stable natural return context" else ();
\<close>
end
