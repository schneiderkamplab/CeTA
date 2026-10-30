theory LP_Prolog_Finite_Actual_Contexts
 imports LP_Prolog_Finite_Triple_Captured LP_Prolog_Evaluation_Comparison LP_Prolog_Evaluation_Transport LP_Prolog_Triple_Integer_Return
begin

lemma lpp_finite_actual_return_preserves_context:
  assumes actual: "lpp_finite_actual_return P ss eta"
    and initialized: "list_all (\<lambda>frame. lpp_evaluation_context_holds lpp_finite_evaluation_result SP incoming_context (snd frame)) ss"
  shows "lpp_evaluation_context_holds lpp_finite_evaluation_result SP incoming_context eta"
  by (rule lpp_actual_return_substitution_property[OF
    lpp_evaluation_context_runtime_subst[where E=lpp_finite_evaluation_result, OF lpp_finite_evaluation_subst] actual initialized])

lemma lpp_evaluation_add_integers_sound:
  "lpp_evaluation_context_holds E SP incoming_context eta \<Longrightarrow> lpp_integer_known K eta \<Longrightarrow>
    lpp_evaluation_context_holds E SP (lpp_context_add_integers incoming_context K) eta"
  by (cases incoming_context) (auto simp: lpp_evaluation_context_holds_def lpp_integer_known_def lpp_is_integer_def list_all_iff)

end
