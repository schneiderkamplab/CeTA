theory LP_Prolog_Scalar_Bound_Controls
  imports LP_Prolog_Scalar_Bound_Observation LP_Prolog_Finite_Evaluation
begin

lemma lpp_binary64_name_not_integer:
  "lpp_binary64_name bits\<noteq>lpp_integer_name n"
  using lpp_binary64_not_integer[of bits n]
  by (simp add: lpp_binary64_value_def lpp_integer_value_def)

lemma lpp_binary64_no_integer_evaluation:
  "\<not>lpp_integer_evaluation (lpp_binary64_value bits) n"
proof
  assume evaluation: "lpp_integer_evaluation (lpp_binary64_value bits) n"
  then show False
    by (cases rule: lpp_integer_evaluation.cases)
      (auto simp: lpp_binary64_value_def lpp_integer_value_def lpp_binary64_name_not_integer)
qed

text \<open>The current finite envelope is an overapproximation, not an exact
successful-return observation for floating scalars. Its nondeterminism is a
concrete reason that the scalar-bound theorem cannot simply be plugged into
that envelope: later comparisons must share the actual fixed result.\<close>

lemma lpp_finite_envelope_does_not_fix_float_result:
  "lpp_finite_evaluation_result (lpp_binary64_value bits) (lpp_integer_value 0) \<and>
   lpp_finite_evaluation_result (lpp_binary64_value bits) (lpp_integer_value 1) \<and>
   lpp_integer_value 0\<noteq>lpp_integer_value 1"
  by (simp add: lpp_finite_evaluation_result_def lpp_binary64_no_integer_evaluation
    lpp_binary64_value_ground lpp_integer_value_def)

ML \<open>
val checked = [@{thm lpp_binary64_no_integer_evaluation},
  @{thm lpp_finite_envelope_does_not_fix_float_result}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted scalar bound control dependency" else ();
\<close>
end
