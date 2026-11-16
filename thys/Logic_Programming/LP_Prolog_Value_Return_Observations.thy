theory LP_Prolog_Value_Return_Observations
 imports LP_Prolog_Success_Value_Domains LP_Prolog_Stable_Observed_Calls
begin

text \<open>A successful integer-valued argument yields a derived arithmetic
observation, not a literal-integer assertion. Modulo one is total on integers;
its checked observation lets existing evaluated-expression consumers retain the
argument's value domain without a new operational semantics.\<close>


lemma lpp_evaluated_integer_comparison:
 assumes compatible: "lpp_stable_integer_operations operation"
   and left: "lpp_stable_scalar_evaluation operation a (lpp_integer_value n)"
   and right: "lpp_stable_scalar_evaluation operation b (lpp_integer_value m)"
   and compared: "lpp_integer_compare c n m"
 shows "lpp_stable_compare_outcome operation c a b (LPPBuiltinSuccess LPIVar)"
proof -
 have ground: "lp_seg_ground a" "lp_seg_ground b"
   using lpp_stable_scalar_evaluation_ground[OF left] lpp_stable_scalar_evaluation_ground[OF right] by auto
 have finite: "lpp_finite_compare_outcome c a b (LPPBuiltinSuccess LPIVar)"
 proof (cases "(\<exists>i. lpp_integer_evaluation a i) \<and> (\<exists>j. lpp_integer_evaluation b j)")
   case False then show ?thesis using ground by (auto simp: lpp_finite_compare_outcome_def)
 next
   case True
   then obtain i j where old_left: "lpp_integer_evaluation a i" and old_right: "lpp_integer_evaluation b j" by blast
   have equal: "i=n" "j=m"
     using lpp_stable_scalar_evaluation_unique[OF lpp_integer_evaluation_stable[OF compatible old_left] left]
       lpp_stable_scalar_evaluation_unique[OF lpp_integer_evaluation_stable[OF compatible old_right] right] by simp_all
   show ?thesis using compared equal
     by (simp only: lpp_finite_comparison_integer[OF old_left old_right]
       lpp_integer_compare_outcome_exact[OF old_left old_right]; simp)
 qed
 have truth: "lpp_stable_compare_values operation c a b True"
   using lpp_stable_compare_values_exact[OF left right lpp_integer_scalar_observation lpp_integer_scalar_observation, of c True] compared by simp
 show ?thesis using finite truth by (auto simp: lpp_stable_compare_outcome_def)
qed

definition lpp_value_observation where
 "lpp_value_observation t = LPPOComparison LPPIntEqual
   (Fun (LPCUser ''2:prolog_data_6d6f64'') [t,lpp_integer_term 1]) (lpp_integer_term 0)"

lemma lpp_value_observation_sound:
 assumes compatible: "lpp_stable_integer_operations operation"
   and evaluated: "lpp_stable_scalar_evaluation operation (lp_ieval t eta) (lpp_integer_value n)"
 shows "lpp_stable_observation_holds operation eta (lpp_value_observation t)"
proof -
 have step: "operation (LPCUser ''2:prolog_data_6d6f64'') [lpp_integer_value n,lpp_integer_value 1]=Some (lpp_integer_value 0)"
   using compatible by (simp add: lpp_stable_integer_operations_def)
 have modulo: "lpp_stable_scalar_evaluation operation
     (lp_ieval (Fun (LPCUser ''2:prolog_data_6d6f64'') [t,lpp_integer_term 1]) eta) (lpp_integer_value 0)"
   using evaluated step
   by (auto intro: lpp_stable_scalar_evaluation.intros lpp_stable_integer_literal lpp_integer_scalar_observation)
 have zero: "lpp_stable_scalar_evaluation operation (lp_ieval (lpp_integer_term 0) eta) (lpp_integer_value 0)"
   by (simp add: lpp_stable_integer_literal)
 show ?thesis unfolding lpp_value_observation_def lpp_stable_observation_holds.simps
   by (rule lpp_evaluated_integer_comparison[OF compatible modulo zero]) simp
qed

definition lpp_value_return_observations where
 "lpp_value_return_observations summaries ps = map lpp_value_observation
   (concat (map (lpp_value_call_terms summaries) ps))"

lemma lpp_value_return_observations_sound:
 assumes compatible: "lpp_stable_integer_operations operation"
   and checked: "lpp_check_value_program summaries P"
   and helpers: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation))
      (map (\<lambda>b. lpp_success_atom_eval b eta) ps)"
 shows "list_all (lpp_stable_observation_holds operation eta) (lpp_value_return_observations summaries ps)"
proof -
 have each: "lpp_stable_observation_holds operation eta (lpp_value_observation t)"
   if call: "b\<in>set ps" and selected: "t\<in>set (lpp_value_call_terms summaries b)" for b t
 proof -
   have actual: "lpp_guarded_success P (lpp_stable_scalar_evaluation operation) (lpp_success_atom_eval b eta)"
     using helpers call by (simp add: list_all_iff)
   have summary: "lpp_value_summaries_hold (lpp_stable_scalar_evaluation operation) summaries (lpp_success_atom_eval b eta)"
     by (rule lpp_check_value_program_sound[OF compatible checked actual])
   obtain n where evaluated: "lpp_stable_scalar_evaluation operation (lp_ieval t eta) (lpp_integer_value n)"
     using lpp_value_call_terms_sound[OF summary selected] by blast
   show ?thesis by (rule lpp_value_observation_sound[OF compatible evaluated])
 qed
 show ?thesis using each by (auto simp: lpp_value_return_observations_def list_all_iff)
qed

ML \<open>
val checked = [@{thm lpp_value_return_observations_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted actual-return value observation dependency" else ();
\<close>
end
