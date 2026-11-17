theory LP_Prolog_Finite_Arithmetic_Domain
 imports LP_Prolog_Finite_Variable_Head LP_Prolog_Stable_Source
begin

lemma lpp_finite_is_source_domain:
 "lpp_finite_term e \<Longrightarrow> lpp_finite_source_domain ''2:is'' [a,e]"
 by (simp add: lpp_finite_source_domain_def lpp_finite_instantiation_error_def)

lemma lpp_stable_is_finite_substitution:
 assumes success: "lpp_stable_is_outcome operation a e (LPPBuiltinSuccess mu)"
   and finite: "lpp_finite_term t"
 shows "lpp_finite_term (lp_isubst t mu)"
proof -
 obtain f where chosen: "lpp_scalar_unifier a f=Some mu"
   using success by (auto simp: lpp_stable_is_outcome_def split: option.splits)
 show ?thesis by (rule lpp_scalar_unifier_preserves_finite[OF chosen finite])
qed

lemma lpp_stable_evaluation_arity:
 "lpp_stable_scalar_evaluation operation (LPIFun f ts) v \<Longrightarrow> length ts\<le>2"
 by (erule lpp_stable_scalar_evaluation.cases)
   (auto dest: lpp_scalar_fraction_nullary)

lemma lpp_stable_is_large_arity_error:
 assumes arity: "2<length ts"
   and outcome: "lpp_stable_is_outcome operation a (LPIFun f ts) result"
 shows "result=LPPBuiltinError"
 using outcome arity
 by (auto simp: lpp_stable_is_outcome_def dest: lpp_stable_evaluation_arity)

ML \<open>
val checked = [@{thm lpp_finite_is_source_domain}, @{thm lpp_stable_is_finite_substitution},
 @{thm lpp_stable_is_large_arity_error}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite arithmetic domain" else ();
\<close>
end
