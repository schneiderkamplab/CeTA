theory LP_Prolog_Functor_Context
 imports LP_Prolog_Univ_Decomposition LP_Prolog_Context_Refresh
begin

text \<open>Functor facts are explicit three-term relations in one source frame.
Their transport uses the same runtime substitutions and resolution environment
as the existing source contexts. A saved alternative needs its own facts; these
lemmas do not copy successful observations onto a resumed alternative.\<close>

datatype 'v lpp_functor_fact = LPPFunctorFact
 "(string lp_cut_symbol,'v) term" "(string lp_cut_symbol,'v) term"
 "(string lp_cut_symbol,'v) term"

fun lpp_functor_fact_holds where
 "lpp_functor_fact_holds names eta (LPPFunctorFact value name_term arglist) =
  lpp_functor_observation names (lp_ieval value eta) (lp_ieval name_term eta) (lp_ieval arglist eta)"

fun lpp_functor_fact_subst where
 "lpp_functor_fact_subst (LPPFunctorFact value name_term arglist) mu =
  LPPFunctorFact (value\<cdot>mu) (name_term\<cdot>mu) (arglist\<cdot>mu)"

fun lpp_functor_fact_terms where
 "lpp_functor_fact_terms (LPPFunctorFact value name_term arglist) = [value,name_term,arglist]"

lemma lpp_functor_fact_subst_eval:
 "lpp_functor_fact_holds names eta (lpp_functor_fact_subst observation mu) =
  lpp_functor_fact_holds names (\<lambda>x. lp_ieval (mu x) eta) observation"
 by (cases observation) (simp add: lp_ieval_finite_subst)

lemma lpp_functor_fact_runtime_subst:
 "lpp_functor_fact_holds names eta observation \<Longrightarrow>
  lpp_functor_fact_holds names (\<lambda>x. lp_isubst (eta x) sigma) observation"
 by (cases observation) (auto simp: lp_ieval_subst[symmetric] intro: lpp_functor_observation_subst)

lemma lpp_functor_fact_environment_cong:
 "(\<And>t. t\<in>set (lpp_functor_fact_terms observation) \<Longrightarrow> lp_ieval t eta=lp_ieval t nu) \<Longrightarrow>
  lpp_functor_fact_holds names eta observation = lpp_functor_fact_holds names nu observation"
 by (cases observation) auto

definition lpp_check_functor_transport where
 "lpp_check_functor_transport source_facts target_facts bindings =
  list_all (\<lambda>observation. lpp_functor_fact_subst observation bindings\<in>set source_facts) target_facts"

lemma lpp_check_functor_transport_sound:
 assumes checked: "lpp_check_functor_transport source_facts target_facts bindings"
 and held: "list_all (lpp_functor_fact_holds names eta) source_facts"
 shows "list_all (lpp_functor_fact_holds names (\<lambda>x. lp_ieval (bindings x) eta)) target_facts"
 using checked held
 by (auto simp: lpp_check_functor_transport_def list_all_iff lpp_functor_fact_subst_eval[symmetric])

lemma lpp_functor_fact_refresh_sound:
 fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes held: "lpp_functor_fact_holds names eta observation"
 and short: "\<forall>t\<in>set (lpp_functor_fact_terms observation). \<forall>x\<in>vars_term t. length x<k"
 and bounds: "2 * k \<le> l"
 and ground: "\<forall>x\<in>G. lp_seg_ground (eta x)"
 shows "lpp_functor_fact_holds names (lp_cut_resolution_env k l eta sigma rho)
   (lpp_functor_fact_subst observation (lp_cut_refresh k G))"
proof -
 have stable: "lpp_functor_fact_holds names (\<lambda>x. lp_isubst (eta x) sigma) observation"
  by (rule lpp_functor_fact_runtime_subst[OF held])
 have same: "lp_ieval t (\<lambda>x. lp_ieval (lp_cut_refresh k G x) (lp_cut_resolution_env k l eta sigma rho)) =
   lp_ieval t (\<lambda>x. lp_isubst (eta x) sigma)" if "t\<in>set (lpp_functor_fact_terms observation)" for t
 proof -
  have small: "\<forall>x\<in>vars_term t. length x<k" using short that by blast
  show ?thesis using lp_cut_resolution_active[OF small bounds ground]
   by (simp add: lp_ieval_finite_subst lp_ieval_subst)
 qed
 show ?thesis using lpp_functor_fact_environment_cong[OF same] stable
  by (simp only: lpp_functor_fact_subst_eval)
qed

lemma lpp_univ_acquires_functor_fact:
 assumes outcome: "lpp_univ_view_outcome names (lp_ieval value eta)
   (LPIFun (LPCUser ''2:prolog_data_2e'') [lp_ieval name_term eta,lp_ieval arglist eta])
   (LPPBuiltinSuccess mu)"
 and held: "list_all (lpp_functor_fact_holds names eta) previous"
 shows "list_all (lpp_functor_fact_holds names (\<lambda>x. lp_isubst (eta x) mu))
   (LPPFunctorFact value name_term arglist # previous)"
 using lpp_univ_view_success_observation[OF outcome] held
 by (auto simp: list_all_iff lp_ieval_subst[symmetric] intro: lpp_functor_fact_runtime_subst)

lemma lpp_functor_transport_identity:
 "lpp_check_functor_transport [LPPFunctorFact value name_term arglist]
    [LPPFunctorFact value name_term arglist] Var"
 by (simp add: lpp_check_functor_transport_def)

lemma lpp_functor_transport_changed_arguments_rejected:
 "\<not> lpp_check_functor_transport [LPPFunctorFact (Var ''V'') (Var ''N'') (Var ''A'')]
    [LPPFunctorFact (Var ''V'') (Var ''N'') (Var ''B'')] Var"
 by (simp add: lpp_check_functor_transport_def)

lemma lpp_functor_transport_changed_name_rejected:
 "\<not> lpp_check_functor_transport [LPPFunctorFact (Var ''V'') (Var ''N'') (Var ''A'')]
    [LPPFunctorFact (Var ''V'') (Var ''M'') (Var ''A'')] Var"
 by (simp add: lpp_check_functor_transport_def)

lemma lpp_functor_transport_missing_fact_rejected:
 "\<not> lpp_check_functor_transport [] [observation] bindings"
 by (simp add: lpp_check_functor_transport_def)

ML \<open>
val checked = [@{thm lpp_univ_acquires_functor_fact}, @{thm lpp_functor_fact_refresh_sound}, @{thm lpp_check_functor_transport_sound},
 @{thm lpp_functor_fact_runtime_subst}, @{thm lpp_functor_fact_environment_cong}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted functor context transport dependency" else ();
\<close>
end
