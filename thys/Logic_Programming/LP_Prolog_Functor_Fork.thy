theory LP_Prolog_Functor_Fork
 imports LP_Prolog_Functor_Context LP_Prolog_Evaluation_Refresh
begin

definition lpp_functor_context_short where
 "lpp_functor_context_short k observations =
  list_all (\<lambda>observation. list_all (\<lambda>t. \<forall>x\<in>vars_term t. length x<k)
    (lpp_functor_fact_terms observation)) observations"

definition lpp_functor_fork_context where
 "lpp_functor_fork_context observations k G =
  map (\<lambda>observation. lpp_functor_fact_subst observation (lp_cut_refresh k G)) observations @ observations"

text \<open>The refreshed half describes successful active execution. The
original half retains the pre-step valuation for saved alternatives. No relation
acquired by success is asserted about a resumed failure alternative.\<close>

lemma lpp_functor_context_fork_sound:
 fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes known: "list_all (lpp_functor_fact_holds names eta) observations"
 and short: "lpp_functor_context_short k observations"
 and bounds: "2 * k \<le> l"
 and ground: "\<forall>x\<in>G. lp_seg_ground (eta x)"
 shows "list_all (lpp_functor_fact_holds names (lp_cut_resolution_env k l eta sigma rho))
   (lpp_functor_fork_context observations k G)"
proof -
 have held: "lpp_functor_fact_holds names eta observation"
  and small: "\<forall>t\<in>set (lpp_functor_fact_terms observation). \<forall>x\<in>vars_term t. length x<k"
  if "observation\<in>set observations" for observation
  using known short that by (auto simp: list_all_iff lpp_functor_context_short_def)
 have refreshed: "lpp_functor_fact_holds names (lp_cut_resolution_env k l eta sigma rho)
   (lpp_functor_fact_subst observation (lp_cut_refresh k G))"
  if "observation\<in>set observations" for observation
  by (rule lpp_functor_fact_refresh_sound[OF held[OF that] small[OF that] bounds ground])
 have original: "lpp_functor_fact_holds names (lp_cut_resolution_env k l eta sigma rho) observation"
  if member: "observation\<in>set observations" for observation
 proof -
  have same: "lp_ieval t (lp_cut_resolution_env k l eta sigma rho)=lp_ieval t eta"
   if "t\<in>set (lpp_functor_fact_terms observation)" for t
   by (rule lp_cut_resolution_old)
    (use small[OF member] that bounds in auto)
  show ?thesis using lpp_functor_fact_environment_cong[OF same] held[OF member] by simp
 qed
 show ?thesis using refreshed original
  by (auto simp: lpp_functor_fork_context_def list_all_iff)
qed

lemma lpp_functor_fork_retains_original:
 "set observations\<subseteq> set (lpp_functor_fork_context observations k G)"
 by (simp add: lpp_functor_fork_context_def)

lemma lpp_functor_fork_rejects_unbounded_variable:
 "\<not> lpp_functor_context_short 1 [LPPFunctorFact (Var ''long'') (Var ''N'') (Var ''A'')]"
 by (simp add: lpp_functor_context_short_def)

ML \<open>
val checked = [@{thm lpp_functor_context_fork_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted functor context fork dependency" else ();
\<close>
end
