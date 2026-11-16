theory LP_Prolog_Context_Refresh
  imports LP_Prolog_Context_Comparison
begin

fun lpp_context_guard_terms where
  "lpp_context_guard_terms (LPPSInteger t) = [t]"
| "lpp_context_guard_terms (LPPSEvaluates e t) = [e,t]"
| "lpp_context_guard_terms (LPPSOpaque t) = [t]"
| "lpp_context_guard_terms (LPPSNumeric c a b) = [a,b]"
fun lpp_context_observation_terms where
  "lpp_context_observation_terms (LPPOGround t) = [t]"
| "lpp_context_observation_terms (LPPOEquation a b) = [a,b]"
| "lpp_context_observation_terms (LPPOShape G shape t) = [t]"
| "lpp_context_observation_terms (LPPOInteger t) = [t]"
| "lpp_context_observation_terms (LPPOEvaluation e t) = [e,t]"
| "lpp_context_observation_terms (LPPOComparison c a b) = [a,b]"
fun lpp_context_terms where
  "lpp_context_terms (facts,guards,observations) =
    concat (map snd facts) @ concat (map lpp_context_guard_terms guards) @
    concat (map lpp_context_observation_terms observations)"
lemma lpp_context_runtime_subst:
  fixes eta :: "'v \<Rightarrow> (string lp_cut_symbol,'w) lp_iterm"
    and sigma :: "'w \<Rightarrow> (string lp_cut_symbol,'w) lp_iterm"
  assumes known: "lpp_source_context_holds P source_context eta"
  shows "lpp_source_context_holds P source_context (\<lambda>x. lp_isubst (eta x) sigma)"
  using known by (cases source_context)
    (auto simp: lpp_path_context_holds_def list_all_iff lpp_success_atom_eval_subst[symmetric]
      intro: lpp_guarded_success_integer_subst lpp_success_guard_integer_subst lpp_numeric_observation_subst)

lemma lpp_context_environment_cong:
  assumes same: "\<And>t. t\<in>set (lpp_context_terms source_context) \<Longrightarrow> lp_ieval t eta=lp_ieval t nu"
  shows "lpp_source_context_holds P source_context eta=lpp_source_context_holds P source_context nu"
proof -
  obtain facts guards observations where ctx: "source_context=(facts,guards,observations)"
    by (cases source_context) auto
  have atoms: "lpp_success_atom_eval a eta=lpp_success_atom_eval a nu" if "a\<in>set facts" for a
    using same that by (auto simp: ctx lpp_success_atom_eval_def intro!: map_cong)
  have tests: "lpp_success_guard_holds lpp_integer_result eta g=lpp_success_guard_holds lpp_integer_result nu g"
    if "g\<in>set guards" for g
    proof -
    have eq: "lp_ieval t eta=lp_ieval t nu" if "t\<in>set (lpp_context_guard_terms g)" for t
      by (rule same) (use that \<open>g\<in>set guards\<close> in \<open>auto simp: ctx\<close>)
    show ?thesis using eq by (cases g) auto
  qed
  have numeric: "lpp_numeric_observation_holds eta observation=lpp_numeric_observation_holds nu observation"
    if "observation\<in>set observations" for observation
    proof -
    have eq: "lp_ieval t eta=lp_ieval t nu" if "t\<in>set (lpp_context_observation_terms observation)" for t
      by (rule same) (use that \<open>observation\<in>set observations\<close> in \<open>auto simp: ctx\<close>)
    show ?thesis using eq by (cases observation) auto
  qed
  show ?thesis using atoms tests numeric by (auto simp: ctx lpp_path_context_holds_def list_all_iff)
qed

definition lpp_context_short where
  "lpp_context_short k source_context =
    list_all (\<lambda>t. \<forall>x\<in>vars_term t. length x<k) (lpp_context_terms source_context)"

lemma lpp_context_refresh_sound:
  fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes known: "lpp_source_context_holds P source_context eta"
    and short: "lpp_context_short k source_context"
    and bounds: "2 * k \<le> l"
    and ground: "\<forall>x\<in>G. lp_seg_ground (eta x)"
  shows "lpp_source_context_holds P (lpp_source_context_subst source_context (lp_cut_refresh k G))
    (lp_cut_resolution_env k l eta sigma rho)"
proof -
  have stable: "lpp_source_context_holds P source_context (\<lambda>x. lp_isubst (eta x) sigma)"
    by (rule lpp_context_runtime_subst[OF known])
  have same: "lp_ieval t (\<lambda>x. lp_ieval (lp_cut_refresh k G x) (lp_cut_resolution_env k l eta sigma rho)) =
    lp_ieval t (\<lambda>x. lp_isubst (eta x) sigma)" if member: "t\<in>set (lpp_context_terms source_context)" for t
  proof -
    have small: "\<forall>x\<in>vars_term t. length x<k"
      using short member by (auto simp: lpp_context_short_def list_all_iff)
    show ?thesis using lp_cut_resolution_active[OF small bounds ground]
      by (simp add: lp_ieval_finite_subst lp_ieval_subst)
  qed
  show ?thesis using lpp_context_environment_cong[where source_context=source_context and P=P, OF same] stable
    by (simp only: lpp_context_subst_eval)
qed

ML \<open>
val checked = [@{thm lpp_context_refresh_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted context refresh dependency" else ();
\<close>
end
