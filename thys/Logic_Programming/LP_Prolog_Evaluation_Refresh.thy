theory LP_Prolog_Evaluation_Refresh
  imports LP_Prolog_Evaluation_Link LP_Prolog_Context_Refresh
begin

lemma lpp_evaluation_context_runtime_subst:
  fixes eta :: "'v \<Rightarrow> (string lp_cut_symbol,'w) lp_iterm"
    and sigma :: "'w \<Rightarrow> (string lp_cut_symbol,'w) lp_iterm"
  assumes stable_evaluation: "\<And>e t sigma. E e t \<Longrightarrow> E (lp_isubst e sigma) (lp_isubst t sigma)"
    and known: "lpp_evaluation_context_holds E P source_context eta"
  shows "lpp_evaluation_context_holds E P source_context (\<lambda>x. lp_isubst (eta x) sigma)"
  using known by (cases source_context)
    (auto simp: lpp_evaluation_context_holds_def list_all_iff lpp_success_atom_eval_subst[symmetric]
      intro: lpp_guarded_success_evaluation_subst[where E=E, OF stable_evaluation]
        lpp_success_guard_evaluation_subst[where E=E, OF stable_evaluation]
        lpp_evaluation_observation_subst[where E=E, OF stable_evaluation])

lemma lpp_evaluation_context_environment_cong:
  assumes same: "\<And>t. t\<in>set (lpp_context_terms source_context) \<Longrightarrow> lp_ieval t eta=lp_ieval t nu"
  shows "lpp_evaluation_context_holds E P source_context eta=lpp_evaluation_context_holds E P source_context nu"
proof -
  obtain facts guards observations where ctx: "source_context=(facts,guards,observations)"
    by (cases source_context) auto
  have atoms: "lpp_success_atom_eval a eta=lpp_success_atom_eval a nu" if "a\<in>set facts" for a
    using same that by (auto simp: ctx lpp_success_atom_eval_def intro!: map_cong)
  have tests: "lpp_success_guard_holds E eta g=lpp_success_guard_holds E nu g"
    if "g\<in>set guards" for g
    proof -
    have eq: "lp_ieval t eta=lp_ieval t nu" if "t\<in>set (lpp_context_guard_terms g)" for t
      by (rule same) (use that \<open>g\<in>set guards\<close> in \<open>auto simp: ctx\<close>)
    show ?thesis using eq by (cases g) auto
  qed
  have numeric: "lpp_evaluation_observation_holds E eta observation=lpp_evaluation_observation_holds E nu observation"
    if "observation\<in>set observations" for observation
    proof -
    have eq: "lp_ieval t eta=lp_ieval t nu" if "t\<in>set (lpp_context_observation_terms observation)" for t
      by (rule same) (use that \<open>observation\<in>set observations\<close> in \<open>auto simp: ctx\<close>)
    show ?thesis using eq by (cases observation) auto
  qed
  show ?thesis using atoms tests numeric by (auto simp: ctx lpp_evaluation_context_holds_def list_all_iff)
qed

lemma lpp_evaluation_context_refresh_sound:
  fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes stable_evaluation: "\<And>e t sigma. E e t \<Longrightarrow> E (lp_isubst e sigma) (lp_isubst t sigma)"
    and known: "lpp_evaluation_context_holds E P source_context eta"
    and short: "lpp_context_short k source_context"
    and bounds: "2 * k \<le> l"
    and ground: "\<forall>x\<in>G. lp_seg_ground (eta x)"
  shows "lpp_evaluation_context_holds E P (lpp_source_context_subst source_context (lp_cut_refresh k G))
    (lp_cut_resolution_env k l eta sigma rho)"
proof -
  have stable: "lpp_evaluation_context_holds E P source_context (\<lambda>x. lp_isubst (eta x) sigma)"
    by (rule lpp_evaluation_context_runtime_subst[OF stable_evaluation known])
  have same: "lp_ieval t (\<lambda>x. lp_ieval (lp_cut_refresh k G x) (lp_cut_resolution_env k l eta sigma rho)) =
    lp_ieval t (\<lambda>x. lp_isubst (eta x) sigma)" if member: "t\<in>set (lpp_context_terms source_context)" for t
  proof -
    have small: "\<forall>x\<in>vars_term t. length x<k"
      using short member by (auto simp: lpp_context_short_def list_all_iff)
    show ?thesis using lp_cut_resolution_active[OF small bounds ground]
      by (simp add: lp_ieval_finite_subst lp_ieval_subst)
  qed
  show ?thesis using lpp_evaluation_context_environment_cong[where source_context=source_context and P=P, OF same] stable
    by (simp only: lpp_evaluation_context_substitute)
qed

fun lpp_join_source_context where
  "lpp_join_source_context (facts,guards,observations) (other_facts,other_guards,other_observations) =
    (facts@other_facts,guards@other_guards,observations@other_observations)"

lemma lpp_evaluation_join_context:
  "lpp_evaluation_context_holds E P (lpp_join_source_context a b) eta =
    (lpp_evaluation_context_holds E P a eta \<and> lpp_evaluation_context_holds E P b eta)"
  by (cases a; cases b) (auto simp: lpp_evaluation_context_holds_def)

definition lpp_evaluation_fork_context where
  "lpp_evaluation_fork_context source_context k G =
    lpp_join_source_context
      (lpp_source_context_subst source_context (lp_cut_refresh k G)) source_context"

lemma lpp_evaluation_context_fork_sound:
  fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes stable: "\<And>e t sigma. E e t \<Longrightarrow> E (lp_isubst e sigma) (lp_isubst t sigma)"
    and known: "lpp_evaluation_context_holds E P source_context eta"
    and short: "lpp_context_short k source_context"
    and bounds: "2 * k \<le> l"
    and ground: "\<forall>x\<in>G. lp_seg_ground (eta x)"
  shows "lpp_evaluation_context_holds E P (lpp_evaluation_fork_context source_context k G)
    (lp_cut_resolution_env k l eta sigma rho)"
proof -
  have old: "lp_ieval t (lp_cut_resolution_env k l eta sigma rho)=lp_ieval t eta"
    if "t\<in>set (lpp_context_terms source_context)" for t
    by (rule lp_cut_resolution_old)
      (use short that bounds in \<open>auto simp: lpp_context_short_def list_all_iff\<close>)
  have original: "lpp_evaluation_context_holds E P source_context (lp_cut_resolution_env k l eta sigma rho)"
    using known lpp_evaluation_context_environment_cong[where source_context=source_context and E=E and P=P, OF old]
    by simp
  have refreshed: "lpp_evaluation_context_holds E P
    (lpp_source_context_subst source_context (lp_cut_refresh k G)) (lp_cut_resolution_env k l eta sigma rho)"
    by (rule lpp_evaluation_context_refresh_sound[OF stable known short bounds ground])
  show ?thesis using original refreshed
    by (simp add: lpp_evaluation_fork_context_def lpp_evaluation_join_context)
qed

lemma lpp_evaluation_context_fresh_eval:
  "lpp_context_fresh x source_context \<Longrightarrow>
    lpp_evaluation_context_holds E P source_context (eta(x:=v))=lpp_evaluation_context_holds E P source_context eta"
  by (rule lpp_evaluation_context_environment_cong) (auto simp: lpp_context_fresh_def intro: lpp_fresh_term_eval)

lemma lpp_add_evaluation_context_holds:
  "lpp_evaluation_context_holds E P source_context eta \<Longrightarrow> E (lp_ieval e eta) (lp_ieval t eta) \<Longrightarrow>
    lpp_evaluation_context_holds E P (lpp_add_evaluation_observation e t source_context) eta"
  by (cases source_context) (auto simp: lpp_evaluation_context_holds_def)

ML \<open>
val checked = [@{thm lpp_evaluation_context_fork_sound}, @{thm lpp_evaluation_context_refresh_sound}, @{thm lpp_evaluation_context_fresh_eval}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted evaluation-context refresh dependency" else ();
\<close>
end
