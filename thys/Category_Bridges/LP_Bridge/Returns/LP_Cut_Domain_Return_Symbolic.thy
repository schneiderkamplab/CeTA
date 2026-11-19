theory LP_Cut_Domain_Return_Symbolic
  imports LP_Cut_Domain_Return_Scopes
begin

context cut_runtime_domain
begin

lemma precise_return_admin_sound:
  "lpc_return_admin ss = Some (event, tt) \<Longrightarrow>
    precise_answer_transition P ss event tt"
  by (induct ss rule: lpc_return_admin.induct)
    (auto intro: precise_answer_transition.intros)

lemma precise_return_admin_unique:
  assumes checked: "lpc_return_admin ss = Some (event, tt)"
    and step: "precise_answer_transition P ss event' tt'"
  shows "event' = event \<and> tt' = tt"
  using step checked
  by (cases rule: precise_answer_transition.cases) auto

corollary precise_return_admin_symbolic_sound:
  assumes "lpc_return_admin ss = Some (event, tt)"
  shows "precise_answer_transition P
    (map (map_prod (lp_cut_entry_map f) g) ss) (map_option g event)
    (map (map_prod (lp_cut_entry_map f) g) tt)"
  by (rule precise_return_admin_sound)
    (simp add: lpc_return_admin_map assms)

corollary precise_resolution_return_values:
  assumes resolve: "lp_cut_check_resolution P fuel k l G A guards a gs c m es next anchors"
    and known: "knowledge (set G) guards eta"
    and unifier: "lp_isubst (lp_ieval a eta) sigma = lp_ieval (fst (P!c)) rho"
    and payload: "lpc_check_return_values fuel k G
      (lp_cut_resolution_equations k l G a (fst (P!c))) active saved result"
  shows "map (\<lambda>t. lp_ieval t (lp_cut_resolution_env k l eta sigma rho)) result =
      map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma) active"
    and "map (\<lambda>t. lp_ieval t (lp_cut_resolution_env k l eta sigma rho)) saved =
      map (\<lambda>t. lp_ieval t eta) saved"
  using lpc_checked_return_values[OF payload _ _
    resolution_equations[OF resolve known unifier]] resolve known
  by (auto simp: lp_cut_check_resolution_def knowledge_def)

corollary precise_unification_return_values:
  assumes unify: "lp_cut_check_unify fuel k l G guards a b gs es next"
    and known: "knowledge (set G) guards eta"
    and unifier: "lp_isubst (lp_ieval a eta) sigma = lp_isubst (lp_ieval b eta) sigma"
    and payload: "lpc_check_return_values fuel k G
      [(a\<cdot>lp_cut_refresh k (set G),b\<cdot>lp_cut_refresh k (set G))] active saved result"
  shows "map (\<lambda>t. lp_ieval t (lp_cut_resolution_env k l eta sigma eta)) result =
      map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma) active"
    and "map (\<lambda>t. lp_ieval t (lp_cut_resolution_env k l eta sigma eta)) saved =
      map (\<lambda>t. lp_ieval t eta) saved"
  using lpc_checked_return_values[OF payload _ _
    unify_equations[OF unify known unifier]] unify known
  by (auto simp: lp_cut_check_unify_def knowledge_def)

lemma precise_return_eval_admin_sound:
  "lpc_return_admin ss = Some (event,tt) \<Longrightarrow>
    precise_answer_transition P (lpc_return_eval eta ss)
      (map_option (\<lambda>ts. lpc_return_env ts eta) event) (lpc_return_eval eta tt)"
  by (rule precise_return_admin_sound) (simp add: lpc_return_eval_admin)


lemma precise_return_env_domain:
  assumes domain: "\<And>x. D (eta x)"
  shows "D (lpc_return_env ts eta n)"
  using domain by (auto simp: lpc_return_env_def intro: valuation_domain constructors)

end
end
