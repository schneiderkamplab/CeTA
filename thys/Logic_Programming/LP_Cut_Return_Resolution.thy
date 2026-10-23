theory LP_Cut_Return_Resolution
  imports LP_Cut_Return_Admin LP_Cut_Equality_Bridge
begin

text \<open>Answer interfaces use the very same source equations as the active
continuation. Saved answers remain in the old namespace. No concrete solver
substitution is trusted: the equations must cover every source unifier.\<close>

definition lpc_check_return_values where
  "lpc_check_return_values fuel k G eqs active saved result =
    ((\<forall>t\<in>set (active@saved). \<forall>x\<in>vars_term t. length x<k) \<and>
     lp_cut_normalize fuel eqs
       (map LPCAtom (map (\<lambda>t. t\<cdot>lp_cut_refresh k (set G)) active)) =
       Some (Some (map LPCAtom result)))"

lemma lpc_checked_return_values:
  assumes checked: "lpc_check_return_values fuel k G eqs active saved result"
    and bounds: "2 * k \<le> l"
    and ground: "\<forall>x\<in>set G. lp_seg_ground (eta x)"
    and equations: "lp_equations eqs (lp_cut_resolution_env k l eta sigma rho)"
  shows "map (\<lambda>t. lp_ieval t (lp_cut_resolution_env k l eta sigma rho)) result =
      map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma) active"
    and "map (\<lambda>t. lp_ieval t (lp_cut_resolution_env k l eta sigma rho)) saved =
      map (\<lambda>t. lp_ieval t eta) saved"
proof -
  have short: "\<forall>t\<in>set (active@saved). \<forall>x\<in>vars_term t. length x<k"
    and normalized: "lp_cut_normalize fuel eqs
      (map LPCAtom (map (\<lambda>t. t\<cdot>lp_cut_refresh k (set G)) active)) =
      Some (Some (map LPCAtom result))"
    using checked by (auto simp: lpc_check_return_values_def)
  have evaluated: "map (\<lambda>t. lp_ieval t (lp_cut_resolution_env k l eta sigma rho)) result =
    map (\<lambda>t. lp_ieval (t\<cdot>lp_cut_refresh k (set G))
      (lp_cut_resolution_env k l eta sigma rho)) active"
    using lp_cut_normalized_terms[OF equations normalized]
    by (simp add: map_map o_def)
  show "map (\<lambda>t. lp_ieval t (lp_cut_resolution_env k l eta sigma rho)) result =
      map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma) active"
    unfolding evaluated by (rule map_cong[OF refl], rule lp_cut_resolution_active[OF _ bounds ground])
      (use short in auto)
  have kl: "k\<le>l" using bounds by arith
  show "map (\<lambda>t. lp_ieval t (lp_cut_resolution_env k l eta sigma rho)) saved =
      map (\<lambda>t. lp_ieval t eta) saved"
    by (rule map_cong[OF refl], rule lp_cut_resolution_old[OF _ kl])
      (use short in auto)
qed

corollary lpc_resolution_return_values:
  assumes resolve: "lp_cut_check_resolution P fuel k l G A guards a gs c m es next anchors"
    and known: "lp_cut_knowledge (set G) guards eta"
    and unifier: "lp_isubst (lp_ieval a eta) sigma = lp_ieval (fst (P!c)) rho"
    and payload: "lpc_check_return_values fuel k G
      (lp_cut_resolution_equations k l G a (fst (P!c))) active saved result"
  shows "map (\<lambda>t. lp_ieval t (lp_cut_resolution_env k l eta sigma rho)) result =
      map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma) active"
    and "map (\<lambda>t. lp_ieval t (lp_cut_resolution_env k l eta sigma rho)) saved =
      map (\<lambda>t. lp_ieval t eta) saved"
  using lpc_checked_return_values[OF payload _ _
    lp_cut_checked_resolution_equations[OF resolve known unifier]] resolve known
  by (auto simp: lp_cut_check_resolution_def lp_cut_knowledge_def)

corollary lpc_unification_return_values:
  assumes unify: "lp_cut_check_unify fuel k l G guards a b gs es next"
    and known: "lp_cut_knowledge (set G) guards eta"
    and unifier: "lp_isubst (lp_ieval a eta) sigma = lp_isubst (lp_ieval b eta) sigma"
    and payload: "lpc_check_return_values fuel k G
      [(a\<cdot>lp_cut_refresh k (set G),b\<cdot>lp_cut_refresh k (set G))] active saved result"
  shows "map (\<lambda>t. lp_ieval t (lp_cut_resolution_env k l eta sigma eta)) result =
      map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma) active"
    and "map (\<lambda>t. lp_ieval t (lp_cut_resolution_env k l eta sigma eta)) saved =
      map (\<lambda>t. lp_ieval t eta) saved"
  using lpc_checked_return_values[OF payload _ _
    lp_cut_checked_unify_equations[OF unify known unifier]] unify known
  by (auto simp: lp_cut_check_unify_def lp_cut_knowledge_def)

end
