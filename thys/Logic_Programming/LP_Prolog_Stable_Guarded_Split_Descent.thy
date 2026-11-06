theory LP_Prolog_Stable_Guarded_Split_Descent
 imports LP_Prolog_Stable_Guarded_Region_Descent LP_Prolog_Finite_Guarded_Split_Descent
begin
hide_const (open) NthRoot.root Term.root Tree_Automata_Containment.entry

theorem lpp_stable_guarded_split_first_descent:
  assumes checked: "lpp_check_finite_guarded_split_descent D incoming outgoing entry receipt first_call second_call"
    and observed: "lpp_stable_context_holds operation SP incoming eta"
  shows "(lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_first_in receipt) eta)
    \<in>inv_image (lpp_stable_observed_calls operation (set D) SP) lpp_unlift_atom"
proof -
  obtain facts guards observations where incoming: "incoming=(facts,guards,observations)"
    by (cases incoming) auto
  have call: "lpp_check_observed_call D facts guards observations
      (lpp_unlift_atom (lpctr_input entry)) (lpp_unlift_atom (lpcts_first_in receipt))
      (fst first_call) (snd first_call)"
    using checked by (simp add: lpp_check_finite_guarded_split_descent_def incoming)
  have matching: "lpp_success_iatom_subst (lpp_success_atom_eval (lpp_unlift_atom (lpctr_input entry)) eta) LPIVar =
      lpp_success_atom_eval (lpp_unlift_atom (lpctr_input entry)) eta"
    by (simp add: lpp_success_iatom_subst_def)
  have edge: "(lpp_success_atom_eval (lpp_unlift_atom (lpctr_input entry)) eta,
      lpp_success_atom_eval (lpp_unlift_atom (lpcts_first_in receipt)) eta)
      \<in>lpp_stable_observed_calls operation (set D) SP"
    by (rule lpp_checked_stable_observed_call[OF call matching])
      (use observed in \<open>auto simp: incoming lpp_stable_context_holds_def lpp_evaluation_context_holds_def list_all_iff\<close>)
  show ?thesis using edge by (simp add: inv_image_def lpp_unlift_atom_eval)
qed

theorem lpp_stable_guarded_split_return_descent:
  assumes checked: "lpp_check_finite_guarded_split_descent D incoming outgoing entry receipt first_call second_call"
    and actual: "lpp_stable_actual_return operation P
      (lpc_return_eval eta [(LPCGoals (lpcts_pre receipt),map Var (lpcn_vars (lpctr_node entry)))]) rho"
    and returned: "rho=lpc_return_env (map Var (lpcn_vars (lpctr_node entry))) theta"
    and observed: "lpp_stable_context_holds operation SP outgoing theta"
  shows "(lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_second_in receipt) theta)
    \<in>inv_image (lpp_stable_observed_calls operation (set D) SP) lpp_unlift_atom"
proof -
  let ?vs = "lpcn_vars (lpctr_node entry)"
  let ?a = "lp_atom_eval (lpctr_input entry) eta"
  let ?inp = "lpc_triple_position_atom ?vs (lpctr_input entry)"
  let ?ss = "lpc_return_eval eta [(LPCGoals (lpcts_pre receipt),map Var ?vs)]"
  obtain facts guards observations where outgoing: "outgoing=(facts,guards,observations)"
    by (cases outgoing) auto
  have distinct: "distinct ?vs" and variables: "set (lp_atom_vars (lpctr_input entry)) \<subseteq> set ?vs"
    and user: "lpp_lift_atom (lpp_unlift_atom (lpctr_input entry))=lpctr_input entry"
    and call: "lpp_check_observed_call D facts guards observations
      (lpp_unlift_atom (lpctr_input entry)) (lpp_unlift_atom (lpcts_second_in receipt))
      (fst second_call) (snd second_call)"
    using checked by (auto simp: lpp_check_finite_guarded_split_descent_def outgoing)
  have equal: "lp_atom_eval ?inp (lpc_return_env (map Var ?vs) eta)=?a"
    by (rule lpc_triple_position_atom_eval[OF distinct variables])
  have invariant: "lpc_triple_instance_invariant ?a ?inp ?ss"
    unfolding lpc_triple_instance_invariant_def lpc_return_eval_def
    by (auto simp: equal intro!: exI[of _ LPIVar])
  have match: "\<exists>sigma. lp_iatom_subst ?a sigma=lp_atom_eval ?inp rho"
  proof (rule lpp_actual_return_substitution_property[OF _ actual
      invariant[unfolded lpc_triple_instance_invariant_def]])
    fix env sigma
    assume "\<exists>tau. lp_iatom_subst ?a tau=lp_atom_eval ?inp env"
    then obtain tau where match: "lp_iatom_subst ?a tau=lp_atom_eval ?inp env" by blast
    have "lp_iatom_subst ?a (\<lambda>x. lp_isubst (tau x) sigma)=
      lp_atom_eval ?inp (\<lambda>x. lp_isubst (env x) sigma)"
      using arg_cong[OF match, of "\<lambda>b. lp_iatom_subst b sigma"]
      by (simp add: lp_iatom_subst_def lp_atom_eval_def lp_seg_isubst_comp
        lp_ieval_subst map_map o_def)
    then show "\<exists>tau. lp_iatom_subst ?a tau=lp_atom_eval ?inp (\<lambda>x. lp_isubst (env x) sigma)" by blast
  qed
  have at_return: "lp_atom_eval ?inp rho=lp_atom_eval (lpctr_input entry) theta"
    using lpc_triple_position_atom_eval[OF distinct variables, of theta] by (simp only: returned)
  obtain sigma where matching: "lp_iatom_subst ?a sigma=lp_atom_eval (lpctr_input entry) theta"
    using match by (auto simp only: at_return)
  have lifted: "lp_iatom_subst (lp_atom_eval (lpp_lift_atom (lpp_unlift_atom (lpctr_input entry))) eta) sigma=
      lp_atom_eval (lpp_lift_atom (lpp_unlift_atom (lpctr_input entry))) theta"
    using matching by (simp only: user)
  have unlifted: "lpp_success_iatom_subst (lpp_success_atom_eval (lpp_unlift_atom (lpctr_input entry)) eta) sigma=
      lpp_success_atom_eval (lpp_unlift_atom (lpctr_input entry)) theta"
    using lifted by (simp add: lpp_lift_atom_def lp_iatom_subst_def lp_atom_eval_def
      lpp_success_iatom_subst_def lpp_success_atom_eval_def)
  have edge: "(lpp_success_atom_eval (lpp_unlift_atom (lpctr_input entry)) eta,
      lpp_success_atom_eval (lpp_unlift_atom (lpcts_second_in receipt)) theta)
      \<in>lpp_stable_observed_calls operation (set D) SP"
    by (rule lpp_checked_stable_observed_call[OF call unlifted])
      (use observed in \<open>auto simp: outgoing lpp_stable_context_holds_def lpp_evaluation_context_holds_def list_all_iff\<close>)
  show ?thesis using edge by (simp add: inv_image_def lpp_unlift_atom_eval)
qed

ML \<open>
val checked = [@{thm lpp_stable_guarded_split_first_descent}, @{thm lpp_stable_guarded_split_return_descent}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable descent dependency" else ();
\<close>
end
