theory LP_Prolog_Stable_Guarded_Descent
 imports LP_Prolog_Stable_Observed_Calls LP_Prolog_Finite_Guarded_Descent
begin
hide_const (open) NthRoot.root Term.root Tree_Automata_Containment.entry

theorem lpp_stable_context_connection_descent:
  assumes checked: "lpp_check_context_connection D facts guards observations roots nd ss inp receipt"
    and invariant: "lpc_triple_instance_invariant (lpp_lift_iatom a) inp (lpc_return_eval eta ss)"
    and observed_context: "lpp_stable_context_holds operation SP (facts,guards,observations) eta"
  shows "(a,lpp_success_atom_eval (lpp_unlift_atom (lpctr_input (roots!lpctc_target receipt)))
      (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpctc_bindings receipt) x) eta))
      \<in>lpp_stable_observed_calls operation (set D) SP"
proof -
  let ?root = "roots!lpctc_target receipt"
  let ?child = "lpctr_node ?root"
  let ?mu = "lp_cut_instance_subst (lpctc_bindings receipt)"
  obtain e observed ce where ss: "ss=[(e,observed)]" and state: "lpcn_state ?child=[ce]"
    using checked by (auto simp: lpp_check_context_connection_def Let_def split: list.splits prod.splits;
      metis list.exhaust prod.exhaust)
  have head: "lpp_lift_atom (lpp_unlift_atom (lpc_triple_observation_atom observed inp))=
      lpc_triple_observation_atom observed inp"
    and call: "lpp_check_observed_call D facts guards observations
      (lpp_unlift_atom (lpc_triple_observation_atom observed inp))
      (lpp_success_atom_subst (lpp_unlift_atom (lpctr_input ?root)) ?mu)
      (lpctc_call receipt) (lpctc_call_bindings receipt)"
    using checked by (auto simp: lpp_check_context_connection_def Let_def ss state)
  obtain sigma where matching: "lp_iatom_subst (lpp_lift_iatom a) sigma=
      lp_atom_eval (lpc_triple_observation_atom observed inp) eta"
    using invariant by (auto simp: ss lpc_triple_instance_invariant_def
      lpc_return_eval_def lpc_triple_observation_atom_eval)
  have lifted_match: "lp_iatom_subst (lpp_lift_iatom a) sigma=
      lp_atom_eval (lpp_lift_atom (lpp_unlift_atom (lpc_triple_observation_atom observed inp))) eta"
    using matching arg_cong[OF head, of "\<lambda>b. lp_atom_eval b eta"] by metis
  have matching': "lpp_success_iatom_subst a sigma=
      lpp_success_atom_eval (lpp_unlift_atom (lpc_triple_observation_atom observed inp)) eta"
    using lifted_match
    by (simp add: lpp_lift_atom_def lpp_lift_iatom_def
      lp_iatom_subst_def lp_atom_eval_def lpp_success_iatom_subst_def lpp_success_atom_eval_def)
  have edge: "(a,lpp_success_atom_eval (lpp_success_atom_subst (lpp_unlift_atom (lpctr_input ?root)) ?mu) eta)
      \<in>lpp_stable_observed_calls operation (set D) SP"
    by (rule lpp_checked_stable_observed_call[OF call matching'])
      (use observed_context in \<open>auto simp: lpp_stable_context_holds_def lpp_evaluation_context_holds_def list_all_iff\<close>)
  show ?thesis using edge by (simp only: lpp_success_atom_subst_eval)
qed


theorem lpp_stable_actual_return_observed_descent:
  assumes actual: "lpp_stable_actual_return operation P ss eta"
    and invariant: "lpc_triple_instance_invariant (lpp_lift_iatom a) inp ss"
    and head: "lpp_lift_atom h=inp"
    and checked: "lpp_check_observed_call D facts guards observations h call c bindings"
    and returned_context: "lpp_stable_context_holds operation SP (facts,guards,observations) eta"
  shows "(a,lpp_success_atom_eval call eta)\<in>lpp_stable_observed_calls operation (set D) SP"
proof -
  have match: "\<exists>sigma. lp_iatom_subst (lpp_lift_iatom a) sigma=lp_atom_eval inp eta"
  proof (rule lpp_actual_return_substitution_property[OF _ actual
      invariant[unfolded lpc_triple_instance_invariant_def]])
    fix rho sigma
    assume "\<exists>tau. lp_iatom_subst (lpp_lift_iatom a) tau=lp_atom_eval inp rho"
    then obtain tau where match: "lp_iatom_subst (lpp_lift_iatom a) tau=lp_atom_eval inp rho" by blast
    have "lp_iatom_subst (lpp_lift_iatom a) (\<lambda>x. lp_isubst (tau x) sigma)=
      lp_atom_eval inp (\<lambda>x. lp_isubst (rho x) sigma)"
      using arg_cong[OF match, of "\<lambda>b. lp_iatom_subst b sigma"]
      by (simp add: lp_iatom_subst_def lp_atom_eval_def lp_seg_isubst_comp
        lp_ieval_subst map_map o_def)
    then show "\<exists>tau. lp_iatom_subst (lpp_lift_iatom a) tau=
      lp_atom_eval inp (\<lambda>x. lp_isubst (rho x) sigma)" by blast
  qed
  obtain sigma where matching: "lp_iatom_subst (lpp_lift_iatom a) sigma=lp_atom_eval (lpp_lift_atom h) eta"
    using match head by blast
  have unlifted: "lpp_success_iatom_subst a sigma=lpp_success_atom_eval h eta"
    using matching by (simp add: lpp_lift_atom_def lpp_lift_iatom_def lp_iatom_subst_def
      lp_atom_eval_def lpp_success_iatom_subst_def lpp_success_atom_eval_def)
  show ?thesis by (rule lpp_checked_stable_observed_call[OF checked unlifted])
    (use returned_context in \<open>auto simp: lpp_stable_context_holds_def lpp_evaluation_context_holds_def list_all_iff\<close>)
qed

ML \<open>
val checked = [@{thm lpp_stable_context_connection_descent}, @{thm lpp_stable_actual_return_observed_descent}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable descent dependency" else ();
\<close>
end
