theory LP_Prolog_Stable_Call_Projection
 imports LP_Prolog_Stable_Guarded_Graph LP_Prolog_Finite_Numeric_Projection
begin

lemma lpp_stable_observed_call_projection:
  assumes edge: "(a,b)\<in>lpp_stable_observed_calls operation D P"
  shows "(lpp_project_call positions a,lpp_project_call positions b)\<in>
    lpp_stable_observed_calls operation (lpp_project_observed_triple positions ` D) P"
proof -
  obtain h ps target gs observations sigma eta where
    member: "((h,ps,target,gs),observations)\<in>D"
    and matching: "lpp_success_iatom_subst a sigma=lpp_success_atom_eval h eta"
    and guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta) gs"
    and observations: "list_all (lpp_stable_observation_holds operation eta) observations"
    and facts: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation))
      (map (\<lambda>g. lpp_success_atom_eval g eta) ps)"
    and target: "b=lpp_success_atom_eval target eta"
    using edge by (auto simp: lpp_stable_observed_calls_def)
  have projected: "((lpp_project_call positions h,ps,lpp_project_call positions target,gs),observations)
      \<in>lpp_project_observed_triple positions ` D"
    using imageI[OF member, of "lpp_project_observed_triple positions"] by simp
  have match: "lpp_success_iatom_subst (lpp_project_call positions a) sigma =
      lpp_success_atom_eval (lpp_project_call positions h) eta"
    by (simp only: lpp_project_call_subst matching lpp_project_call_eval)
  show ?thesis unfolding lpp_stable_observed_calls_def
    apply (rule CollectI)
    apply (rule exI[of _ "lpp_project_call positions a"], rule exI[of _ "lpp_project_call positions h"],
      rule exI[of _ ps], rule exI[of _ "lpp_project_call positions target"],
      rule exI[of _ gs], rule exI[of _ observations], rule exI[of _ sigma], rule exI[of _ eta])
    using projected match guards observations facts target
    by (simp add: lpp_project_call_eval)
qed

theorem lpp_stable_projected_calls_SN:
  assumes sn: "SN (lpp_stable_observed_calls operation (lpp_project_observed_triple positions ` D) P :: 'w lpp_success_iatom rel)"
  shows "SN (lpp_stable_observed_calls operation D P :: 'w lpp_success_iatom rel)"
  by (rule lpp_typed_successor_simulation_SN[where T="\<lambda>_. True" and
      project="lpp_project_call positions", OF sn])
    (auto intro: lpp_stable_observed_call_projection)


ML \<open>
val checked = [@{thm lpp_stable_observed_call_projection}, @{thm lpp_stable_projected_calls_SN}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable call projection dependency" else ();
\<close>
end
