theory LP_Prolog_Stable_Structural_Components
 imports LP_Prolog_Stable_Routed_Calls
begin

text \<open>Structural children apply to finite observed arguments. Groundness
of the projected target is checked independently of termination. No finite
graph representation of a rational cycle supplies this premise.\<close>

definition lpp_check_stable_structural_row where
  "lpp_check_stable_structural_row T triple facts =
    (case triple of ((h,ps,b,gs),os) \<Rightarrow>
      lpp_check_path_types T ps gs facts \<and>
      (\<Union>t\<in>set (snd b). vars_term t) \<subseteq>
        set (map lpp_transfer_variable facts) \<union> lpp_observations_ground os)"

lemma lpp_stable_observations_ground:
  assumes observations: "list_all (lpp_stable_observation_holds operation eta) os"
    and member: "x\<in>lpp_observations_ground os"
  shows "lp_seg_ground (eta x)"
proof -
  obtain ob where ob: "ob\<in>set os" and var: "x\<in>lpp_observation_ground_vars ob"
    using member by (auto simp: lpp_observations_ground_def)
  have held: "lpp_evaluation_observation_holds (lpp_stable_scalar_evaluation operation) eta ob"
    by (rule lpp_stable_observation_refines) (use observations ob in \<open>auto simp: list_all_iff\<close>)
  have all: "\<forall>x\<in>lpp_observation_ground_vars ob. lp_seg_ground (eta x)"
    by (rule lpp_evaluation_observation_ground[OF _ held])
      (auto dest: lpp_stable_scalar_evaluation_ground)
  show ?thesis using all var by blast
qed

lemma lpp_stable_structural_row_target:
  fixes P :: "'v lpp_success_clause list" and facts :: "'v lpp_transfer_fact list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_stable_structural_row T ((h,ps,b,gs),os) facts"
    and transfer: "lpp_check_transfer_program T P receipts"
    and guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta) gs"
    and prefix: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation))
      (map (\<lambda>g. lpp_success_atom_eval g eta) ps)"
    and observations: "list_all (lpp_stable_observation_holds operation eta) os"
  shows "list_all lp_seg_ground (snd (lpp_success_atom_eval b eta))"
proof -
  have typed: "lpp_check_path_types T ps gs facts"
    and cover: "(\<Union>t\<in>set (snd b). vars_term t) \<subseteq>
      set (map lpp_transfer_variable facts) \<union> lpp_observations_ground os"
    using checked by (auto simp: lpp_check_stable_structural_row_def)
  have known: "lpp_integer_known (map lpp_transfer_variable facts) eta"
    by (rule lpp_check_path_types_sound[OF transfer typed guards prefix lpp_stable_evaluation_integer_contract[OF compatible]])
  have integers: "\<forall>x\<in>set (map lpp_transfer_variable facts). lp_seg_ground (eta x)"
    using known by (auto simp: lpp_integer_known_def lpp_integer_value_def intro: lp_seg_ground.intros)
  show ?thesis using cover integers lpp_stable_observations_ground[OF observations]
    by (auto simp: lpp_success_atom_eval_def list_all_iff lp_seg_ground_eval)
qed

theorem lpp_stable_structural_typed_component_SN:
  fixes D :: "'v lpp_observed_triple set" and P :: "'v lpp_success_clause list"
  assumes targets: "\<And>a b. (a,b)\<in>(lpp_stable_observed_calls operation D P :: 'w lpp_success_iatom rel) \<Longrightarrow> list_all lp_seg_ground (snd b)"
    and child: "\<And>a :: 'w lpp_success_iatom. list_all lp_seg_ground (snd a) \<Longrightarrow>
      SN_on (lp_triple_calls (lpp_erase_triples (fst ` D)) (lpp_erase_success P)) {lpp_lift_iatom a}"
  shows "SN (lpp_stable_observed_calls operation D P :: 'w lpp_success_iatom rel)"
  apply (rule lpp_typed_relational_simulation_SN[where
    T="\<lambda>a. list_all lp_seg_ground (snd a)" and rep="\<lambda>a s. s=lpp_lift_iatom a" and
    S="lp_triple_calls (lpp_erase_triples (fst ` D)) (lpp_erase_success P)"])
  apply (erule targets)
  apply (blast intro: child)
  by (blast dest: lpp_stable_call_structural)

ML \<open>
val checked = [@{thm lpp_stable_structural_row_target}, @{thm lpp_stable_structural_typed_component_SN}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable structural component dependency" else ();
\<close>
end
