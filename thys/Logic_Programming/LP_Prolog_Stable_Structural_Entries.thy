theory LP_Prolog_Stable_Structural_Entries
 imports LP_Prolog_Stable_Structural_Components LP_Dependency_Triple_Observed_Roles
begin

definition lpp_check_stable_structural_selected_row where
  "lpp_check_stable_structural_selected_row T triple positions facts =
    (case triple of ((h,ps,b,gs),os) \<Rightarrow>
      lpp_check_path_types T ps gs facts \<and>
      set positions \<subseteq> {0..<length (snd b)} \<and>
      (\<Union>i\<in>set positions. vars_term (snd b!i)) \<subseteq>
        set (map lpp_transfer_variable facts) \<union> lpp_observations_ground os)"

lemma lpp_stable_structural_selected_target:
  fixes P :: "'v lpp_success_clause list" and facts :: "'v lpp_transfer_fact list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_stable_structural_selected_row T ((h,ps,b,gs),os) positions facts"
    and transfer: "lpp_check_transfer_program T P receipts"
    and guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta) gs"
    and prefix: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation))
      (map (\<lambda>g. lpp_success_atom_eval g eta) ps)"
    and observations: "list_all (lpp_stable_observation_holds operation eta) os"
  shows "\<forall>i\<in>set positions. i<length (snd b) \<and> lp_seg_ground (snd (lpp_success_atom_eval b eta)!i)"
proof -
  have typed: "lpp_check_path_types T ps gs facts"
    and cover: "(\<Union>i\<in>set positions. vars_term (snd b!i)) \<subseteq>
      set (map lpp_transfer_variable facts) \<union> lpp_observations_ground os"
    using checked by (auto simp: lpp_check_stable_structural_selected_row_def)
  have bounds: "set positions \<subseteq> {0..<length (snd b)}"
    using checked by (auto simp: lpp_check_stable_structural_selected_row_def)
  have known: "lpp_integer_known (map lpp_transfer_variable facts) eta"
    by (rule lpp_check_path_types_sound[OF transfer typed guards prefix lpp_stable_evaluation_integer_contract[OF compatible]])
  have integers: "\<forall>x\<in>set (map lpp_transfer_variable facts). lp_seg_ground (eta x)"
    using known by (auto simp: lpp_integer_known_def lpp_integer_value_def intro: lp_seg_ground.intros)
  show ?thesis
  proof (intro ballI conjI)
    fix i assume member: "i\<in>set positions"
    show "i<length (snd b)" using bounds member by auto
    have bound: "i<length (snd b)" using bounds member by auto
    have variables: "\<forall>x\<in>vars_term (snd b!i). lp_seg_ground (eta x)"
      using cover member integers lpp_stable_observations_ground[OF observations] by blast
    show "lp_seg_ground (snd (lpp_success_atom_eval b eta)!i)"
      using variables bound by (simp add: lpp_success_atom_eval_def lp_seg_ground_eval)
  qed
qed

definition lpp_structural_entry_admissible where
  "lpp_structural_entry_admissible entries a =
    (\<exists>q n positions. (q,n,positions)\<in>set entries \<and> fst a=q \<and> length (snd a)=n \<and>
      (\<forall>i\<in>set positions. i<n \<and> lp_seg_ground (snd a!i)))"

theorem lpp_stable_structural_entries_SN:
  fixes D :: "'v lpp_observed_triple set" and P :: "'v lpp_success_clause list"
  assumes targets: "\<And>a b. (a,b)\<in>(lpp_stable_observed_calls operation D P :: 'w lpp_success_iatom rel) \<Longrightarrow>
      lpp_structural_entry_admissible entries b"
    and children: "\<And>q n positions ts. (q,n,positions)\<in>set entries \<Longrightarrow> length (ts :: (string lp_cut_symbol,'w) lp_iterm list)=n \<Longrightarrow>
      (\<And>i. i\<in>set positions \<Longrightarrow> i<n \<Longrightarrow> lp_seg_ground (ts!i)) \<Longrightarrow>
      SN_on (lp_triple_calls (lpp_erase_triples (fst ` D)) (lpp_erase_success P)) {lpp_lift_iatom (q,ts)}"
  shows "SN (lpp_stable_observed_calls operation D P :: 'w lpp_success_iatom rel)"
proof -
  have child: "SN_on (lp_triple_calls (lpp_erase_triples (fst ` D)) (lpp_erase_success P)) {lpp_lift_iatom a}"
    if admissible: "lpp_structural_entry_admissible entries a" for a :: "'w lpp_success_iatom"
  proof -
    obtain q n positions where member: "(q,n,positions)\<in>set entries"
      and name: "fst a=q" and len: "length (snd a)=n"
      and ground: "\<forall>i\<in>set positions. i<n \<and> lp_seg_ground (snd a!i)"
      using admissible by (auto simp: lpp_structural_entry_admissible_def)
    have result: "SN_on (lp_triple_calls (lpp_erase_triples (fst ` D)) (lpp_erase_success P))
        {lpp_lift_iatom (q,snd a)}"
      by (rule children[OF member len]) (use ground in blast)
    show ?thesis using result by (simp only: name[symmetric] prod.collapse)
  qed
  show ?thesis
    apply (rule lpp_typed_relational_simulation_SN[where
      T="lpp_structural_entry_admissible entries" and rep="\<lambda>a s. s=lpp_lift_iatom a" and
      S="lp_triple_calls (lpp_erase_triples (fst ` D)) (lpp_erase_success P)"])
    apply (erule targets)
    apply (blast intro: child)
    by (blast dest: lpp_stable_call_structural)
qed

ML \<open>
val checked = [@{thm lpp_stable_structural_selected_target}, @{thm lpp_stable_structural_entries_SN}];
val inherited = map (fst o fst) (Thm_Deps.all_oracles [@{thm check_trs_termination_proof}]);
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (map (fst o fst) (Thm_Deps.all_oracles checked))
  then error "Untrusted structural entry coverage" else ();
\<close>
end
