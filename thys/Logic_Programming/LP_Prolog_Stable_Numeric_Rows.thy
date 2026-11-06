theory LP_Prolog_Stable_Numeric_Rows
 imports LP_Prolog_Stable_Endpoint_Tuples
begin

record 'v lpp_stable_numeric_call_receipt =
  lppsnc_facts :: "'v lpp_transfer_fact list"
  lppsnc_ground :: "'v list"
  lppsnc_inputs :: "'v lpp_stable_numeric_endpoint list"
  lppsnc_outputs :: "'v lpp_stable_numeric_endpoint list"
  lppsnc_tests :: "'v lpp_stable_condition_receipt list"
  lppsnc_bindings :: "('v lpp_stable_numeric_key * string trans_var) list"
  lppsnc_formula :: "string trans_var ia4_exp Formula.formula"

definition lpp_check_stable_numeric_call_row where
  "lpp_check_stable_numeric_call_row T coordinates modes locations system (triple::'v lpp_observed_triple)
      (receipt::'v lpp_stable_numeric_call_receipt) =
    (case triple of ((h,ps,b,gs),os) \<Rightarrow>
      let K=map lpp_transfer_variable (lppsnc_facts receipt); G=lppsnc_ground receipt;
          inputs=lppsnc_inputs receipt; outputs=lppsnc_outputs receipt;
          bindings=lppsnc_bindings receipt; formula=lppsnc_formula receipt
      in lpp_check_path_types T ps gs (lppsnc_facts receipt) \<and>
        set G \<subseteq> set K \<union> lpp_observations_ground os \<and>
        lpp_check_stable_numeric_path K G inputs outputs
          (filter lpp_numeric_constraint_observation os) (lppsnc_tests receipt) bindings formula \<and>
        lpp_check_stable_numeric_bindings inputs outputs bindings \<and>
        map fst inputs=coordinates (fst h) \<and>
        map (lpp_stable_endpoint_mode o snd o snd) inputs=modes (fst h) \<and>
        map (fst o snd) inputs=snd h \<and>
        map fst outputs=coordinates (fst b) \<and>
        map (lpp_stable_endpoint_mode o snd o snd) outputs=modes (fst b) \<and>
        map (fst o snd) outputs=snd b \<and>
        Transition (locations (fst h)) (locations (fst b)) formula\<in>transition_rules system \<and>
        assertion system (locations (fst h))=Conjunction [] \<and>
        assertion system (locations (fst b))=Conjunction [])"

lemma lpp_stable_numeric_call_row_types:
  fixes P :: "'v lpp_success_clause list" and receipt :: "'v lpp_stable_numeric_call_receipt"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_stable_numeric_call_row T coordinates modes locations system ((h,ps,b,gs),os) receipt"
    and transfer: "lpp_check_transfer_program T P receipts"
    and guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta) gs"
    and facts: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation))
      (map (\<lambda>g. lpp_success_atom_eval g eta) ps)"
  shows "lpp_integer_known (map lpp_transfer_variable (lppsnc_facts receipt)) eta"
  by (rule lpp_check_path_types_sound[OF transfer _ guards facts lpp_stable_evaluation_integer_contract[OF compatible]])
    (use checked in \<open>auto simp: lpp_check_stable_numeric_call_row_def Let_def\<close>)

lemma lpp_stable_numeric_call_row_ground:
  assumes checked: "lpp_check_stable_numeric_call_row T coordinates modes locations system ((h,ps,b,gs),os) receipt"
    and known: "lpp_integer_known (map lpp_transfer_variable (lppsnc_facts receipt)) eta"
    and observed: "list_all (lpp_stable_observation_holds operation eta) os"
    and member: "x\<in>set (lppsnc_ground receipt)"
  shows "lp_seg_ground (eta x)"
proof -
  have cover: "set (lppsnc_ground receipt) \<subseteq>
    set (map lpp_transfer_variable (lppsnc_facts receipt)) \<union> lpp_observations_ground os"
    using checked by (auto simp: lpp_check_stable_numeric_call_row_def Let_def)
  have integers: "\<forall>x\<in>set (map lpp_transfer_variable (lppsnc_facts receipt)). lp_seg_ground (eta x)"
    using known by (auto simp: lpp_integer_known_def lpp_integer_value_def intro: lp_seg_ground.intros)
  have each: "\<forall>x\<in>lpp_observation_ground_vars ob. lp_seg_ground (eta x)"
    if ob: "ob\<in>set os" for ob
  proof -
    have held: "lpp_evaluation_observation_holds (lpp_stable_scalar_evaluation operation) eta ob"
      by (rule lpp_stable_observation_refines) (use observed ob in \<open>auto simp: list_all_iff\<close>)
    show ?thesis by (rule lpp_evaluation_observation_ground[OF lpp_stable_scalar_evaluation_ground held])
  qed
  show ?thesis using cover member integers each by (auto simp: lpp_observations_ground_def)
qed

lemma lpp_stable_numeric_call_row_output:
  assumes checked: "lpp_check_stable_numeric_call_row T coordinates modes locations system ((h,ps,b,gs),os) receipt"
    and known: "lpp_integer_known (map lpp_transfer_variable (lppsnc_facts receipt)) eta"
    and observed: "list_all (lpp_stable_observation_holds operation eta) os"
  shows "\<exists>rho. lpp_stable_numeric_call operation coordinates modes (lpp_success_atom_eval b eta) rho"
proof -
  let ?K = "map lpp_transfer_variable (lppsnc_facts receipt)"
  let ?G = "lppsnc_ground receipt"
  let ?outputs = "lppsnc_outputs receipt"
  have endpoints: "list_all (\<lambda>(coordinate,t,e). lpp_check_stable_endpoint ?K ?G t e) ?outputs"
    and distinct: "distinct (map fst ?outputs)"
    and names: "map fst ?outputs=coordinates (fst b)"
    and modes: "map (lpp_stable_endpoint_mode o snd o snd) ?outputs=modes (fst b)"
    and terms: "map (fst o snd) ?outputs=snd b"
    using checked by (auto simp: lpp_check_stable_numeric_call_row_def lpp_check_stable_numeric_path_def Let_def)
  have ground: "\<And>x. x\<in>set ?G \<Longrightarrow> lp_seg_ground (eta x)"
    by (rule lpp_stable_numeric_call_row_ground[OF checked known observed])
  obtain rho where tuple: "lpp_stable_numeric_tuple operation (map fst ?outputs)
      (map (lpp_stable_endpoint_mode o snd o snd) ?outputs)
      (map (\<lambda>e. lp_ieval (fst (snd e)) eta) ?outputs) rho"
    using lpp_stable_endpoint_tuple_exists[OF endpoints distinct known ground] by blast
  have "lpp_stable_numeric_call operation coordinates modes (lpp_success_atom_eval b eta) rho"
    using tuple names modes terms by (simp add: lpp_stable_numeric_call_def lpp_success_atom_eval_def map_map o_def terms[symmetric])
  then show ?thesis by blast
qed

ML \<open>
val checked = [@{thm lpp_stable_numeric_call_row_types}, @{thm lpp_stable_numeric_call_row_ground},
  @{thm lpp_stable_numeric_call_row_output}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable numeric row dependency" else ();
\<close>
end
