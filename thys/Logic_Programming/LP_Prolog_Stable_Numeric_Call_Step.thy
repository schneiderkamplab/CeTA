theory LP_Prolog_Stable_Numeric_Call_Step
 imports LP_Prolog_Stable_Numeric_Rows
begin

theorem lpp_checked_stable_numeric_call_step:
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_stable_numeric_call_row T coordinates modes locations system ((h,ps,b,gs),os) receipt"
    and known: "lpp_integer_known (map lpp_transfer_variable (lppsnc_facts receipt)) eta"
    and observations: "list_all (lpp_stable_observation_holds operation eta) os"
    and matching: "lpp_success_iatom_subst a sigma=lpp_success_atom_eval h eta"
    and represented: "lpp_stable_numeric_call operation coordinates modes a pre"
  shows "\<exists>post. (State (lpp_integer_assignment pre) (locations (fst a)),
      State (lpp_integer_assignment post) (locations (fst b)))\<in>LPPIntegerLTS.transition system \<and>
    lpp_stable_numeric_call operation coordinates modes (lpp_success_atom_eval b eta) post"
proof -
  let ?K = "map lpp_transfer_variable (lppsnc_facts receipt)"
  let ?G = "lppsnc_ground receipt"
  let ?inputs = "lppsnc_inputs receipt"
  let ?outputs = "lppsnc_outputs receipt"
  let ?bindings = "lppsnc_bindings receipt"
  let ?formula = "lppsnc_formula receipt"
  have path: "lpp_check_stable_numeric_path ?K ?G ?inputs ?outputs
      (filter lpp_numeric_constraint_observation os) (lppsnc_tests receipt) ?bindings ?formula"
    and admissible: "lpp_check_stable_numeric_bindings ?inputs ?outputs ?bindings"
    and input_names: "map fst ?inputs=coordinates (fst h)"
    and input_modes: "map (lpp_stable_endpoint_mode o snd o snd) ?inputs=modes (fst h)"
    and input_terms: "map (fst o snd) ?inputs=snd h"
    and output_names: "map fst ?outputs=coordinates (fst b)"
    and output_modes: "map (lpp_stable_endpoint_mode o snd o snd) ?outputs=modes (fst b)"
    and output_terms: "map (fst o snd) ?outputs=snd b"
    and member: "Transition (locations (fst h)) (locations (fst b)) ?formula\<in>transition_rules system"
    and initial_assertion: "assertion system (locations (fst h))=Conjunction []"
    and final_assertion: "assertion system (locations (fst b))=Conjunction []"
    using checked by (auto simp: lpp_check_stable_numeric_call_row_def Let_def list_all_iff)
  have ground: "\<And>x. x\<in>set ?G \<Longrightarrow> lp_seg_ground (eta x)"
    by (rule lpp_stable_numeric_call_row_ground[OF checked known observations])
  have obs: "list_all (lpp_stable_observation_holds operation eta) (filter lpp_numeric_constraint_observation os)"
    using observations by (auto simp: list_all_iff)
  have input_rep: "lpp_stable_numeric_call operation coordinates modes (lpp_success_atom_eval h eta) pre"
    by (rule lpp_stable_numeric_call_match[OF matching represented])
  have input_tuple: "lpp_stable_numeric_tuple operation (map fst ?inputs)
      (map (lpp_stable_endpoint_mode o snd o snd) ?inputs)
      (map (\<lambda>e. lp_ieval (fst (snd e)) eta) ?inputs) pre"
    using input_rep input_names input_modes input_terms
    by (simp add: lpp_stable_numeric_call_def lpp_success_atom_eval_def map_map o_def input_terms[symmetric])
  obtain output_values where output_rep:
    "lpp_stable_numeric_call operation coordinates modes (lpp_success_atom_eval b eta) output_values"
    using lpp_stable_numeric_call_row_output[OF checked known observations] by blast
  have output_tuple: "lpp_stable_numeric_tuple operation (map fst ?outputs)
      (map (lpp_stable_endpoint_mode o snd o snd) ?outputs)
      (map (\<lambda>e. lp_ieval (fst (snd e)) eta) ?outputs) output_values"
    using output_rep output_names output_modes output_terms
    by (simp add: lpp_stable_numeric_call_def lpp_success_atom_eval_def map_map o_def output_terms[symmetric])
  have inputs: "\<And>coordinate t e. (coordinate,t,e)\<in>set ?inputs \<Longrightarrow>
      lpp_stable_coordinate_value operation (lpp_stable_endpoint_mode e) (lp_ieval t eta) (pre coordinate)"
    by (rule lpp_stable_numeric_tuple_endpoint[OF input_tuple])
  have outputs: "\<And>coordinate t e. (coordinate,t,e)\<in>set ?outputs \<Longrightarrow>
      lpp_stable_coordinate_value operation (lpp_stable_endpoint_mode e) (lp_ieval t eta) (output_values coordinate)"
    by (rule lpp_stable_numeric_tuple_endpoint[OF output_tuple])
  have before: "IA4.satisfies (lpp_integer_assignment pre) (assertion system (locations (fst h)))"
    by (simp add: initial_assertion)
  have after: "\<And>post. IA4.satisfies (lpp_integer_assignment post) (assertion system (locations (fst b)))"
    by (simp add: final_assertion)
  have witness: "\<exists>post. (State (lpp_integer_assignment pre) (locations (fst h)),
      State (lpp_integer_assignment post) (locations (fst b)))\<in>LPPIntegerLTS.transition system \<and>
      (\<forall>coordinate\<in>set (map fst ?outputs). post coordinate = output_values coordinate)"
  proof (rule lpp_checked_stable_numeric_path_witness[where operation=operation and eta=eta and pre=pre and output_values=output_values,
      OF compatible path admissible obs known])
    fix x assume member: "x\<in>set ?G"
    show "lp_seg_ground (eta x)" by (rule ground[OF member])
  next
    fix coordinate t e assume member: "(coordinate,t,e)\<in>set ?inputs"
    show "lpp_stable_coordinate_value operation (lpp_stable_endpoint_mode e) (lp_ieval t eta) (pre coordinate)" by (rule inputs[OF member])
  next
    fix coordinate t e assume member: "(coordinate,t,e)\<in>set ?outputs"
    show "lpp_stable_coordinate_value operation (lpp_stable_endpoint_mode e) (lp_ieval t eta) (output_values coordinate)" by (rule outputs[OF member])
  next
    show "Transition (locations (fst h)) (locations (fst b)) ?formula\<in>transition_rules system" by (rule member)
    show "IA4.satisfies (lpp_integer_assignment pre) (assertion system (locations (fst h)))" by (rule before)
    show "\<And>post. IA4.satisfies (lpp_integer_assignment post) (assertion system (locations (fst b)))" by (rule after)
  qed
  obtain post where step: "(State (lpp_integer_assignment pre) (locations (fst h)),
      State (lpp_integer_assignment post) (locations (fst b)))\<in>LPPIntegerLTS.transition system"
    and coordinates: "\<forall>coordinate\<in>set (map fst ?outputs). post coordinate = output_values coordinate"
    using witness by blast
  have post: "lpp_stable_numeric_call operation coordinates modes (lpp_success_atom_eval b eta) post"
    unfolding lpp_stable_numeric_call_def
    by (rule lpp_stable_numeric_tuple_coordinates[OF output_rep[unfolded lpp_stable_numeric_call_def]])
      (use coordinates output_names in \<open>auto simp: lpp_success_atom_eval_def\<close>)
  have predicate: "fst a=fst h"
    using arg_cong[OF matching, of fst]
    by (simp add: lpp_success_iatom_subst_def lpp_success_atom_eval_def)
  show ?thesis using step post predicate by auto
qed

ML \<open>
val checked = [@{thm lpp_checked_stable_numeric_call_step}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable numeric call step dependency" else ();
\<close>
end
