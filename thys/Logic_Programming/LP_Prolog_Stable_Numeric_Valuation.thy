theory LP_Prolog_Stable_Numeric_Valuation
 imports LP_Prolog_Stable_Numeric_Path
begin

fun lpp_stable_numeric_binding_admissible where
  "lpp_stable_numeric_binding_admissible inputs outputs (numeric_key,Pre coordinate) =
    list_ex (\<lambda>(input_coordinate,t,e). input_coordinate=coordinate \<and>
      lpp_stable_endpoint_numeric_expression e=LPPEVariable numeric_key) inputs"
| "lpp_stable_numeric_binding_admissible inputs outputs (numeric_key,Post coordinate) =
    (coordinate\<notin>set (map fst outputs))"
| "lpp_stable_numeric_binding_admissible inputs outputs (numeric_key,Intermediate coordinate) = True"

definition lpp_check_stable_numeric_bindings where
  "lpp_check_stable_numeric_bindings inputs outputs bindings =
    (distinct (map snd bindings) \<and>
      list_all (lpp_stable_numeric_binding_admissible inputs outputs) bindings)"

lemma lpp_stable_numeric_pre_binding:
  assumes checked: "lpp_check_stable_numeric_path K G inputs outputs observations receipts bindings formula"
    and admissible: "lpp_check_stable_numeric_bindings inputs outputs bindings"
    and typed: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (source_values x)"
    and ground: "\<And>x. x\<in>set G \<Longrightarrow> lp_seg_ground (eta x)"
    and inputs: "\<And>coordinate t e. (coordinate,t,e)\<in>set inputs \<Longrightarrow>
      lpp_stable_coordinate_value operation (lpp_stable_endpoint_mode e) (lp_ieval t eta) (pre coordinate)"
    and binding: "(numeric_key,Pre coordinate)\<in>set bindings"
  shows "pre coordinate=lpp_stable_key_value operation eta source_values numeric_key"
proof -
  have admissible_row: "lpp_stable_numeric_binding_admissible inputs outputs (numeric_key,Pre coordinate)"
    using admissible binding by (auto simp: lpp_check_stable_numeric_bindings_def list_all_iff)
  obtain t e where member: "(coordinate,t,e)\<in>set inputs"
    and numeric_key: "lpp_stable_endpoint_numeric_expression e=LPPEVariable numeric_key"
    using admissible_row by (auto simp: list_ex_iff)
  have check: "lpp_check_stable_endpoint K G t e"
    using checked member by (auto simp: lpp_check_stable_numeric_path_def list_all_iff)
  have determined: "lpp_stable_coordinate_value operation (lpp_stable_endpoint_mode e) (lp_ieval t eta)
    (lpp_stable_key_value operation eta source_values numeric_key)"
    using lpp_checked_stable_endpoint[where operation=operation and eta=eta and rho=source_values, OF check typed ground] by (simp add: numeric_key)
  show ?thesis by (rule lpp_stable_coordinate_unique[OF inputs[OF member] determined])
qed

lemma lpp_stable_numeric_assigned:
  assumes checked: "lpp_check_stable_numeric_path K G inputs outputs observations receipts bindings formula"
    and admissible: "lpp_check_stable_numeric_bindings inputs outputs bindings"
    and typed: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (source_values x)"
    and ground: "\<And>x. x\<in>set G \<Longrightarrow> lp_seg_ground (eta x)"
    and inputs: "\<And>coordinate t e. (coordinate,t,e)\<in>set inputs \<Longrightarrow>
      lpp_stable_coordinate_value operation (lpp_stable_endpoint_mode e) (lp_ieval t eta) (pre coordinate)"
    and member: "numeric_key\<in>set (map fst bindings)"
  shows "lpp_trans_integer pre
      (lpp_numeric_post bindings (lpp_stable_key_value operation eta source_values) (map fst outputs) output_values)
      (lpp_numeric_middle bindings (lpp_stable_key_value operation eta source_values))
      (lpp_numeric_rename bindings numeric_key) = lpp_stable_key_value operation eta source_values numeric_key"
proof -
  have distinct: "distinct (map snd bindings)"
    and rows: "list_all (lpp_stable_numeric_binding_admissible inputs outputs) bindings"
    using admissible by (auto simp: lpp_check_stable_numeric_bindings_def)
  have pre: "pre coordinate=lpp_stable_key_value operation eta source_values x"
    if "(x,Pre coordinate)\<in>set bindings" for x coordinate
    by (rule lpp_stable_numeric_pre_binding[where pre=pre and operation=operation and eta=eta and source_values=source_values, OF checked admissible typed ground inputs that])
  have fresh: "coordinate\<notin>set (map fst outputs)"
    if "(x,Post coordinate)\<in>set bindings" for x coordinate
  proof -
    have row: "lpp_stable_numeric_binding_admissible inputs outputs (x,Post coordinate)"
      using rows that by (auto simp only: list_all_iff)
    show ?thesis using row by simp
  qed
  have mapped: "map_of bindings numeric_key\<noteq>None" using member by (simp add: map_of_eq_None_iff)
  obtain v where lookup: "map_of bindings numeric_key=Some v" using mapped by (cases "map_of bindings numeric_key") auto
  have binding: "(numeric_key,v)\<in>set bindings" by (rule map_of_SomeD[OF lookup])
  show ?thesis using lpp_numeric_valuation_extension[OF distinct pre fresh binding]
    by (simp add: lpp_numeric_rename_def lookup)
qed

theorem lpp_checked_stable_numeric_path_witness:
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_stable_numeric_path K G inputs outputs observations receipts bindings formula"
    and admissible: "lpp_check_stable_numeric_bindings inputs outputs bindings"
    and observed: "list_all (lpp_stable_observation_holds operation eta) observations"
    and known: "lpp_integer_known K eta"
    and ground: "\<And>x. x\<in>set G \<Longrightarrow> lp_seg_ground (eta x)"
    and inputs: "\<And>coordinate t e. (coordinate,t,e)\<in>set inputs \<Longrightarrow>
      lpp_stable_coordinate_value operation (lpp_stable_endpoint_mode e) (lp_ieval t eta) (pre coordinate)"
    and outputs: "\<And>coordinate t e. (coordinate,t,e)\<in>set outputs \<Longrightarrow>
      lpp_stable_coordinate_value operation (lpp_stable_endpoint_mode e) (lp_ieval t eta) (output_values coordinate)"
    and member: "Transition from to formula\<in>transition_rules system"
    and before: "IA4.satisfies (lpp_integer_assignment pre) (assertion system from)"
    and after: "\<And>post. IA4.satisfies (lpp_integer_assignment post) (assertion system to)"
  shows "\<exists>post. (State (lpp_integer_assignment pre) from,State (lpp_integer_assignment post) to)
    \<in>LPPIntegerLTS.transition system \<and>
    (\<forall>coordinate\<in>set (map fst outputs). post coordinate = output_values coordinate)"
proof -
  obtain source_values where typed: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (source_values x)"
    using lpp_integer_known_environment[OF known] by blast
  let ?values = "lpp_stable_key_value operation eta source_values"
  let ?post = "lpp_numeric_post bindings ?values (map fst outputs) output_values"
  let ?middle = "lpp_numeric_middle bindings ?values"
  let ?rho = "lpp_trans_integer pre ?post ?middle"
  have assigned: "?rho (lpp_numeric_rename bindings numeric_key)=?values numeric_key"
    if "numeric_key\<in>set (map fst bindings)" for numeric_key
    by (rule lpp_stable_numeric_assigned[where pre=pre and operation=operation and output_values=output_values and eta=eta, OF checked admissible typed ground inputs that])
  have output_rep: "lpp_stable_coordinate_value operation (lpp_stable_endpoint_mode e)
      (lp_ieval t eta) (?post coordinate)"
    if row: "(coordinate,t,e)\<in>set outputs" for coordinate t e
    using outputs[OF row] row by (auto simp: lpp_numeric_post_def image_iff Bex_def)
  have truth: "IA4.satisfies (lpp_integer_assignment ?rho) formula"
    by (rule lpp_check_stable_numeric_path_sound[where operation=operation and rho="?rho" and eta=eta,
      OF compatible checked observed typed ground assigned])
      (use inputs output_rep in auto)
  have edge: "(State (lpp_integer_assignment pre) from,State (lpp_integer_assignment ?post) to)
    \<in>LPPIntegerLTS.transition system"
    by (rule LPPIntegerLTS.mem_transitionI[OF member],
      rule LPPIntegerLTS.mem_transition_step_TransitionI[where \<gamma>="lpp_integer_assignment ?middle"])
      (use truth before after in \<open>auto simp: lpp_integer_assignment_typed lpp_pre_post_integer_assignment\<close>)
  show ?thesis by (rule exI[of _ ?post])
    (use edge in \<open>simp add: lpp_numeric_post_def\<close>)
qed

ML \<open>
val checked = [@{thm lpp_stable_numeric_pre_binding}, @{thm lpp_stable_numeric_assigned}, @{thm lpp_checked_stable_numeric_path_witness}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable valuation dependency" else ();
\<close>
end
