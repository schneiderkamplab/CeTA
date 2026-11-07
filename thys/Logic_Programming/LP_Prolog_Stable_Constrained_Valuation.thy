theory LP_Prolog_Stable_Constrained_Valuation
 imports LP_Prolog_Stable_Numeric_Valuation
begin

text \<open>Additional independently justified return constraints use the same
numeric valuation as the checked source path. Arbitrary witnesses satisfying
only the weaker path cannot discharge these constraints.\<close>

theorem lpp_checked_stable_constrained_path_witness:
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
    and constraint_typed: "IA4.formula constraint"
    and constraint_sound: "\<And>source_values rho. (\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (source_values x)) \<Longrightarrow>
      (\<And>numeric_key. numeric_key\<in>set (map fst bindings) \<Longrightarrow>
        rho (lpp_numeric_rename bindings numeric_key)=lpp_stable_key_value operation eta source_values numeric_key) \<Longrightarrow>
      IA4.satisfies (lpp_integer_assignment rho) constraint"
    and member: "Transition from to (Conjunction [formula,constraint])\<in>transition_rules system"
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
  have extra_truth: "IA4.satisfies (lpp_integer_assignment ?rho) constraint"
    by (rule constraint_sound[OF typed assigned])
  have base_typed: "IA4.formula formula"
    using checked lpp_stable_numeric_path_formula_typed
    by (auto simp: lpp_check_stable_numeric_path_def)
  have combined: "IA4.satisfies (lpp_integer_assignment ?rho) (Conjunction [formula,constraint])"
    using truth extra_truth base_typed constraint_typed by simp
  have edge: "(State (lpp_integer_assignment pre) from,State (lpp_integer_assignment ?post) to)
    \<in>LPPIntegerLTS.transition system"
    by (rule LPPIntegerLTS.mem_transitionI[OF member],
      rule LPPIntegerLTS.mem_transition_step_TransitionI[where \<gamma>="lpp_integer_assignment ?middle"])
      (use combined before after in \<open>auto simp: lpp_integer_assignment_typed lpp_pre_post_integer_assignment\<close>)
  show ?thesis by (rule exI[of _ ?post])
    (use edge in \<open>simp add: lpp_numeric_post_def\<close>)
qed

ML \<open>
val checked = [@{thm lpp_checked_stable_constrained_path_witness}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted constrained valuation dependency" else ();
\<close>
end
