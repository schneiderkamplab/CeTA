theory LP_Prolog_Partial_Query_Initial
 imports LP_Prolog_Split_Prefix_Partial_Entry LP_Prolog_Parameter_Subterms
begin

text \<open>Initialize the observational fragment for an (o,i,o) call.
Input and output_value may be arbitrary finite terms and may share variables.
This does not establish the source-family representation or its node premises.\<close>

lemma lpp_partial_query_initial:
 fixes input_value parameter_value output_value :: "(string lp_cut_symbol,string) lp_iterm"
 and caller helper :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes input_finite: "lpp_finite_term input_value"
 and output_finite: "lpp_finite_term output_value"
 and parameter_ground: "lp_seg_ground parameter_value"
 and input_slot: "caller ii = input_value"
 and output_slot: "caller oi = output_value"
 shows "\<exists>c input_shape output_shape.
   vars_term c={} \<and> parameter_value = lp_ieval c LPIVar \<and>
   lpp_runtime_parameter c parameter_value \<and>
   lpp_runtime_structure input_value input_shape \<and>
   lpp_runtime_structure output_value output_shape \<and>
   lpp_observer_invariant (lpp_parameter_subterm_templates f g c)
    [(ii,input_shape),(oi,output_shape)] []
    [(LPCGoals [LPCAtom (LPIFun p [input_value,parameter_value,output_value])],case_sum helper caller)]"
proof -
 obtain c where ground: "vars_term c={}" and represented: "parameter_value = lp_ieval c LPIVar"
  using lp_seg_ground_finite[OF parameter_ground] by (auto simp: ground_vars_term_empty)
 have tracked: "lpp_runtime_parameter c parameter_value"
  using lpp_runtime_parameter_initial[OF ground] represented by simp
 have finite_parameter: "lpp_finite_term parameter_value"
  by (rule lpp_ground_finite_term[OF parameter_ground])
 obtain input_shape where input_shape: "lpp_runtime_structure input_value input_shape"
  using lpp_runtime_structure_exists[OF input_finite] by blast
 obtain output_shape where output_shape: "lpp_runtime_structure output_value output_shape"
  using lpp_runtime_structure_exists[OF output_finite] by blast
 have input_leaf: "lpp_runtime_leaf_effect (lpp_parameter_subterm_templates f g c) input_shape input_value"
  by (rule lpp_runtime_leaf_effect_initial[OF input_shape])
 have output_leaf: "lpp_runtime_leaf_effect (lpp_parameter_subterm_templates f g c) output_shape output_value"
  by (rule lpp_runtime_leaf_effect_initial[OF output_shape])
 have invariant: "lpp_observer_invariant (lpp_parameter_subterm_templates f g c)
    [(ii,input_shape),(oi,output_shape)] []
    [(LPCGoals [LPCAtom (LPIFun p [input_value,parameter_value,output_value])],case_sum helper caller)]"
  using input_finite output_finite finite_parameter input_leaf output_leaf input_slot output_slot
  by (simp add: lpp_observer_invariant_def lpc_reinterface_def lpc_attach_answers_def
    lpp_finite_execution_def lpp_finite_goals_def lpp_leaf_stack_invariant_def)
 show ?thesis using ground represented tracked input_shape output_shape invariant by blast
qed

ML \<open>
val checked = @{thms lpp_partial_query_initial};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted partial query initialization" else ();
\<close>
end
