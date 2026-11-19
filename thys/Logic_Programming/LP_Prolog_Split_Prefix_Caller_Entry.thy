theory LP_Prolog_Split_Prefix_Caller_Entry
 imports LP_Prolog_Recursive_Caller_Entry LP_Prolog_Observer_Invariant LP_Prolog_Structural_List_Observation
begin

text \<open>Initialize the actual suspended caller from its checked return slots.
The helper input and incoming parameter need not occur in the caller payload.
They remain in the helper goal and source context. No return is authenticated.\<close>

definition lpp_check_prefix_caller_coordinates where
 "lpp_check_prefix_caller_coordinates payload helper_slot tail_slot caller_slot hi ti ci =
  (distinct [hi,ti,ci] \<and> hi<length payload \<and> ti<length payload \<and> ci<length payload \<and>
   payload!hi=Var helper_slot \<and> payload!ti=Var tail_slot \<and> payload!ci=Var caller_slot)"

lemma lpp_prefix_caller_coordinate_values:
 assumes checked: "lpp_check_prefix_caller_coordinates payload helper_slot tail_slot caller_slot hi ti ci"
 shows "lpc_return_env payload eta hi=eta helper_slot"
 and "lpc_return_env payload eta ti=eta tail_slot"
 and "lpc_return_env payload eta ci=eta caller_slot"
 using checked by (simp_all add: lpp_check_prefix_caller_coordinates_def lpc_return_env_def)

lemma lpp_split_prefix_caller_initial:
 fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 and p q :: "string lp_cut_symbol"
 and caller helper_env :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes checked: "lpp_check_prefix_caller_coordinates payload helper_slot tail_slot caller_slot hi ti ci"
 and entry: "lpp_recursive_caller_entry initial_parameter input_slot parameter_slot helper_slot tail_slot caller_slot eta"
 defines caller_env: "caller \<equiv> lpc_return_env payload eta"
 and rest_def: "rest \<equiv> [LPCAtom (Fun q [Var ti,Var hi,Var ci])]"
 and runtime_def: "runtime \<equiv> [(LPCGoals [LPCAtom (LPIFun p [eta input_slot,eta parameter_slot,eta helper_slot])],
   case_sum helper_env caller)]"
 shows "\<exists>xs caller_shape.
   lpp_runtime_structure (caller ti) (lpp_structural_argument_list xs) \<and>
   lpp_runtime_structure (caller ci) caller_shape \<and>
   lpp_caller_output_mode (caller ci) \<and>
   (\<exists>v. caller hi=LPIVar v) \<and>
   (\<exists>n. lpp_list_length (caller ti) n) \<and>
   set2_lp_iterm (caller hi) \<inter> (set2_lp_iterm (caller ti) \<union> set2_lp_iterm (caller ci))={} \<and>
   lpp_observer_invariant A [(ti,lpp_structural_argument_list xs),(ci,caller_shape)] rest runtime"
proof -
 have coords: "caller hi=eta helper_slot" "caller ti=eta tail_slot" "caller ci=eta caller_slot"
  using lpp_prefix_caller_coordinate_values[OF checked, of eta] by (simp_all add: caller_env)
 have input_finite: "lpp_finite_term (eta input_slot)"
 and tail_finite: "lpp_finite_term (caller ti)"
 and mode: "lpp_caller_output_mode (caller ci)"
 and fresh_output: "\<exists>v. caller hi=LPIVar v"
 and spine: "\<exists>n. lpp_list_length (caller ti) n"
 and separation: "set2_lp_iterm (caller hi) \<inter> (set2_lp_iterm (caller ti) \<union> set2_lp_iterm (caller ci))={}"
 and tracked: "lpp_runtime_parameter initial_parameter (eta parameter_slot)"
  using entry coords by (auto simp: lpp_recursive_caller_entry_def)
 have parameter_finite: "lpp_finite_term (eta parameter_slot)"
  by (rule lpp_ground_finite_term[OF lpp_runtime_parameter_ground[OF tracked]])
 have caller_finite: "lpp_finite_term (caller ci)"
  using mode lpp_ground_finite_term by (auto simp: lpp_caller_output_mode_def)
 have helper_finite: "lpp_finite_term (caller hi)" using fresh_output by auto
 obtain xs where tail_observed: "lpp_runtime_structure (caller ti) (lpp_structural_argument_list xs)"
  using spine lpp_finite_spine_structural_observation[OF _ tail_finite] by blast
 obtain caller_shape where caller_observed: "lpp_runtime_structure (caller ci) caller_shape"
  using lpp_runtime_structure_exists[OF caller_finite] by blast
 have tail_leaf: "lpp_runtime_leaf_effect A (lpp_structural_argument_list xs) (caller ti)"
  by (rule lpp_runtime_leaf_effect_initial[OF tail_observed])
 have caller_leaf: "lpp_runtime_leaf_effect A caller_shape (caller ci)"
  by (rule lpp_runtime_leaf_effect_initial[OF caller_observed])
 have invariant: "lpp_observer_invariant A [(ti,lpp_structural_argument_list xs),(ci,caller_shape)] rest runtime"
  using input_finite parameter_finite helper_finite tail_finite caller_finite tail_leaf caller_leaf
  by (simp add: lpp_observer_invariant_def runtime_def rest_def lpc_reinterface_def
    lpc_attach_answers_def lpp_finite_execution_def lpp_finite_goals_def lpp_leaf_stack_invariant_def coords)
 show ?thesis using tail_observed caller_observed mode fresh_output spine separation invariant by blast
qed

ML \<open>
val checked = @{thms lpp_prefix_caller_coordinate_values lpp_split_prefix_caller_initial};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted split prefix caller entry" else ();
\<close>
end
