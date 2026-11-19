theory LP_Prolog_Split_Prefix_Partial_Entry
 imports LP_Prolog_Split_Prefix_Caller_Entry LP_Prolog_Recursive_Partial_Entry
begin

lemma lpp_split_prefix_partial_initial:
 fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 and p q :: "string lp_cut_symbol"
 and caller helper_env :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes checked: "lpp_check_prefix_caller_coordinates payload helper_slot tail_slot caller_slot hi ti ci"
 and entry: "lpp_recursive_partial_entry initial_parameter input_slot parameter_slot helper_slot tail_slot caller_slot eta"
 defines caller_env: "caller \<equiv> lpc_return_env payload eta"
 and rest_def: "rest \<equiv> [LPCAtom (Fun q [Var ti,Var hi,Var ci])]"
 and runtime_def: "runtime \<equiv> [(LPCGoals [LPCAtom (LPIFun p [eta input_slot,eta parameter_slot,eta helper_slot])],
   case_sum helper_env caller)]"
 shows "\<exists>xs caller_shape.
   lpp_runtime_structure (caller ti) (lpp_structural_argument_list xs) \<and>
   lpp_runtime_structure (caller ci) caller_shape \<and>
   lpp_finite_term (caller ci) \<and>
   (\<exists>v. caller hi=LPIVar v) \<and>
   (\<exists>n. lpp_list_length (caller ti) n) \<and>
   set2_lp_iterm (caller hi) \<inter> (set2_lp_iterm (caller ti) \<union> set2_lp_iterm (caller ci))={} \<and>
   lpp_observer_invariant A [(ti,lpp_structural_argument_list xs),(ci,caller_shape)] rest runtime"
proof -
 have coords: "caller hi=eta helper_slot" "caller ti=eta tail_slot" "caller ci=eta caller_slot"
  using lpp_prefix_caller_coordinate_values[OF checked, of eta] by (simp_all add: caller_env)
 have input_finite: "lpp_finite_term (eta input_slot)"
 and tail_finite: "lpp_finite_term (caller ti)"
 and caller_finite: "lpp_finite_term (caller ci)"
 and fresh_output: "\<exists>v. caller hi=LPIVar v"
 and spine: "\<exists>n. lpp_list_length (caller ti) n"
 and separation: "set2_lp_iterm (caller hi) \<inter> (set2_lp_iterm (caller ti) \<union> set2_lp_iterm (caller ci))={}"
 and tracked: "lpp_runtime_parameter initial_parameter (eta parameter_slot)"
  using entry coords by (auto simp: lpp_recursive_partial_entry_def)
 have parameter_finite: "lpp_finite_term (eta parameter_slot)"
  by (rule lpp_ground_finite_term[OF lpp_runtime_parameter_ground[OF tracked]])
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
 show ?thesis using tail_observed caller_observed caller_finite fresh_output spine separation invariant by blast
qed

ML \<open>
val checked = @{thms lpp_split_prefix_partial_initial};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted partial prefix entry" else ();
\<close>
end
