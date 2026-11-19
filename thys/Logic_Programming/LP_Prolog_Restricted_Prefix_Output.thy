theory LP_Prolog_Restricted_Prefix_Output
 imports LP_Prolog_Split_Prefix_Partial_Entry LP_Prolog_Attached_Caller_Copy
begin

text \<open>Observe the fresh helper result as a leaf, separately from the
arbitrary suspended caller output. The restricted invariant then supplies the
helper's free-or-ground mode in every retained frame. This does not assert
preservation of the invariant by unproved source paths.\<close>

lemma lpp_no_variable_leaf_template_iff:
 "lpp_no_variable_leaf (lpp_structure_template t) = (vars_term t = {})"
 by (induct t) (auto simp: list_all_iff)

lemma lpp_restricted_leaf_output_mode:
 assumes effect: "lpp_runtime_leaf_effect A (Fun (Inr ()) []) runtime_value"
 and ground: "\<And>u. u \<in> A \<Longrightarrow> vars_term u = {}"
 shows "lpp_caller_output_mode runtime_value"
proof -
 obtain t where represented: "runtime_value = lp_ieval t LPIVar"
 and related: "lpp_leaf_effect A (Fun (Inr ()) []) (lpp_structure_template t)"
  using effect unfolding lpp_runtime_leaf_effect_def lpp_runtime_structure_def by blast
 have alternatives: "lpp_structure_template t = Fun (Inr ()) [] \<or>
   lpp_no_variable_leaf (lpp_structure_template t)"
  using related ground lpp_ground_template_no_variable_leaf
  by (cases rule: lpp_leaf_effect.cases) (auto simp: lpp_no_variable_leaf_template_iff)
 show ?thesis using alternatives
  by (cases t) (auto simp: represented lpp_caller_output_mode_def
    lpp_no_variable_leaf_template_iff lp_seg_ground_eval list_all_iff)
qed

lemma lpp_observer_restricted_output_mode:
 assumes invariant: "lpp_observer_invariant A specs rest runtime"
 and observed: "(hi,Fun (Inr ()) []) \<in> set specs"
 and frame: "(goals,env) \<in> set runtime"
 and ground: "\<And>u. u \<in> A \<Longrightarrow> vars_term u = {}"
 shows "lpp_caller_output_mode (env (Inr hi))"
proof -
 have effect: "lpp_runtime_leaf_effect A (Fun (Inr ()) []) (env (Inr hi))"
  using invariant observed frame
  by (fastforce simp: lpp_observer_invariant_def lpp_leaf_stack_invariant_def
    lpc_reinterface_def list_all_iff)
 show ?thesis by (rule lpp_restricted_leaf_output_mode[OF effect ground])
qed

lemma lpp_restricted_prefix_output_initial:
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
   lpp_observer_invariant (lpp_parameter_leaf_templates f g initial_parameter)
    [(hi,Fun (Inr ()) []),(ti,lpp_structural_argument_list xs),(ci,caller_shape)] rest runtime"
proof -
 obtain xs caller_shape where tail_shape:
   "lpp_runtime_structure (caller ti) (lpp_structural_argument_list xs)"
 and caller_shape: "lpp_runtime_structure (caller ci) caller_shape"
 and fresh: "\<exists>v. caller hi = LPIVar v"
 and invariant: "lpp_observer_invariant (lpp_parameter_leaf_templates f g initial_parameter)
    [(ti,lpp_structural_argument_list xs),(ci,caller_shape)] rest runtime"
  using lpp_split_prefix_partial_initial[OF checked entry, where q=q and p=p and helper_env=helper_env
    and A="lpp_parameter_leaf_templates f g initial_parameter"]
  unfolding caller_env rest_def runtime_def by blast
 have helper_leaf: "lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter)
   (Fun (Inr ()) []) (caller hi)"
 proof -
  obtain v where eq: "caller hi = LPIVar v" using fresh by blast
  have "lpp_runtime_structure (caller hi) (Fun (Inr ()) [])"
   unfolding lpp_runtime_structure_def
   by (rule exI[of _ "Var v"]) (simp add: eq)
  then show ?thesis by (rule lpp_runtime_leaf_effect_initial)
 qed
 have extended: "lpp_observer_invariant (lpp_parameter_leaf_templates f g initial_parameter)
    [(hi,Fun (Inr ()) []),(ti,lpp_structural_argument_list xs),(ci,caller_shape)] rest runtime"
  using invariant helper_leaf
  by (simp add: lpp_observer_invariant_def lpp_leaf_stack_invariant_def
    runtime_def lpc_reinterface_def)
 show ?thesis using tail_shape caller_shape extended by blast
qed


lemma lpp_observed_output_copy_step:
 fixes env :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes step: "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCClause (LPCAtom (LPIFun p [input_value,parameter,output_value])#gs) c m,env)#saved)) event tt"
 and head: "fst (P!c) = Fun p [Fun nil [],Var n,Var n]"
 and spine: "lpp_finite_spine cons nil input_value spine_length"
 and tracked: "lpp_runtime_parameter initial_parameter parameter"
 and coordinate: "output_value = env hi"
 and observed: "(hi,Fun (Inr ()) []) \<in> set specs"
 and finite: "lpp_finite_execution
   (lpc_attach_answers rest ((LPCClause (LPCAtom (LPIFun p [input_value,parameter,output_value])#gs) c m,env)#saved))"
 and invariant: "lpp_leaf_stack_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs
   ((LPCClause (LPCAtom (LPIFun p [input_value,parameter,output_value])#gs) c m,env)#saved)"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 shows "lpp_finite_execution tt \<and>
   lpp_leaf_stack_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs tt"
proof -
 have ground: "vars_term initial_parameter = {}"
  using tracked by (simp add: lpp_runtime_parameter_def)
 have effect: "lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter)
   (Fun (Inr ()) []) output_value"
  using lpp_leaf_stack_head[OF invariant observed] coordinate by simp
 have mode: "lpp_caller_output_mode output_value"
  by (rule lpp_restricted_leaf_output_mode[OF effect])
   (rule lpp_parameter_leaf_templates_ground[OF ground])
 have finite_call: "lpp_finite_term (LPIFun p [input_value,parameter,output_value])"
 and finite_rest: "lpp_finite_goals (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t env)) rest)"
  using finite by (auto simp: lpp_finite_execution_def lpc_attach_answers_def lpp_finite_goals_def)
 have leaf: "lpp_leaf_stack_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs tt"
  by (rule lpp_attached_caller_copy_leaf_step[OF step head spine tracked mode finite_call finite_rest invariant covered])
 have result_finite: "lpp_finite_execution tt"
  by (rule lpp_attached_caller_copy_finite_step[OF step finite head spine tracked])
 show ?thesis using leaf result_finite by blast
qed

ML \<open>
val checked = @{thms lpp_no_variable_leaf_template_iff lpp_restricted_leaf_output_mode
 lpp_observer_restricted_output_mode lpp_restricted_prefix_output_initial lpp_observed_output_copy_step};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted restricted prefix output" else ();
\<close>
end
