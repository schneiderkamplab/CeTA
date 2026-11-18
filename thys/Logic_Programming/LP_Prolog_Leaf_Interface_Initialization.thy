theory LP_Prolog_Leaf_Interface_Initialization
 imports LP_Prolog_Attached_Forest_Composition LP_Cut_Return_State
begin

text \<open>Observation slots must refer to the actual payload of every frame.
The default value outside a return interface is not evidence for a caller
observation. Initialization retains the source evaluation and all saved frames.\<close>

definition lpp_check_leaf_interface_slot where
 "lpp_check_leaf_interface_slot payload slot source_term =
   (slot < length payload \<and> payload!slot=source_term)"

lemma lpp_checked_leaf_interface_slot_eval:
 assumes checked: "lpp_check_leaf_interface_slot payload slot source_term"
 shows "lpc_return_env payload eta slot = lp_ieval source_term eta"
 using checked by (simp add: lpp_check_leaf_interface_slot_def lpc_return_env_def)

lemma lpp_leaf_interface_slot_initial:
 assumes checked: "lpp_check_leaf_interface_slot payload slot source_term"
 and observed: "lpp_runtime_structure (lp_ieval source_term eta) shape"
 shows "lpp_runtime_leaf_effect A shape (lpc_return_env payload eta slot)"
 using lpp_runtime_leaf_effect_initial[OF observed]
 by (simp add: lpp_checked_leaf_interface_slot_eval[OF checked])

lemma lpp_leaf_return_stack_initial:
 assumes observations: "\<And>entry payload slot shape. (entry,payload)\<in>set ss \<Longrightarrow>
   (slot,shape)\<in>set specs \<Longrightarrow>
   \<exists>source_term. lpp_check_leaf_interface_slot payload slot source_term \<and>
     lpp_runtime_structure (lp_ieval source_term eta) shape"
 shows "lpp_leaf_stack_invariant A specs (lpc_return_eval eta ss)"
 using observations lpp_leaf_interface_slot_initial
 by (auto simp: lpp_leaf_stack_invariant_def lpc_return_eval_def list_all_iff; blast)

lemma lpp_leaf_interface_missing_slot:
 "\<not>lpp_check_leaf_interface_slot payload (length payload) source_term"
 by (simp add: lpp_check_leaf_interface_slot_def)

lemma lpp_leaf_interface_wrong_term:
 assumes "slot < length payload" "payload!slot \<noteq> source_term"
 shows "\<not>lpp_check_leaf_interface_slot payload slot source_term"
 using assms by (simp add: lpp_check_leaf_interface_slot_def)

lemma lpp_leaf_interface_variable_slot:
 "lpp_check_leaf_interface_slot [Var x,Var y] 1 (Var y)"
 by (simp add: lpp_check_leaf_interface_slot_def)

ML \<open>
val checked = @{thms lpp_checked_leaf_interface_slot_eval lpp_leaf_interface_slot_initial
 lpp_leaf_return_stack_initial lpp_leaf_interface_missing_slot
 lpp_leaf_interface_wrong_term lpp_leaf_interface_variable_slot};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted leaf interface initialization" else ();
\<close>
end
