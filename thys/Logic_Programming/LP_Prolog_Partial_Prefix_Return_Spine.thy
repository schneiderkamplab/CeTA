theory LP_Prolog_Partial_Prefix_Return_Spine
 imports LP_Prolog_Split_Prefix_Partial_Entry LP_Prolog_Functor_Spine_Return
begin

text \<open>Initialize the actual-answer spine theorem at a checked recursive
prefix. An actual answer is required; termination and leaf effects are separate.\<close>

lemma lpp_partial_prefix_actual_return_spine:
 fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes coordinates: "lpp_check_prefix_caller_coordinates payload helper_slot tail_slot caller_slot hi ti ci"
 and entry: "lpp_recursive_partial_entry initial_parameter input_slot parameter_slot helper_slot tail_slot caller_slot eta"
 and actual: "lp_actual_answer (lpp_domain_answers P B U D)
   [(LPCGoals [LPCAtom (LPIFun p [eta input_slot,eta parameter_slot,eta helper_slot])],
     lpc_return_env payload eta)] returned_env"
 shows "\<exists>n. lpp_list_length (eta tail_slot) n \<and>
   lpp_list_length (returned_env ti) n \<and> n<Suc n"
proof -
 obtain n where initial: "lpp_list_length (eta tail_slot) n"
  using entry by (auto simp: lpp_recursive_partial_entry_def)
 have coordinate: "lpc_return_env payload eta ti=eta tail_slot"
  using lpp_prefix_caller_coordinate_values[OF coordinates, of eta] by simp
 have initialized: "list_all (\<lambda>frame. lpp_list_length (lp_ieval (Var ti) (snd frame)) n)
   [(LPCGoals [LPCAtom (LPIFun p [eta input_slot,eta parameter_slot,eta helper_slot])],
     lpc_return_env payload eta)]"
  using initial coordinate by simp
 have returned: "lpp_list_length (returned_env ti) n"
  using lpp_actual_return_preserves_list_length[OF actual initialized] by simp
 show ?thesis using initial returned by auto
qed

ML \<open>
val checked = @{thms lpp_partial_prefix_actual_return_spine};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted partial prefix return spine" else ();
\<close>
end
