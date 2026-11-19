theory LP_Prolog_Acquired_Univ_Entry
 imports LP_Prolog_Acquired_Univ_Normalized
begin

text \<open>Discharge normalized entry finiteness using the actual resolved body
and continuation. Saved alternatives retain their explicit finite invariant.
The body and pending equalities are coordinate obligations for block assembly.\<close>

lemma lpp_acquired_univ_normalized_from_resolution:
 fixes env :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes checked: "lpp_check_fresh_univ_clause h bs x y z"
 and mgu: "lpc_mgu_resolve a (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t env)) rest) h bs sigma rho"
 and matching: "lp_ieval h witness=a"
 and finite_call: "lpp_finite_term a"
 and finite_rest: "lpp_finite_goals (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t env)) rest)"
 and invariant: "lpp_leaf_stack_invariant A specs ((old_frame,env)#saved)"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and ground: "\<And>u. u\<in>A \<Longrightarrow> vars_term u={}"
 and constructor: "rho x=LPIFun f ts"
 and first_step: "lpp_domain_answers P B U D
   (lpc_attach_answers rest ((LPCGoals (LPCUnify (rho x) (rho x)#
     LPCUnify (LPIFun (LPCUser ''2:prolog_data_2e'') [rho y,rho z])
       (lpp_argument_list (LPIFun (names f) []#ts))#pending),
     \<lambda>slot. lp_isubst (env slot) sigma)#saved)) first_event middle"
 and second_step: "lpp_domain_answers P B U D middle second_event result"
 and body_shape: "bs=LPCAtom (Fun (LPCUser ''2:=..'')
   [Var x,Fun (LPCUser ''2:prolog_data_2e'') [Var y,Var z]])#body_tail"
 and pending_shape: "pending=map (lp_cut_bind mark (\<lambda>t. lp_ieval t rho)) body_tail @
   map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs"
 and saved_finite: "lpp_finite_execution (lpc_attach_answers rest saved)"
 shows "first_event=None \<and> second_event=None \<and>
   lpp_finite_execution middle \<and> lpp_finite_execution result \<and>
   lpp_leaf_stack_invariant A specs result"
proof -
 have resolved: "lpp_finite_goals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t rho)) bs @
   map (lp_cut_map (\<lambda>t. lp_isubst t sigma))
     (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t env)) rest))"
  by (rule lpp_matching_head_resolution_finite[OF mgu matching finite_call finite_rest])
 have finite_entry: "lpp_finite_execution
   (lpc_attach_answers rest ((LPCGoals (LPCUnify (rho x) (rho x)#
     LPCUnify (LPIFun (LPCUser ''2:prolog_data_2e'') [rho y,rho z])
       (lpp_argument_list (LPIFun (names f) []#ts))#pending),
     \<lambda>slot. lp_isubst (env slot) sigma)#saved))"
  using resolved saved_finite
  by (auto simp: body_shape pending_shape constructor lpc_attach_answers_def
    lpp_finite_execution_def lpp_finite_goals_def lpp_argument_list_finite
    lp_cut_map_comp lp_ieval_subst o_def)
 show ?thesis
  by (rule lpp_acquired_univ_caller_normalized_steps[where names=names and f=f and ts=ts
    and env=env and pending=pending and rest=rest, OF checked mgu matching finite_call
    finite_rest invariant covered ground constructor first_step second_step finite_entry])
qed

ML \<open>
val checked = @{thms lpp_acquired_univ_normalized_from_resolution};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted acquired univ entry" else ();
val _ = writeln "ACQUIRED_UNIV_ENTRY_KERNEL_CHECKED";
\<close>
end
