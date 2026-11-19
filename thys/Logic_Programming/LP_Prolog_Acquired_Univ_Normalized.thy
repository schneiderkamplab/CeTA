theory LP_Prolog_Acquired_Univ_Normalized
 imports LP_Prolog_Acquired_Univ_Caller LP_Prolog_Attached_Univ_Finite_Steps
begin

text \<open>The normalized equality path obtains caller protection from the
actual matching acquisition. Finite execution at block entry remains an explicit
premise; this rule does not authenticate the block exit or recursive returns.\<close>

lemma lpp_acquired_univ_caller_normalized_steps:
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
 and finite_execution: "lpp_finite_execution
   (lpc_attach_answers rest ((LPCGoals (LPCUnify (rho x) (rho x)#
     LPCUnify (LPIFun (LPCUser ''2:prolog_data_2e'') [rho y,rho z])
       (lpp_argument_list (LPIFun (names f) []#ts))#pending),
     \<lambda>slot. lp_isubst (env slot) sigma)#saved))"
 shows "first_event=None \<and> second_event=None \<and>
   lpp_finite_execution middle \<and> lpp_finite_execution result \<and>
   lpp_leaf_stack_invariant A specs result"
proof -
 have live: "set (map fst specs) \<subseteq>
   (\<Union>g\<in>set rest. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
  by (rule lpp_check_attached_leaf_slots_sound[OF covered])
 have runtime_coverage: "set2_lp_iterm (env slot) \<subseteq>
   (\<Union>g\<in>set (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t env)) rest).
    \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
  if member: "(slot,shape)\<in>set specs" for slot shape
 proof -
  have occurrence: "slot\<in>(\<Union>g\<in>set rest. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
   using live member by force
  show ?thesis by (rule lpp_attached_slot_runtime_coverage[OF occurrence])
 qed

 have finite_head: "lpp_finite_term (lp_ieval h rho)"
  by (rule lpp_matching_head_finite_instance[OF mgu matching finite_call])
 have finite_subst: "lpp_finite_term (lp_isubst a sigma)"
  using finite_head mgu by (simp add: lpc_mgu_resolve_def)
 obtain u v where vars: "rho y=LPIVar u" "rho z=LPIVar v"
 and distinct: "u\<noteq>v"
 and fresh: "u\<notin>set2_lp_iterm (rho x)" "v\<notin>set2_lp_iterm (rho x)"
  using lpp_check_fresh_univ_clause_sound[OF checked mgu finite_subst] by blast
 have input_member: "x\<in>vars_term h"
  using checked by (auto simp: lpp_check_fresh_univ_clause_def lpp_check_fresh_decomposition_def)
 have finite_input: "lpp_finite_term (rho x)"
  by (rule lpp_finite_eval_variable[OF input_member finite_head])
 have finite: "list_all lpp_finite_term ts" using finite_input constructor by simp
 have protected: "lpp_runtime_leaf_effect A shape (lp_isubst (env slot) sigma) \<and>
   {u,v}\<inter>set2_lp_iterm (lp_isubst (env slot) sigma)={}"
  if member: "(slot,shape)\<in>set specs" for slot shape
 proof -
  have known: "lpp_runtime_leaf_effect A shape (env slot)"
   using invariant member by (auto simp: lpp_leaf_stack_invariant_def list_all_iff)
  show ?thesis using lpp_acquired_univ_caller_protection[OF checked mgu matching finite_call finite_rest
    known runtime_coverage[OF member] ground] by (auto simp: vars)
 qed
 have after_invariant: "lpp_leaf_stack_invariant A specs
   ((old_frame,\<lambda>slot. lp_isubst (env slot) sigma)#saved)"
  using invariant protected by (auto simp: lpp_leaf_stack_invariant_def list_all_iff)
 show ?thesis
  by (rule lpp_attached_univ_domain_invariants[where names=names and f=f and ts=ts
    and x=u and y=v and env="\<lambda>slot. lp_isubst (env slot) sigma"
    and rest=rest and pending=pending, OF first_step[unfolded constructor vars]
    second_step after_invariant finite_execution[unfolded constructor vars] distinct
    fresh[unfolded constructor] _ covered]) (use protected in blast)
qed

ML \<open>
val checked = @{thms lpp_acquired_univ_caller_normalized_steps};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted acquired normalized univ" else ();
val _ = writeln "ACQUIRED_UNIV_NORMALIZED_KERNEL_CHECKED";
\<close>
end
