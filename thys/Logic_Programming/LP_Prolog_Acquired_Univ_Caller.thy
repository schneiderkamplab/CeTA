theory LP_Prolog_Acquired_Univ_Caller
 imports LP_Prolog_Attached_Return_Leaf LP_Prolog_Actual_Univ_Caller_Leaf
  LP_Prolog_Relational_Matching_Leaf
begin

text \<open>Acquire caller protection from the actual matching resolution, including
its full live continuation. Separation from the selected input alone is not
sufficient when the suspended caller has additional observed values.\<close>

lemma lpp_acquired_univ_caller_protection:
 assumes checked: "lpp_check_fresh_univ_clause h bs x y z"
 and mgu: "lpc_mgu_resolve a gs h bs sigma rho"
 and matching: "lp_ieval h witness=a"
 and finite_call: "lpp_finite_term a"
 and finite_rest: "lpp_finite_goals gs"
 and known: "lpp_runtime_leaf_effect A shape caller_value"
 and covered: "set2_lp_iterm caller_value \<subseteq>
   (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
 and ground: "\<And>u. u\<in>A \<Longrightarrow> vars_term u={}"
 shows "lpp_runtime_leaf_effect A shape (lp_isubst caller_value sigma) \<and>
   set2_lp_iterm (rho y) \<inter> set2_lp_iterm (lp_isubst caller_value sigma)={} \<and>
   set2_lp_iterm (rho z) \<inter> set2_lp_iterm (lp_isubst caller_value sigma)={}"
proof -
 have body_y: "y\<in>lpc_body_only_variables h bs"
 and body_z: "z\<in>lpc_body_only_variables h bs"
  using checked by (auto simp: lpp_check_fresh_univ_clause_def lpp_check_fresh_decomposition_def)
 have full_coverage: "set2_lp_iterm caller_value \<subseteq> set2_lp_iterm a \<union>
   (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)" using covered by blast
 have images: "lpp_bounded_images A sigma (set2_lp_iterm caller_value)"
  by (rule lpp_runtime_matching_leaf_images[OF mgu matching finite_call finite_rest full_coverage])
 have preserved: "lpp_runtime_leaf_effect A shape (lp_isubst caller_value sigma)"
  by (rule lpp_runtime_leaf_effect_substitute[OF known images ground])
 have before_finite: "lpp_finite_term caller_value" by (rule lpp_runtime_leaf_effect_finite[OF known])
 have after_finite: "lpp_finite_term (lp_isubst caller_value sigma)"
  by (rule lpp_runtime_leaf_effect_finite[OF preserved])
 show ?thesis using preserved
  lpp_runtime_fresh_body_separates_observer[OF mgu body_y finite_rest before_finite after_finite covered]
  lpp_runtime_fresh_body_separates_observer[OF mgu body_z finite_rest before_finite after_finite covered] by blast
qed

lemma lpp_acquired_univ_caller_leaf_step:
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
 and step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [rho x,
     LPIFun (LPCUser ''2:prolog_data_2e'') [rho y,rho z]])#pending),
     \<lambda>slot. lp_isubst (env slot) sigma)#saved) event result"
 shows "lpp_leaf_stack_invariant A specs result"
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
  ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [LPIFun f ts,
    LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar u,LPIVar v]])#pending),
    \<lambda>slot. lp_isubst (env slot) sigma)#saved)"
  using invariant protected by (auto simp: lpp_leaf_stack_invariant_def list_all_iff)
 show ?thesis
  by (rule lpp_actual_univ_leaf_stack_step[OF step[unfolded constructor vars] after_invariant finite distinct
    fresh[unfolded constructor]]) (use protected in blast)
qed

ML \<open>
val checked = @{thms lpp_acquired_univ_caller_protection lpp_acquired_univ_caller_leaf_step};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted acquired univ caller" else ();
\<close>
end
