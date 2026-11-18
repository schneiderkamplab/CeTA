theory LP_Prolog_Checked_Fresh_Univ_Step
 imports LP_Prolog_Actual_Univ_Caller_Leaf
begin

text \<open>Caller protection for the actual first univ operation is derived
from its preceding checked resolution. The post-resolution invariant includes
all saved alternatives and remains an explicit premise from the resolution
step theorem. No successful-return fact is assumed for resumed alternatives.\<close>

lemma lpp_checked_fresh_clause_univ_leaf_step:
 fixes SP :: "string lpp_success_clause list"
 and ret :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes checked: "lpp_check_separation_head P nd ctx a c witness"
 and fresh: "lpp_check_fresh_decomposition (fst (P!c)) (snd (P!c)) input_variable name_variable arguments_variable"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
 and observed: "lpp_stable_context_holds operation SP ctx eta"
 and resolution: "lpc_mgu_resolve (lp_ieval a eta)
   (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t ret)) rest) (fst (P!c)) (snd (P!c)) sigma rho"
 and finite_call: "lpp_finite_term (lp_ieval a eta)"
 and finite_resolved: "lpp_finite_term (lp_isubst (lp_ieval a eta) sigma)"
 and finite_rest: "lpp_finite_goals (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t ret)) rest)"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and initial: "\<And>slot shape. (slot,shape)\<in>set specs \<Longrightarrow>
   lpp_runtime_leaf_effect {u. vars_term u={}} shape (ret slot)"
 and step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [rho input_variable,
     LPIFun (LPCUser ''2:prolog_data_2e'') [rho name_variable,rho arguments_variable]])#pending_goals),
     \<lambda>slot. lp_isubst (ret slot) sigma)#saved) event tt"
 and invariant: "lpp_leaf_stack_invariant {u. vars_term u={}} specs
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [rho input_variable,
     LPIFun (LPCUser ''2:prolog_data_2e'') [rho name_variable,rho arguments_variable]])#pending_goals),
     \<lambda>slot. lp_isubst (ret slot) sigma)#saved)"
 shows "lpp_leaf_stack_invariant {u. vars_term u={}} specs tt"
proof (cases "rho input_variable")
 case (LPIVar v)
 show ?thesis by (rule lpp_actual_variable_univ_leaf_stack_step[OF step[unfolded LPIVar] invariant[unfolded LPIVar]])
next
 case (LPIFun f ts)
 obtain n r where nv: "rho name_variable=LPIVar n" and rv: "rho arguments_variable=LPIVar r"
 and distinct: "n\<noteq>r"
 and avoid: "n\<notin>set2_lp_iterm (rho input_variable)" "r\<notin>set2_lp_iterm (rho input_variable)"
  using lpp_check_fresh_decomposition_sound[OF fresh resolution finite_resolved] by blast
 have head: "lp_isubst (lp_ieval a eta) sigma=lp_ieval (fst (P!c)) rho"
  using resolution by (simp add: lpc_mgu_resolve_def)
 have finite_input: "lpp_finite_term (rho input_variable)"
  by (rule lpp_finite_eval_variable[OF _ finite_resolved[unfolded head]])
    (use fresh in \<open>simp add: lpp_check_fresh_decomposition_def\<close>)
 have finite: "list_all lpp_finite_term ts" using finite_input by (simp add: LPIFun)
 have protected: "{n,r}\<inter>set2_lp_iterm (lp_isubst (ret slot) sigma)={}"
  if member: "(slot,shape)\<in>set specs" for slot shape
 proof -
  have live: "slot\<in>(\<Union>g\<in>set rest. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
   using lpp_check_attached_leaf_slots_sound[OF covered] member by force
  have name_body: "name_variable\<in>lpc_body_only_variables (fst (P!c)) (snd (P!c))"
  and args_body: "arguments_variable\<in>lpc_body_only_variables (fst (P!c)) (snd (P!c))"
   using fresh by (auto simp: lpp_check_fresh_decomposition_def)
  note name = lpp_checked_head_acquires_caller_separation[
    OF checked known observed resolution finite_call finite_rest live name_body initial[OF member]]
  note args = lpp_checked_head_acquires_caller_separation[
    OF checked known observed resolution finite_call finite_rest live args_body initial[OF member]]
  show ?thesis using name args by (simp add: nv rv)
 qed
 show ?thesis
  by (rule lpp_actual_univ_leaf_stack_step[OF step[unfolded LPIFun nv rv]
    invariant[unfolded LPIFun nv rv] finite distinct avoid[unfolded LPIFun] protected])
qed

ML \<open>
val checked = @{thms lpp_checked_fresh_clause_univ_leaf_step};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted checked fresh univ step" else ();
\<close>
end
