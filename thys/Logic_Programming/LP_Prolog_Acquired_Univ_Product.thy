theory LP_Prolog_Acquired_Univ_Product
 imports LP_Prolog_Normalized_Univ_Product
begin

text \<open>Derive the joint normalized entry invariant and fresh-output caller
protection from actual matching acquisition. The initial helper representation
and global equality coverage remain explicit assembly obligations.\<close>

lemma lpp_acquired_normalized_entry_invariant:
 fixes SP :: "string lpp_success_clause list"
 and combined_env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes acquired: "lpp_check_fresh_univ_clause h bs x y z"
 and mgu: "lpc_mgu_resolve a
   (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t (\<lambda>slot. combined_env (Inr slot)))) rest)
   h bs sigma rho"
 and matching: "lp_ieval h witness=a"
 and incoming: "lpp_observer_invariant A specs rest
   ((LPCClause (LPCAtom a#gs) c mark,combined_env)#saved)"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and ground: "\<And>v. v\<in>A \<Longrightarrow> vars_term v={}"
 and constructor: "rho x=LPIFun f ts"
 and body_shape: "bs=LPCAtom (Fun (LPCUser ''2:=..'')
   [Var x,Fun (LPCUser ''2:prolog_data_2e'') [Var y,Var z]])#body_tail"
 and pending_shape: "pending=map (lp_cut_bind mark (\<lambda>t. lp_ieval t rho)) body_tail @
   map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs"
 and tail: "pending\<noteq>[]"
 and shape: "runtime=(LPCGoals (LPCUnify (rho x) (rho x)#
   LPCUnify (LPIFun (LPCUser ''2:prolog_data_2e'') [rho y,rho z])
    (lpp_argument_list (LPIFun (names f) []#ts))#pending),
    case_sum helper_env (\<lambda>slot. lp_isubst (combined_env (Inr slot)) sigma))#saved"

 shows "lpp_observer_invariant A specs rest runtime"
proof -
 let ?R = "\<lambda>env slot. env (Inr slot)"
 have finite_call: "lpp_finite_term a"
 and finite_rest: "lpp_finite_goals
   (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t (?R combined_env))) rest)"
 and saved_finite: "lpp_finite_execution (lpc_attach_answers rest (lpc_reinterface ?R saved))"
 and caller_leaf: "lpp_leaf_stack_invariant A specs
   ((LPCClause (LPCAtom a#gs) c mark,?R combined_env)#lpc_reinterface ?R saved)"
  using incoming by (auto simp: lpp_observer_invariant_def lpc_reinterface_def
   lpc_attach_answers_def lpp_finite_execution_def lpp_finite_goals_def)
 have live: "set (map fst specs) \<subseteq>
   (\<Union>g\<in>set rest. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
  by (rule lpp_check_attached_leaf_slots_sound[OF covered])
 have runtime_coverage: "set2_lp_iterm (combined_env (Inr slot)) \<subseteq>
   (\<Union>g\<in>set (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t (\<lambda>slot. combined_env (Inr slot)))) rest).
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
  using lpp_check_fresh_univ_clause_sound[OF acquired mgu finite_subst] by blast
 have input_member: "x\<in>vars_term h"
  using acquired by (auto simp: lpp_check_fresh_univ_clause_def lpp_check_fresh_decomposition_def)
 have finite_input: "lpp_finite_term (rho x)"
  by (rule lpp_finite_eval_variable[OF input_member finite_head])
 have finite: "list_all lpp_finite_term ts" using finite_input constructor by simp
 have protected: "lpp_runtime_leaf_effect A shape (lp_isubst (combined_env (Inr slot)) sigma) \<and>
   {u,v}\<inter>set2_lp_iterm (lp_isubst (combined_env (Inr slot)) sigma)={}"
  if member: "(slot,shape)\<in>set specs" for slot shape
 proof -
  have known: "lpp_runtime_leaf_effect A shape (combined_env (Inr slot))"
   using caller_leaf member by (auto simp: lpp_leaf_stack_invariant_def list_all_iff)
  show ?thesis using lpp_acquired_univ_caller_protection[OF acquired mgu matching finite_call finite_rest
    known runtime_coverage[OF member] ground] by (auto simp: vars)
 qed

 have resolved: "lpp_finite_goals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t rho)) bs @
   map (lp_cut_map (\<lambda>t. lp_isubst t sigma))
    (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t (?R combined_env))) rest))"
  by (rule lpp_matching_head_resolution_finite[OF mgu matching finite_call finite_rest])
 have entry_finite: "lpp_finite_execution (lpc_attach_answers rest (lpc_reinterface ?R runtime))"
  using resolved saved_finite
  by (auto simp: shape body_shape pending_shape constructor lpc_reinterface_def lpc_attach_answers_def
    lpp_finite_execution_def lpp_finite_goals_def lpp_argument_list_finite
    lp_cut_map_comp lp_ieval_subst o_def)
 have entry_leaf: "lpp_leaf_stack_invariant A specs (lpc_reinterface ?R runtime)"
  using caller_leaf protected
  by (auto simp: shape lpc_reinterface_def lpp_leaf_stack_invariant_def list_all_iff)
 have entry: "lpp_observer_invariant A specs rest runtime"
  using entry_finite entry_leaf by (simp add: lpp_observer_invariant_def)
 show ?thesis by (rule entry)
qed

lemma lpp_acquired_normalized_univ_product:
 fixes SP :: "string lpp_success_clause list"
 and combined_env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes acquired: "lpp_check_fresh_univ_clause h bs x y z"
 and mgu: "lpc_mgu_resolve a
   (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t (\<lambda>slot. combined_env (Inr slot)))) rest)
   h bs sigma rho"
 and matching: "lp_ieval h witness=a"
 and incoming: "lpp_observer_invariant A specs rest
   ((LPCClause (LPCAtom a#gs) c mark,combined_env)#saved)"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and ground: "\<And>v. v\<in>A \<Longrightarrow> vars_term v={}"
 and constructor: "rho x=LPIFun f ts"
 and body_shape: "bs=LPCAtom (Fun (LPCUser ''2:=..'')
   [Var x,Fun (LPCUser ''2:prolog_data_2e'') [Var y,Var z]])#body_tail"
 and pending_shape: "pending=map (lp_cut_bind mark (\<lambda>t. lp_ieval t rho)) body_tail @
   map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs"
 and tail: "pending\<noteq>[]"
 and shape: "runtime=(LPCGoals (LPCUnify (rho x) (rho x)#
   LPCUnify (LPIFun (LPCUser ''2:prolog_data_2e'') [rho y,rho z])
    (lpp_argument_list (LPIFun (names f) []#ts))#pending),
    case_sum helper_env (\<lambda>slot. lp_isubst (combined_env (Inr slot)) sigma))#saved"
 and first: "lpp_domain_answers P B U D
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env slot. env (Inr slot)) runtime)) first_event middle"
 and second: "lpp_domain_answers P B U D middle second_event result"
 and program: "lp_cut_source_program P"
 and coverage: "\<And>i (eta :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm). i<length nds \<Longrightarrow>
   lpp_observer_continuing_equality_frame (lpc_return_eval eta (states!i)) \<Longrightarrow>
   lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functors
    node_conditions lpp_finite_execution i"
 and represented: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functors
   node_conditions (lpc_reinterface (\<lambda>env slot. env (Inl slot)) runtime) subject"
 shows "first_event=None \<and> second_event=None \<and> (\<exists>joint_result target.
   result=lpc_attach_answers rest (lpc_reinterface (\<lambda>env slot. env (Inr slot)) joint_result) \<and>
   lpp_observer_invariant A specs rest joint_result \<and>
   (subject,target)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functors
    node_conditions (lpc_reinterface (\<lambda>env slot. env (Inl slot)) joint_result) target)"
proof -
 let ?R = "\<lambda>env slot. env (Inr slot)"
 have finite_call: "lpp_finite_term a"
 and finite_rest: "lpp_finite_goals
   (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t (?R combined_env))) rest)"
 and saved_finite: "lpp_finite_execution (lpc_attach_answers rest (lpc_reinterface ?R saved))"
 and caller_leaf: "lpp_leaf_stack_invariant A specs
   ((LPCClause (LPCAtom a#gs) c mark,?R combined_env)#lpc_reinterface ?R saved)"
  using incoming by (auto simp: lpp_observer_invariant_def lpc_reinterface_def
   lpc_attach_answers_def lpp_finite_execution_def lpp_finite_goals_def)
 have live: "set (map fst specs) \<subseteq>
   (\<Union>g\<in>set rest. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
  by (rule lpp_check_attached_leaf_slots_sound[OF covered])
 have runtime_coverage: "set2_lp_iterm (combined_env (Inr slot)) \<subseteq>
   (\<Union>g\<in>set (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t (\<lambda>slot. combined_env (Inr slot)))) rest).
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
  using lpp_check_fresh_univ_clause_sound[OF acquired mgu finite_subst] by blast
 have input_member: "x\<in>vars_term h"
  using acquired by (auto simp: lpp_check_fresh_univ_clause_def lpp_check_fresh_decomposition_def)
 have finite_input: "lpp_finite_term (rho x)"
  by (rule lpp_finite_eval_variable[OF input_member finite_head])
 have finite: "list_all lpp_finite_term ts" using finite_input constructor by simp
 have protected: "lpp_runtime_leaf_effect A shape (lp_isubst (combined_env (Inr slot)) sigma) \<and>
   {u,v}\<inter>set2_lp_iterm (lp_isubst (combined_env (Inr slot)) sigma)={}"
  if member: "(slot,shape)\<in>set specs" for slot shape
 proof -
  have known: "lpp_runtime_leaf_effect A shape (combined_env (Inr slot))"
   using caller_leaf member by (auto simp: lpp_leaf_stack_invariant_def list_all_iff)
  show ?thesis using lpp_acquired_univ_caller_protection[OF acquired mgu matching finite_call finite_rest
    known runtime_coverage[OF member] ground] by (auto simp: vars)
 qed

 have entry: "lpp_observer_invariant A specs rest runtime"
  by (rule lpp_acquired_normalized_entry_invariant[where names=names and helper_env=helper_env and runtime=runtime and pending=pending and rho=rho and sigma=sigma and x=x and y=y and z=z, OF acquired mgu matching incoming
    covered ground constructor body_shape pending_shape tail shape])
 show ?thesis
  apply (rule lpp_normalized_univ_observer_product[where SP=SP and x=u and y=v,
   OF shape[unfolded constructor vars] tail entry covered distinct fresh[unfolded constructor] _
    first second program _ represented])
  subgoal using protected by simp
  subgoal for i eta by (rule coverage[of i eta]) assumption+
  done
qed

ML \<open>
val checked = @{thms lpp_acquired_normalized_entry_invariant lpp_acquired_normalized_univ_product};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted acquired univ product" else ();
val _ = writeln "ACQUIRED_UNIV_PRODUCT_KERNEL_CHECKED";
\<close>
end
