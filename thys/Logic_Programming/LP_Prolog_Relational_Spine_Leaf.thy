theory LP_Prolog_Relational_Spine_Leaf
 imports LP_Prolog_Relational_Matching_Leaf
begin
lemma lpp_relational_spine_leaf_base_step:
 assumes step: "lpc_answer_transition P
   (lpc_return_eval eta ((LPCClause (LPCAtom (Fun f (arg#actuals))#gs) c m,payload)#saved)) event tt"
 and invariant: "lpp_leaf_stack_invariant {u. vars_term u={}} specs
   (lpc_return_eval eta ((LPCClause (LPCAtom (Fun f (arg#actuals))#gs) c m,payload)#saved))"
 and coverage: "lpp_check_relational_leaf_coverage facts (map fst specs) payload (Fun f (arg#actuals)) gs"
 and facts: "list_all (lpp_functor_fact_holds names eta) facts"
 and head: "fst (P!c)=Fun f (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y]#map Var H)"
 and distinct: "distinct (x#y#H)"
 and lengths: "length H=length actuals"
 and spine: "lpp_list_length (lp_ieval arg eta) n"
 and finite_call: "lpp_finite_term (lp_ieval (Fun f (arg#actuals)) eta)"
 and finite_rest: "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
 shows "lpp_leaf_stack_invariant {u. vars_term u={}} specs tt"
proof (rule lpp_leaf_stack_base_step[OF step invariant])
 fix a qs d n ret es sigma rho
 assume shape: "lpc_return_eval eta ((LPCClause (LPCAtom (Fun f (arg#actuals))#gs) c m,payload)#saved) =
   (LPCClause (LPCAtom a#qs) d n,ret)#es"
 and bound: "d<length P"
 and mgu: "lpc_mgu_resolve a qs (fst (P!d)) (snd (P!d)) sigma rho"
 have actual_mgu: "lpc_mgu_resolve (lp_ieval (Fun f (arg#actuals)) eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) (fst (P!c)) (snd (P!c)) sigma rho"
  using mgu shape by (auto simp: lpc_return_eval_def)
 have runtime_mgu: "lpc_mgu_resolve (LPIFun f (lp_ieval arg eta#map (\<lambda>t. lp_ieval t eta) actuals))
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)
   (Fun f (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y]#map Var H)) (snd (P!c)) sigma rho"
  using actual_mgu head by simp
 have runtime_lengths: "length H=length (map (\<lambda>t. lp_ieval t eta) actuals)" using lengths by simp
 obtain nu where matched: "lp_ieval (fst (P!c)) nu=lp_ieval (Fun f (arg#actuals)) eta"
  using lpp_spine_head_matching_witness[OF spine runtime_mgu distinct runtime_lengths]
  by (auto simp: head)
 have ret: "ret=lpc_return_env payload eta"
  using shape by (simp add: lpc_return_eval_def)
 show "lpp_leaf_environment_transport {u. vars_term u={}} specs ret sigma"
  unfolding ret by (rule lpp_relational_matching_leaf_transport[OF coverage facts actual_mgu matched finite_call finite_rest])
qed (auto simp: lpc_return_eval_def)

lemma lpp_relational_leaf_empty_separation_spine_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_resolution_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (Fun f (arg#actuals)) gs c m active saved k l A next anchors resolution_bindings mode outputs (contexts!i) (functor_contexts!i) yes no"
 and shape: "states!i=((LPCClause (LPCAtom (Fun f (arg#actuals))#gs) c m,active)#saved)"
 and head: "fst (P!c)=Fun f (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y]#map Var H)"
 and distinct: "distinct (x#y#H)"
 and lengths: "length H=length actuals"
 and spine: "LPPOShape lpp_spine_grammar (LPReturnShape 0) arg\<in>set (snd (snd (contexts!i)))"
 and coverage: "lpp_check_relational_leaf_coverage (functor_contexts!i) (map fst specs) active (Fun f (arg#actuals)) gs"
 and success_target: "mode\<noteq>LPCAlwaysFailure \<Longrightarrow> lpp_empty_separation_target separation_contexts yes"
 and failure_target: "mode\<noteq>LPCAlwaysSuccess \<Longrightarrow> lpp_empty_separation_target separation_contexts no"
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts (lpp_separation_node_conditions separation_contexts)
   (\<lambda>ss. lpp_finite_execution ss \<and> lpp_leaf_stack_invariant {u. vars_term u={}} specs ss) returned arity i"
proof (rule lpp_empty_separation_resolution_node_contract[OF compatible transfer checked shape success_target failure_target])
 fix eta ev ys
 assume conditions: "lpp_separation_node_conditions separation_contexts i eta"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and step: "lpc_answer_transition P (lpc_return_eval eta (states!i)) ev ys"
 and invariant: "lpp_finite_execution (lpc_return_eval eta (states!i)) \<and>
   lpp_leaf_stack_invariant {u. vars_term u={}} specs (lpc_return_eval eta (states!i))"
 have finite: "lpp_finite_execution (lpc_return_eval eta (states!i))" using invariant by simp
 have observed_shape: "lp_return_shape_holds lpp_spine_grammar (LPReturnShape 0) (lp_ieval arg eta)"
  using spine observed by (cases "contexts!i")
   (auto simp: lpp_stable_context_holds_def lpp_evaluation_context_holds_def list_all_iff)
 obtain n where runtime_spine: "lpp_list_length (lp_ieval arg eta) n"
  using lpp_return_shape_list_length[OF observed_shape] by blast
 have after_finite: "lpp_finite_execution ys"
  using lpp_finite_spine_resolution_base_step[OF _ _ head distinct lengths runtime_spine] step finite
  by (simp add: shape lpc_return_eval_def)
 have call_finite: "lpp_finite_term (lp_ieval (Fun f (arg#actuals)) eta)"
  and rest_finite: "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
  using finite by (auto simp: shape lpc_return_eval_def lpp_finite_execution_def lpp_finite_goals_def)
 have after_leaf: "lpp_leaf_stack_invariant {u. vars_term u={}} specs ys"
  by (rule lpp_relational_spine_leaf_base_step[OF _ _ coverage functors head distinct lengths runtime_spine call_finite rest_finite])
    (use step invariant in \<open>auto simp: shape\<close>)
 show "lpp_finite_execution ys \<and> lpp_leaf_stack_invariant {u. vars_term u={}} specs ys"
  using after_finite after_leaf by simp
qed

ML \<open>
val checked = @{thms lpp_relational_spine_leaf_base_step lpp_relational_leaf_empty_separation_spine_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted relational spine leaf" else ();
\<close>
end
