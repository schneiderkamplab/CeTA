theory LP_Prolog_Separation_Finite_Unification
 imports LP_Prolog_Separation_Empty_Unification
begin

lemma lpp_finite_empty_separation_ground_equality_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_equality_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) a b gs active saved k l next mode outputs (contexts!i) (functor_contexts!i) yes no"
 and shape: "states!i=((LPCGoals (LPCUnify a b#gs),active)#saved)"
 and ground: "vars_term b \<subseteq> set (lpcn_ground (nds!i)) \<union> lpp_source_context_ground (contexts!i)"
 and success_target: "mode\<noteq>LPCAlwaysFailure \<Longrightarrow> lpp_empty_separation_target separation_contexts yes"
 and failure_target: "mode\<noteq>LPCAlwaysSuccess \<Longrightarrow> lpp_empty_separation_target separation_contexts no"
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts (lpp_separation_node_conditions separation_contexts)
   lpp_finite_execution returned arity i"
proof (rule lpp_empty_separation_equality_node_contract[OF compatible transfer checked shape success_target failure_target])
 fix eta ev ys
 assume conditions: "lpp_separation_node_conditions separation_contexts i eta"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and step: "lpc_answer_transition P (lpc_return_eval eta (states!i)) ev ys"
 and finite: "lpp_finite_execution (lpc_return_eval eta (states!i))"
 have runtime_ground: "lp_seg_ground (lp_ieval b eta)"
  using ground known lpp_stable_context_ground_sound[OF observed]
  by (auto simp: lp_seg_ground_eval lp_cut_knowledge_def)
 show "lpp_finite_execution ys"
  using lpp_finite_ground_equality_base_step[OF _ _ runtime_ground] step finite
  by (simp add: shape lpc_return_eval_def)
qed

lemma lpp_finite_empty_separation_matching_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_resolution_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (a) gs c m active saved k l A next anchors resolution_bindings mode outputs (contexts!i) (functor_contexts!i) yes no"
 and shape: "states!i=((LPCClause (LPCAtom a#gs) c m,active)#saved)"
 and matching: "lp_cut_check_match a (fst (P!c)) bindings"
 and success_target: "mode\<noteq>LPCAlwaysFailure \<Longrightarrow> lpp_empty_separation_target separation_contexts yes"
 and failure_target: "mode\<noteq>LPCAlwaysSuccess \<Longrightarrow> lpp_empty_separation_target separation_contexts no"
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts (lpp_separation_node_conditions separation_contexts)
   lpp_finite_execution returned arity i"
proof (rule lpp_empty_separation_resolution_node_contract[OF compatible transfer checked shape success_target failure_target])
 fix eta ev ys
 assume conditions: "lpp_separation_node_conditions separation_contexts i eta"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and step: "lpc_answer_transition P (lpc_return_eval eta (states!i)) ev ys"
 and finite: "lpp_finite_execution (lpc_return_eval eta (states!i))"
 show "lpp_finite_execution ys"
  using lpp_finite_matching_resolution_base_step[OF _ _ matching] step finite
  by (simp add: shape lpc_return_eval_def)
qed

lemma lpp_finite_empty_separation_anchored_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_resolution_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (Fun f actuals) gs c m active saved k l A next anchors resolution_bindings mode outputs (contexts!i) (functor_contexts!i) yes no"
 and shape: "states!i=((LPCClause (LPCAtom (Fun f actuals)#gs) c m,active)#saved)"
 and head: "fst (P!c)=Fun f hs"
 and lengths: "length actuals=length hs"
 and anchored: "lpp_check_anchored_head G actuals hs"
 and ground: "set G \<subseteq> set (lpcn_ground (nds!i)) \<union> lpp_source_context_ground (contexts!i)"
 and success_target: "mode\<noteq>LPCAlwaysFailure \<Longrightarrow> lpp_empty_separation_target separation_contexts yes"
 and failure_target: "mode\<noteq>LPCAlwaysSuccess \<Longrightarrow> lpp_empty_separation_target separation_contexts no"
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts (lpp_separation_node_conditions separation_contexts)
   lpp_finite_execution returned arity i"
proof (rule lpp_empty_separation_resolution_node_contract[OF compatible transfer checked shape success_target failure_target])
 fix eta ev ys
 assume conditions: "lpp_separation_node_conditions separation_contexts i eta"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and step: "lpc_answer_transition P (lpc_return_eval eta (states!i)) ev ys"
 and finite: "lpp_finite_execution (lpc_return_eval eta (states!i))"
 have runtime_ground: "lp_seg_ground (eta x)" if "x\<in>set G" for x
  using ground known lpp_stable_context_ground_sound[OF observed] that
  by (auto simp: lp_cut_knowledge_def)
 show "lpp_finite_execution ys"
  using lpp_finite_anchored_resolution_base_step[OF _ _ head lengths anchored runtime_ground] step finite
  by (simp add: shape lpc_return_eval_def)
qed

lemma lpp_finite_empty_separation_spine_head_node_contract:
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
 and success_target: "mode\<noteq>LPCAlwaysFailure \<Longrightarrow> lpp_empty_separation_target separation_contexts yes"
 and failure_target: "mode\<noteq>LPCAlwaysSuccess \<Longrightarrow> lpp_empty_separation_target separation_contexts no"
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts (lpp_separation_node_conditions separation_contexts)
   lpp_finite_execution returned arity i"
proof (rule lpp_empty_separation_resolution_node_contract[OF compatible transfer checked shape success_target failure_target])
 fix eta ev ys
 assume conditions: "lpp_separation_node_conditions separation_contexts i eta"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and step: "lpc_answer_transition P (lpc_return_eval eta (states!i)) ev ys"
 and finite: "lpp_finite_execution (lpc_return_eval eta (states!i))"
 have observed_shape: "lp_return_shape_holds lpp_spine_grammar (LPReturnShape 0) (lp_ieval arg eta)"
  using spine observed by (cases "contexts!i")
   (auto simp: lpp_stable_context_holds_def lpp_evaluation_context_holds_def list_all_iff)
 obtain n where runtime_spine: "lpp_list_length (lp_ieval arg eta) n"
  using lpp_return_shape_list_length[OF observed_shape] by blast
 show "lpp_finite_execution ys"
  using lpp_finite_spine_resolution_base_step[OF _ _ head distinct lengths runtime_spine] step finite
  by (simp add: shape lpc_return_eval_def)
qed

ML \<open>
val checked = @{thms lpp_finite_empty_separation_ground_equality_node_contract lpp_finite_empty_separation_matching_node_contract lpp_finite_empty_separation_anchored_node_contract lpp_finite_empty_separation_spine_head_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite separation unification" else ();
\<close>
end
