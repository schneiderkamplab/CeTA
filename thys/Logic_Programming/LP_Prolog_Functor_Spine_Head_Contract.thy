theory LP_Prolog_Functor_Spine_Head_Contract
 imports LP_Prolog_Functor_Anchored_Contract LP_Prolog_Spine_Shape
begin

text \<open>A checked proper-spine observation supplies the linear cons-head
  premise. Finite execution is still required: a proper spine alone says
  nothing about cyclic elements or later helper returns.\<close>

lemma lpp_finite_spine_resolution_base_step:
 assumes step: "lpc_answer_transition P
   ((LPCClause (LPCAtom (lp_ieval (Fun f (arg#actuals)) eta)#gs) c m,ret)#saved) event tt"
 and finite: "lpp_finite_execution
   ((LPCClause (LPCAtom (lp_ieval (Fun f (arg#actuals)) eta)#gs) c m,ret)#saved)"
 and head: "fst (P!c)=Fun f (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y]#map Var H)"
 and distinct: "distinct (x#y#H)"
 and lengths: "length H=length actuals"
 and spine: "lpp_list_length (lp_ieval arg eta) n"
 shows "lpp_finite_execution tt"
proof (rule lpp_finite_base_answer_step[OF step finite])
 fix a' gs' c' m' eta' es sigma rho
 assume shape: "((LPCClause (LPCAtom (lp_ieval (Fun f (arg#actuals)) eta)#gs) c m,ret)#saved)=
   (LPCClause (LPCAtom a'#gs') c' m',eta')#es"
 and bound: "c'<length P"
 and mgu: "lpc_mgu_resolve a' gs' (fst (P!c')) (snd (P!c')) sigma rho"
 have actual_mgu: "lpc_mgu_resolve (LPIFun f (lp_ieval arg eta#map (\<lambda>t. lp_ieval t eta) actuals)) gs
   (Fun f (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y]#map Var H)) (snd (P!c)) sigma rho"
  using mgu shape head by auto
 have finite_call: "lpp_finite_term (LPIFun f (lp_ieval arg eta#map (\<lambda>t. lp_ieval t eta) actuals))"
 and continuation: "lpp_finite_goals gs"
  using finite by (auto simp: lpp_finite_execution_def lpp_finite_goals_def lp_cut_terms.simps)
 have runtime_lengths: "length H=length (map (\<lambda>t. lp_ieval t eta) actuals)" by (simp add: lengths)
 have finite_head: "lpp_finite_term (lp_ieval
   (Fun f (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y]#map Var H)) rho)"
  using lpp_list_head_finite_resolution[OF spine actual_mgu distinct runtime_lengths finite_call continuation] by blast
 show "lpp_finite_term (lp_ieval (fst (P!c')) rho)"
  using finite_head shape head by simp
qed auto

lemma lpp_finite_functor_spine_head_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity (LPPFCut action yes_facts no_facts)"
 and shape: "states!i=((LPCClause (LPCAtom (Fun f (arg#actuals))#gs) c m,active)#saved)"
 and head: "fst (P!c)=Fun f (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y]#map Var H)"
 and distinct: "distinct (x#y#H)"
 and lengths: "length H=length actuals"
 and spine: "LPPOShape lpp_spine_grammar (LPReturnShape 0) arg\<in>set (snd (snd (contexts!i)))"
 shows "lpp_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
   lpp_finite_execution returned arity i"
proof (rule lpp_functor_contextual_cut_node_contract[OF compatible transfer checked])
 fix eta ev ys
 assume known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_return_eval eta (states!i)) ev ys"
 and finite: "lpp_finite_execution (lpc_return_eval eta (states!i))"
 have observed_shape: "lp_return_shape_holds lpp_spine_grammar (LPReturnShape 0) (lp_ieval arg eta)"
  using spine observed by (cases "contexts!i")
   (auto simp: lpp_stable_context_holds_def lpp_evaluation_context_holds_def list_all_iff)
 obtain n where runtime_spine: "lpp_list_length (lp_ieval arg eta) n"
  using lpp_return_shape_list_length[OF observed_shape] by blast
 have clear: "lpp_no_builtin_frame (states!i)" by (simp add: shape)
 have supported: "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_univ_source_domain (map fst (lpc_return_eval eta (states!i)))"
  by (rule lpp_no_builtin_domain_bad[OF lpp_no_builtin_frame_sound[OF clear]])
 have actual: "lpp_answer_transition P lpp_builtin_signature (lpp_univ_source_builtin names operation)
   (lpc_return_eval eta (states!i)) ev ys"
  using step supported by (simp add: lpp_domain_answers_def)
 have base: "lpc_answer_transition P (lpc_return_eval eta (states!i)) ev ys"
  by (rule lpp_univ_source_nonbuiltin_base[OF clear actual])
 show "lpp_finite_execution ys"
  using lpp_finite_spine_resolution_base_step[OF _ _ head distinct lengths runtime_spine] base finite
  by (simp add: shape lpc_return_eval_def)
qed

lemma lpp_spine_head_missing_observation_rejected:
 "LPPOShape lpp_spine_grammar (LPReturnShape 0) arg\<notin>set ([]::string lpp_numeric_observation list)"
 by simp

ML \<open>
val checked = @{thms lpp_finite_spine_resolution_base_step lpp_finite_functor_spine_head_node_contract
 lpp_spine_head_missing_observation_rejected};
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
 exists (fn n => not (member (op =) inherited n)) (oracles checked)
 then error "Untrusted spine head contract dependency" else ();
\<close>
end
