theory LP_Prolog_Separation_Finite_Control
 imports LP_Prolog_Separation_Builtin_Contracts LP_Prolog_Separation_Control_Reductions
begin

lemma lpp_finite_separation_is_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts (nds!i) (Fs!i) (states!i)
   (contexts!i) (functor_contexts!i) returned arity (LPPFIs result_var middle facts)"
 and shape: "(states!i)=((LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved)"

 and separation_bound: "lpcl_target middle<length separation_contexts"
 and separation_empty: "separation_contexts!lpcl_target middle=[]"
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts (lpp_separation_node_conditions separation_contexts) lpp_finite_execution returned arity i"
 by (rule lpp_separation_is_node_contract[OF compatible transfer checked shape separation_bound separation_empty])
   (simp only: shape; rule lpp_finite_execution_is_normalization; assumption)

lemma lpp_finite_separation_trim_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity
   (LPPFTrim successor barriers e fs)"
 and bound: "lpcl_target e<length separation_contexts"
 and empty: "separation_contexts!lpcl_target e=[]"
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts (lpp_separation_node_conditions separation_contexts)
   lpp_finite_execution returned arity i"
 by (rule lpp_separation_trim_node_contract[OF compatible transfer checked bound empty])
   (auto simp: lpp_finite_execution_def list_all_iff)

lemma lpp_finite_separation_parallel_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity (LPPFParallel links factss)"
 and empty_targets: "\<And>j. j<length (states!i) \<Longrightarrow>
   lpcl_target (links!j)<length separation_contexts \<and> separation_contexts!lpcl_target (links!j)=[]"
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts (lpp_separation_node_conditions separation_contexts)
   lpp_finite_execution returned arity i"
 by (rule lpp_separation_parallel_node_contract[OF compatible transfer checked empty_targets])
   (auto simp: lpp_finite_execution_def list_all_iff)

lemma lpp_finite_separation_test_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity (LPPFTest yes no yes_facts no_facts)"
 and shape: "states!i=((LPCGoals (LPCAtom (Fun (LPCUser f) [a])#gs),active)#saved)"
 and empty_targets: "\<And>holds. holds\<in>set (lpp_var_outcomes f (lpcn_ground (nds!i)) a) \<Longrightarrow>
   lpcl_target (if holds then yes else no)<length separation_contexts \<and>
   separation_contexts!lpcl_target (if holds then yes else no)=[]"
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts (lpp_separation_node_conditions separation_contexts)
   lpp_finite_execution returned arity i"
proof -
 have name: "lpp_var_name f"
  using checked by (auto simp: shape lpp_check_functor_source_action_def lpp_check_functor_term_test_def)
 show ?thesis
  apply (rule lpp_separation_test_node_contract[OF compatible transfer checked shape])
  subgoal by (rule empty_targets; assumption)
  subgoal by (simp only: shape; rule lpp_finite_functor_test_step[OF name]; assumption)
  done
qed

ML \<open>
val checked = @{thms lpp_finite_separation_is_node_contract lpp_finite_separation_trim_node_contract
 lpp_finite_separation_parallel_node_contract lpp_finite_separation_test_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite separation control" else ();
\<close>
end
