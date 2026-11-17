theory LP_Prolog_Finite_Functor_Normalization
 imports LP_Prolog_Functor_Table_Contract LP_Prolog_Finite_Execution_Step
begin

text \<open>Discharge the normalization invariant at actual source operations.
No unification, return contract or termination obligation is discharged here.\<close>

lemma lpp_finite_execution_is_normalization:
 assumes finite: "lpp_finite_execution (lpc_return_eval eta
   ((LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved))"
 shows "lpp_finite_execution ((LPCGoals
   (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser f) [])#
    map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),lpc_return_env active eta)#lpc_return_eval eta saved)"
 using finite
 by (auto simp: lpp_finite_execution_def lpc_return_eval_def lpp_finite_goals_def lp_cut_terms.simps)

lemma lpp_finite_execution_univ_normalization:
 assumes input: "lp_ieval a eta=LPIFun f ts"
 and finite: "lpp_finite_execution (lpc_return_eval eta
   ((LPCGoals (LPCAtom (Fun (LPCUser ''2:=..'') [a,b])#gs),active)#saved))"
 shows "lpp_finite_execution ((LPCGoals (LPCUnify (LPIFun f ts) (LPIFun f ts)#
   LPCUnify (lp_ieval b eta) (lpp_argument_list (LPIFun (names f) []#ts))#
   map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),lpc_return_env active eta)#lpc_return_eval eta saved)"
 using finite input
 by (auto simp: lpp_finite_execution_def lpc_return_eval_def lpp_finite_goals_def
   lp_cut_terms.simps lpp_argument_list_finite)

lemma lpp_finite_functor_is_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts (nds!i) (Fs!i) (states!i)
   (contexts!i) (functor_contexts!i) returned arity (LPPFIs result_var middle facts)"
 and shape: "(states!i)=((LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved)"

 shows "lpp_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts lpp_finite_execution returned arity i"
 by (rule lpp_functor_is_node_contract[OF compatible transfer checked shape])
   (simp only: shape; rule lpp_finite_execution_is_normalization; assumption)

lemma lpp_finite_functor_univ_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts (nds!i) (Fs!i) (states!i)
   (contexts!i) (functor_contexts!i) returned arity (LPPFUniv value_var name_var args_var middle facts)"
 and shape: "(states!i)=((LPCGoals (LPCAtom (Fun (LPCUser ''2:=..'') [a,b])#gs),active)#saved)"

 shows "lpp_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts lpp_finite_execution returned arity i"
 by (rule lpp_functor_univ_node_contract[OF compatible transfer checked shape])
   (simp only: shape; rule lpp_finite_execution_univ_normalization; assumption)

theorem lpp_finite_functor_table_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes checked: "lpp_check_functor_control T fuel P Q nds states contexts Fs functor_contexts returned arity actions"
 and program: "lp_cut_source_program P"
 and local: "\<And>j action. j<length nds \<Longrightarrow> actions!j=Some action \<Longrightarrow>
   lpp_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts lpp_finite_execution returned arity j"
 and boundary: "\<And>j. j<length nds \<Longrightarrow> actions!j=None \<Longrightarrow>
   lpp_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts lpp_finite_execution returned arity j"
 and root: "i<length nds"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and invariant: "lpp_finite_execution (lpc_return_eval eta (states!i))"
 and residual: "SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]}"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_return_eval eta (states!i)) (lp_ild Q) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]
   (\<lambda>rho. [(returned,map rho [0..<arity])])"
 by (rule lpp_functor_table_contract[OF checked program _ local boundary root known free observed functors invariant residual])
   (simp add: lpp_finite_execution_scope_word)

ML \<open>
val checked = @{thms lpp_finite_execution_is_normalization lpp_finite_execution_univ_normalization};
val inherited = map (fst o fst) (Thm_Deps.all_oracles @{thms check_trs_termination_proof});
val contracts = @{thms lpp_finite_functor_table_contract lpp_finite_functor_is_node_contract lpp_finite_functor_univ_node_contract};
val _ = if Thm_Deps.has_skip_proof contracts orelse
 exists (fn n => not (member (op =) inherited n)) (map (fst o fst) (Thm_Deps.all_oracles contracts))
 then error "Untrusted finite functor node contract" else ();
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite functor normalization" else ();
\<close>
end
