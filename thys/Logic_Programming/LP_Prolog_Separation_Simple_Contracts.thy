theory LP_Prolog_Separation_Simple_Contracts
 imports LP_Prolog_Premised_Base_Contract LP_Prolog_Separation_Empty_Actions LP_Prolog_Functor_Simple_Control
begin

lemma lpp_finite_separation_admin_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_admin_node T fs fuel Q nds states contexts Fs functor_contexts (nds!i) (Fs!i) (states!i)
   (contexts!i) (functor_contexts!i) returned arity event next e"
 and simple: "lpp_simple_control_frame (states!i)"
 and clear: "lpp_no_builtin_frame (states!i)"
 and bound: "lpcl_target e<length separation_contexts"
 and empty: "separation_contexts!lpcl_target e=[]"
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) lpp_finite_execution returned arity i"
proof (rule lpp_premised_functor_base_node_contract[OF clear])

 fix eta ev ys
 assume conditions: "lpp_separation_node_conditions separation_contexts i eta"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and finite: "lpp_finite_execution (lpc_return_eval eta (states!i))"
 and step: "lpc_answer_transition P (lpc_return_eval eta (states!i)) ev ys"
 have preserved: "lpp_finite_execution ys"
   by (rule lpp_finite_simple_base_step[OF _ step finite])
     (simp add: lpp_simple_control_frame_eval simple)
 show "(\<exists>v swaps. ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],v)\<in>(lp_ild Q)\<^sup>+ \<and>
      lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts (lpp_separation_node_conditions separation_contexts)
       (lpc_return_scope_word swaps ys) v) \<and>
   (\<forall>rho. ev=Some rho \<longrightarrow>
      ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*) \<and> lpp_finite_execution ys"
   using lpp_empty_separation_admin_node_sound[OF compatible transfer checked bound empty known free observed functors step] preserved by blast
qed

lemma lpp_finite_separation_case_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_case_node T fs fuel P Q nds states contexts Fs functor_contexts (nds!i) (Fs!i)
   (contexts!i) (functor_contexts!i) m f ts gs active saved e"
 and shape: "states!i=((LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved)"
 and simple: "lpp_simple_control_frame (states!i)"
 and clear: "lpp_no_builtin_frame (states!i)"
 and bound: "lpcl_target e<length separation_contexts"
 and empty: "separation_contexts!lpcl_target e=[]"
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) lpp_finite_execution returned arity i"
proof (rule lpp_premised_functor_base_node_contract[OF clear])

 fix eta ev ys
 assume conditions: "lpp_separation_node_conditions separation_contexts i eta"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and finite: "lpp_finite_execution (lpc_return_eval eta (states!i))"
 and step: "lpc_answer_transition P (lpc_return_eval eta (states!i)) ev ys"
 have preserved: "lpp_finite_execution ys"
   by (rule lpp_finite_simple_base_step[OF _ step finite])
     (simp add: lpp_simple_control_frame_eval simple)
 show "(\<exists>v swaps. ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],v)\<in>(lp_ild Q)\<^sup>+ \<and>
      lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts (lpp_separation_node_conditions separation_contexts)
       (lpc_return_scope_word swaps ys) v) \<and>
   (\<forall>rho. ev=Some rho \<longrightarrow>
      ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*) \<and> lpp_finite_execution ys"
   using lpp_empty_separation_case_node_sound[OF compatible transfer checked bound empty known free observed functors step[unfolded shape]] preserved by auto
qed

ML \<open>
val checked = @{thms lpp_finite_separation_admin_node_contract lpp_finite_separation_case_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted separation simple node contracts" else ();
\<close>
end
