theory LP_Prolog_Observer_Univ_Module
 imports LP_Prolog_Observer_Univ_Frame
begin

lemma lpp_checked_univ_module_step:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and program: "lp_cut_source_program P"
 and equality_coverage: "\<And>j (nu :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm). j<length nds \<Longrightarrow>
   lpp_observer_equality_frame (lpc_return_eval nu (states!j)) \<Longrightarrow>
   lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) lpp_finite_execution j"
 and univ_coverage: "\<And>i (eta :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm). i<length nds \<Longrightarrow>
   lpp_observer_univ_frame (lpc_return_eval eta (states!i)) \<Longrightarrow>
   \<exists>value_var name_var args_var middle facts pair_symbol output_name output_args.
    lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
     (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity
     (LPPFUniv value_var name_var args_var middle facts) \<and>
    lpp_check_separation_univ separation_contexts i (states!i) name_var args_var middle pair_symbol output_name output_args"
 and represented: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) xs t"
 and finite: "lpp_finite_execution xs"
 and frame: "lpp_observer_univ_frame xs"
 and step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain xs ev ys"
 shows "ev=None \<and> (ys=[] \<or> (\<exists>u. (t,u)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) ys u))"
proof (rule lpp_observer_domain_module_step[where eligible=lpp_observer_univ_frame and node_conditions="lpp_separation_node_conditions separation_contexts", OF program _ _ represented finite frame step])
 show "\<And>swaps xs. lpp_observer_univ_frame xs \<Longrightarrow> lpp_observer_univ_frame (lpc_return_scope_word swaps xs)"
  by (simp add: lpp_observer_univ_frame_scopes)
next
 fix i eta ev ys
 assume bound: "i<length nds"
 and frame: "lpp_observer_univ_frame (lpc_return_eval eta (states!i))"
 and conditions: "lpp_separation_node_conditions separation_contexts i eta"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and finite: "lpp_finite_execution (lpc_return_eval eta (states!i))"
 and actual: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
    (lpc_return_eval eta (states!i)) ev ys"
 obtain value_var name_var args_var middle facts pair_symbol output_name output_args where
 check: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
     (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity
     (LPPFUniv value_var name_var args_var middle facts)"
 and extra: "lpp_check_separation_univ separation_contexts i (states!i) name_var args_var middle pair_symbol output_name output_args"
  using univ_coverage[OF bound frame] by blast
 show "ev=None \<and> (ys=[] \<or> (\<exists>u.
   ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) ys u))"
  apply (rule lpp_checked_separation_univ_source_step[OF compatible transfer check extra program _
    conditions known free observed functors finite actual])
  subgoal for j nu by (rule equality_coverage[of j nu]) assumption+
  done
qed
end
