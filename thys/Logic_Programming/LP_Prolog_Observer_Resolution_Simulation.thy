theory LP_Prolog_Observer_Resolution_Simulation
 imports LP_Prolog_Observer_Univ_Module_Block LP_Prolog_Observer_Ground_Equality_Simulation
begin

lemma lpp_separation_resolution_node_simulation:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_resolution_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) a gs c m active saved k l A next anchors bindings mode outputs (contexts!i) (functor_contexts!i) yes no"
 and shape: "states!i=((LPCClause (LPCAtom a#gs) c m,active)#saved)"
 and success_transport: "mode\<noteq>LPCAlwaysFailure \<Longrightarrow>
   lpcl_target yes<length separation_contexts \<and>
   lpp_check_separation_transport yes_separation (separation_contexts!lpcl_target yes)
     (lp_cut_instance_subst (lpcl_bindings yes))"
 and failure_transport: "mode\<noteq>LPCAlwaysSuccess \<Longrightarrow>
   lpcl_target no<length separation_contexts \<and>
   lpp_check_separation_transport no_separation (separation_contexts!lpcl_target no)
     (lp_cut_instance_subst (lpcl_bindings no))"
 and success_separation: "\<And>eta sigma rho.
   lpp_separation_node_conditions separation_contexts i eta \<Longrightarrow>
   lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
   lpc_free_knowledge (set (Fs!i)) eta \<Longrightarrow>
   lpp_stable_context_holds operation SP (contexts!i) eta \<Longrightarrow>
   list_all (lpp_functor_fact_holds names eta) (functor_contexts!i) \<Longrightarrow>
   J (lpc_return_eval eta (states!i)) \<Longrightarrow>
   lpc_mgu_resolve (lp_ieval a eta) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) (fst (P!c)) (snd (P!c)) sigma rho \<Longrightarrow>
   list_all (lpp_separation_holds (lp_cut_resolution_env k l eta sigma rho)) yes_separation"
 and failure_separation: "\<And>eta :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm. lpp_separation_node_conditions separation_contexts i eta \<Longrightarrow>
   list_all (lpp_separation_holds eta) no_separation"
 and stable: "\<And>eta ev ys.
   lpp_separation_node_conditions separation_contexts i eta \<Longrightarrow>
   lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
   lpc_free_knowledge (set (Fs!i)) eta \<Longrightarrow>
   lpp_stable_context_holds operation SP (contexts!i) eta \<Longrightarrow>
   list_all (lpp_functor_fact_holds names eta) (functor_contexts!i) \<Longrightarrow>
   lpc_answer_transition P (lpc_return_eval eta (states!i)) ev ys \<Longrightarrow>
   J (lpc_return_eval eta (states!i)) \<Longrightarrow> J ys"
 shows "lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) J i"
 unfolding lpp_observer_node_simulation_def
proof (intro allI impI)
 fix eta ev ys
 assume conditions: "lpp_separation_node_conditions separation_contexts i eta"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and invariant: "J (lpc_return_eval eta (states!i))"
 and step: "lpc_answer_transition P (lpc_return_eval eta (states!i)) ev ys"
 have separation: "\<And>sigma rho. lpc_mgu_resolve (lp_ieval a eta) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) (fst (P!c)) (snd (P!c)) sigma rho \<Longrightarrow>
      list_all (lpp_separation_holds (lp_cut_resolution_env k l eta sigma rho)) yes_separation"
  by (rule success_separation[OF conditions known free observed functors invariant])
 have simulated: "ev=None \<and> (\<exists>u swaps.
    ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts
     (lpp_separation_node_conditions separation_contexts) (lpc_return_scope_word swaps ys) u)"
  by (rule lpp_separation_functor_resolution_node_sound[OF compatible transfer checked success_transport failure_transport
    separation failure_separation[OF conditions] known free observed functors step[unfolded shape]])
 have preserved: "J ys" by (rule stable[OF conditions known free observed functors step invariant])
 show "ev=None \<and> J ys \<and> (\<exists>u.
    ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
     (lpp_separation_node_conditions separation_contexts) ys u)"
  using simulated preserved by (auto simp: lpp_premised_functor_module_rep_def)
qed

end
