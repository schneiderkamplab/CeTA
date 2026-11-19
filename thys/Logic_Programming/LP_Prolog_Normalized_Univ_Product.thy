theory LP_Prolog_Normalized_Univ_Product
 imports LP_Prolog_Acquired_Univ_Witness LP_Prolog_Observer_Continuing_Module
  LP_Prolog_Observer_Finite_Helper
begin

text \<open>Compose normalized equality simulation with the restricted caller
invariant on the same joint execution. Initial representation and caller
protection are explicit inputs supplied by acquisition assembly.\<close>

lemma lpp_normalized_univ_observer_product:
 fixes SP :: "string lpp_success_clause list"
 and combined_env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes shape: "runtime=(LPCGoals (LPCUnify (LPIFun f ts) (LPIFun f ts)#
   LPCUnify (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y])
    (lpp_argument_list (LPIFun (names f) []#ts))#pending),combined_env)#saved"
 and tail: "pending\<noteq>[]"
 and invariant: "lpp_observer_invariant A specs rest runtime"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and distinct: "x\<noteq>y"
 and fresh: "x\<notin>set2_lp_iterm (LPIFun f ts)" "y\<notin>set2_lp_iterm (LPIFun f ts)"
 and protected: "\<And>slot sh. (slot,sh)\<in>set specs \<Longrightarrow>
   {x,y}\<inter>set2_lp_iterm (combined_env (Inr slot))={}"
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
 let ?T = "lpp_domain_answers P B U D"
 let ?L = "\<lambda>env slot. env (Inl slot)"
 let ?R = "\<lambda>env slot. env (Inr slot)"
 have active: "lpc_prefix_active runtime" by (simp add: shape)
 obtain joint_middle where silent1: "first_event=None"
 and joint_first: "?T runtime None joint_middle"
 and helper_first: "?T (lpc_reinterface ?L runtime) None (lpc_reinterface ?L joint_middle)"
 and middle_eq: "middle=lpc_attach_answers rest (lpc_reinterface ?R joint_middle)"
  using lpp_attached_observer_product_step[OF active first] by blast
 have joint_base: "lpc_answer_transition P runtime None joint_middle"
  using joint_first by (auto simp: shape intro: lpp_observer_equality_base)
 obtain subst where middle_shape: "joint_middle=
   (LPCGoals (LPCUnify
     (lp_isubst (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y]) subst)
     (lp_isubst (lpp_argument_list (LPIFun (names f) []#ts)) subst)#
     map (lp_cut_map (\<lambda>t. lp_isubst t subst)) pending),
     \<lambda>slot. lp_isubst (combined_env slot) subst)#saved"
  using joint_base[unfolded shape]
  by (cases rule: lpc_answer_transition.cases) auto
 have middle_frame: "lpp_observer_continuing_equality_frame (lpc_reinterface ?L joint_middle)"
  using tail by (cases pending) (simp_all add: middle_shape lpc_reinterface_def)
 have middle_active: "lpc_prefix_active joint_middle"
  by (simp add: middle_shape)
 obtain joint_result where silent2: "second_event=None"
 and helper_second: "?T (lpc_reinterface ?L joint_middle) None (lpc_reinterface ?L joint_result)"
 and result_eq: "result=lpc_attach_answers rest (lpc_reinterface ?R joint_result)"
  using lpp_attached_observer_product_step[OF middle_active second[unfolded middle_eq]] by blast
 have caller_first: "?T (lpc_attach_answers rest
   ((LPCGoals (LPCUnify (LPIFun f ts) (LPIFun f ts)#
     LPCUnify (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y])
       (lpp_argument_list (LPIFun (names f) []#ts))#pending),?R combined_env)#lpc_reinterface ?R saved)) first_event middle"
  using first by (simp add: shape lpc_reinterface_def)
 have finite: "lpp_finite_execution (lpc_attach_answers rest
   ((LPCGoals (LPCUnify (LPIFun f ts) (LPIFun f ts)#
     LPCUnify (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y])
       (lpp_argument_list (LPIFun (names f) []#ts))#pending),?R combined_env)#lpc_reinterface ?R saved))"
 and leaf: "lpp_leaf_stack_invariant A specs
   ((LPCGoals (LPCUnify (LPIFun f ts) (LPIFun f ts)#
     LPCUnify (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y])
       (lpp_argument_list (LPIFun (names f) []#ts))#pending),?R combined_env)#lpc_reinterface ?R saved)"
  using invariant by (simp_all add: lpp_observer_invariant_def shape lpc_reinterface_def)
 have preserved: "lpp_finite_execution result \<and> lpp_leaf_stack_invariant A specs result"
  using lpp_attached_univ_domain_invariants[where names=names and f=f and ts=ts
   and x=x and y=y and env="?R combined_env" and rest=rest and pending=pending,
   OF caller_first second leaf finite distinct fresh protected covered] by simp
 have joint_invariant: "lpp_observer_invariant A specs rest joint_result"
  using preserved by (simp add: result_eq lpp_observer_invariant_def lpp_leaf_stack_attachment)
 have finite_helper: "lpp_finite_execution (lpc_reinterface ?L runtime)"
  by (rule lpp_observer_invariant_finite_helper[OF invariant])
 have first_frame: "lpp_observer_continuing_equality_frame (lpc_reinterface ?L runtime)"
  by (simp add: shape lpc_reinterface_def)
 have first_base: "lpc_answer_transition P (lpc_reinterface ?L runtime) None (lpc_reinterface ?L joint_middle)"
  using helper_first by (auto simp: shape lpc_reinterface_def intro: lpp_observer_equality_base)
 have second_base: "lpc_answer_transition P (lpc_reinterface ?L joint_middle) None (lpc_reinterface ?L joint_result)"
  using helper_second middle_frame
  by (cases "lpc_reinterface ?L joint_middle" rule: lpp_observer_continuing_equality_frame.cases)
    (auto intro: lpp_observer_equality_base)
 obtain mid_subject where edge1: "(subject,mid_subject)\<in>(lp_ild Q)\<^sup>+"
 and mid_rep: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functors
   node_conditions (lpc_reinterface ?L joint_middle) mid_subject"
 and mid_finite: "lpp_finite_execution (lpc_reinterface ?L joint_middle)"
  using lpp_observer_continuing_equality_module_step[where node_conditions=node_conditions and SP=SP, OF program _ represented finite_helper first_frame first_base] coverage by blast
 obtain target where edge2: "(mid_subject,target)\<in>(lp_ild Q)\<^sup>+"
 and target_rep: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functors
   node_conditions (lpc_reinterface ?L joint_result) target"
  using lpp_observer_continuing_equality_module_step[where node_conditions=node_conditions and SP=SP, OF program _ mid_rep mid_finite middle_frame second_base] coverage by blast
 have edge: "(subject,target)\<in>(lp_ild Q)\<^sup>+"
  by (rule trancl_trans[OF edge1 edge2])
 show ?thesis unfolding silent1 silent2
  apply (intro conjI)
  apply simp
  apply simp
  apply (rule exI[of _ joint_result], rule exI[of _ target])
  using result_eq joint_invariant edge target_rep by blast
qed

ML \<open>
val checked = @{thms lpp_normalized_univ_observer_product};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted normalized observer product" else ();
val _ = writeln "NORMALIZED_UNIV_PRODUCT_KERNEL_CHECKED";
\<close>
end
