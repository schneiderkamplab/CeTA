theory LP_Prolog_Finite_Triple_Child
 imports LP_Prolog_Finite_Triple_Interface LP_Prolog_Evaluation_Transport LP_Prolog_Finite_Triple_Connection LP_Cut_SEG_Triple_Child
begin

definition lpp_finite_triple_check_child where
  "lpp_finite_triple_check_child T fs fuel roots contexts context pre G guards F vs inp out receipt =
    (lpcsh_target receipt<length roots \<and> lpcsh_target receipt<length contexts \<and>
      lpp_evaluation_context_transport T fs (lpp_context_add_ground context G) (contexts!lpcsh_target receipt) (lpcsh_bindings receipt) \<and>
      (let entry=roots!lpcsh_target receipt; nd=lpctr_node entry;
           mu=lp_cut_instance_subst (lpcsh_bindings receipt) in
       case lpcn_state nd of [ce] \<Rightarrow>
         (lpc_seg_check_instance_boundary (LPCGoals pre) G guards vs (map Var vs)
           ce (lpcn_ground nd) (lpcn_guards nd) (lpcn_vars nd)
           (lpcsh_bindings receipt) (lpcsh_swaps receipt) \<or>
          lpc_seg_check_instance_boundary (LPCGoals pre)
           (G @ filter (\<lambda>x. x\<in>lpp_source_context_ground context) vs) guards vs (map Var vs)
           ce (lpcn_ground nd) (lpcn_guards nd) (lpcn_vars nd)
           (lpcsh_bindings receipt) (lpcsh_swaps receipt)) \<and>
         lpc_check_link_free fuel [] F (lpctr_free entry) (lpcsh_bindings receipt) \<and>
         lp_atom_subst (lpctr_input entry) mu=inp \<and>
         lpc_triple_observe_atom (map (lpc_seg_position_template vs) (map mu (lpcn_vars nd)))
           (lpctr_output entry) =
         lpc_triple_observe_atom (map (lpc_seg_position_template vs) (map Var vs)) out
       | _ \<Rightarrow> False))"

theorem lpp_finite_triple_child_checked_lower:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
  assumes transfer: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_finite_triple_check_child T fs fuel roots contexts context pre G guards F vs inp out receipt"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set G) guards eta"
    and observed: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP context eta"
    and free: "lpc_free_knowledge (set F) eta"
    and edge: "(a,lp_atom_eval inp eta)\<in>lp_triple_calls (set D) Q"
    and lower: "\<And>us b ret. (a,b)\<in>lp_triple_calls (set D) Q \<Longrightarrow>
      lpp_finite_triple_root_rep SP contexts roots us b ret \<Longrightarrow> lpp_finite_triple_answer_contract P us Q ret"
  shows "lpp_finite_triple_answer_contract P (lpc_return_eval eta [(LPCGoals pre,map Var vs)]) Q (lp_atom_eval out)"
proof -
  let ?i = "lpcsh_target receipt"
  let ?entry = "roots!?i"
  let ?nd = "lpctr_node ?entry"
  let ?mu = "lp_cut_instance_subst (lpcsh_bindings receipt)"
  let ?eta = "\<lambda>x. lp_ieval (?mu x) eta"
  have index: "?i<length roots" "?i<length contexts"
    and transport: "lpp_evaluation_context_transport T fs (lpp_context_add_ground context G) (contexts!?i) (lpcsh_bindings receipt)"
    using checked by (auto simp: lpp_finite_triple_check_child_def)
  obtain ce where state: "lpcn_state ?nd=[ce]"
    using checked by (auto simp: lpp_finite_triple_check_child_def Let_def split: list.splits;
      metis list.exhaust)
  have context_ground: "\<forall>x\<in>lpp_source_context_ground context. lp_seg_ground (eta x)"
    by (rule lpp_evaluation_context_ground_sound[OF lpp_finite_evaluation_ground observed])
  have enriched_known: "lp_cut_knowledge
      (set (G @ filter (\<lambda>x. x\<in>lpp_source_context_ground context) vs)) guards eta"
    using known context_ground by (auto simp: lp_cut_knowledge_def)
  obtain grounded where inst: "lpc_seg_check_instance_boundary (LPCGoals pre) grounded guards vs (map Var vs)
      ce (lpcn_ground ?nd) (lpcn_guards ?nd) (lpcn_vars ?nd)
      (lpcsh_bindings receipt) (lpcsh_swaps receipt)"
    and grounded_known: "lp_cut_knowledge (set grounded) guards eta"
    using checked known enriched_known
    unfolding lpp_finite_triple_check_child_def Let_def state
    by auto
  have free_check: "lpc_check_link_free fuel [] F (lpctr_free ?entry) (lpcsh_bindings receipt)"
    and inp: "lp_atom_subst (lpctr_input ?entry) ?mu=inp"
    and equal: "lpc_triple_observe_atom (map (lpc_seg_position_template vs) (map ?mu (lpcn_vars ?nd)))
      (lpctr_output ?entry) = lpc_triple_observe_atom (map (lpc_seg_position_template vs) (map Var vs)) out"
    using checked by (auto simp: lpp_finite_triple_check_child_def Let_def state)
  have child_known: "lp_cut_knowledge (set (lpcn_ground ?nd)) (lpcn_guards ?nd) ?eta"
    by (rule lpc_seg_instance_boundary_knowledge[OF inst grounded_known])
  have child_free: "lpc_free_knowledge (set (lpctr_free ?entry)) ?eta"
    by (rule lpc_checked_link_free_sound[OF free_check _ free]) (simp add: lp_equations_def)
  have enriched: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP (lpp_context_add_ground context G) eta"
    by (rule lpp_evaluation_add_ground_sound[OF observed])
      (use known in \<open>auto simp: lp_cut_knowledge_def\<close>)
  have child_context: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP (contexts!?i) ?eta"
    by (rule lpp_evaluation_transport_sound[OF transfer transport enriched])
  have call_eval: "lp_atom_eval inp eta=lp_atom_eval (lpctr_input ?entry) ?eta"
    by (simp add: inp[symmetric] lp_atom_subst_def lp_atom_eval_def lp_ieval_finite_subst map_map o_def)
  have edge': "(a,lp_atom_eval (lpctr_input ?entry) ?eta)\<in>lp_triple_calls (set D) Q"
    using edge by (simp only: call_eval)
  have rep: "lpp_finite_triple_root_rep SP contexts roots (lpc_return_eval ?eta (lpc_triple_root_state ?entry))
      (lp_atom_eval (lpctr_input ?entry) ?eta) (lp_atom_eval (lpctr_output ?entry))"
    unfolding lpp_finite_triple_root_rep_def
    by (rule exI[of _ ?i], rule exI[of _ ?eta]) (use index child_known child_free child_context in simp)
  have child: "lpp_finite_triple_answer_contract P
      (lpc_return_eval ?eta [(ce,map Var (lpcn_vars ?nd))]) Q (lp_atom_eval (lpctr_output ?entry))"
    using lower[OF edge' rep] by (simp add: lpc_triple_root_state_def state)
  have answer: "lpc_triple_check_instance_answer Q vs (map Var vs) (lpcn_vars ?nd)
      (lpcsh_bindings receipt) (lpctr_output ?entry) out 0 []"
    using equal by (simp add: lpc_triple_check_instance_answer_def)
  show ?thesis by (rule lpp_finite_triple_checked_instance_contract[OF inst program grounded_known answer child])
qed

end
