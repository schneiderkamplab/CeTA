theory LP_Cut_SEG_Triple_Child
  imports LP_Cut_SEG_Triple_Region LP_Cut_SEG_Child
begin

definition lpc_triple_check_child where
  "lpc_triple_check_child fuel roots pre G guards F vs inp out receipt =
    (lpcsh_target receipt<length roots \<and>
      (let entry=roots!lpcsh_target receipt; nd=lpctr_node entry;
           mu=lp_cut_instance_subst (lpcsh_bindings receipt) in
       case lpcn_state nd of [ce] \<Rightarrow>
         lpc_seg_check_instance_boundary (LPCGoals pre) G guards vs (map Var vs)
           ce (lpcn_ground nd) (lpcn_guards nd) (lpcn_vars nd)
           (lpcsh_bindings receipt) (lpcsh_swaps receipt) \<and>
         lpc_check_link_free fuel [] F (lpctr_free entry) (lpcsh_bindings receipt) \<and>
         lp_atom_subst (lpctr_input entry) mu=inp \<and>
         lpc_triple_observe_atom (map (lpc_seg_position_template vs) (map mu (lpcn_vars nd)))
           (lpctr_output entry) =
         lpc_triple_observe_atom (map (lpc_seg_position_template vs) (map Var vs)) out
       | _ \<Rightarrow> False))"

theorem lpc_triple_child_checked_lower:
  fixes P :: "('f,string) lp_cut_program"
  assumes checked: "lpc_triple_check_child fuel roots pre G guards F vs inp out receipt"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set G) guards eta"
    and free: "lpc_free_knowledge (set F) eta"
    and edge: "(a,lp_atom_eval inp eta)\<in>lp_triple_calls (set D) Q"
    and lower: "\<And>us b ret. (a,b)\<in>lp_triple_calls (set D) Q \<Longrightarrow>
      lpc_triple_root_rep roots us b ret \<Longrightarrow> lpc_triple_answer_contract P us Q ret"
  shows "lpc_triple_answer_contract P (lpc_return_eval eta [(LPCGoals pre,map Var vs)]) Q (lp_atom_eval out)"
proof -
  let ?i = "lpcsh_target receipt"
  let ?entry = "roots!?i"
  let ?nd = "lpctr_node ?entry"
  let ?mu = "lp_cut_instance_subst (lpcsh_bindings receipt)"
  let ?eta = "\<lambda>x. lp_ieval (?mu x) eta"
  have index: "?i<length roots" using checked by (simp add: lpc_triple_check_child_def)
  obtain ce where state: "lpcn_state ?nd=[ce]"
    using checked by (auto simp: lpc_triple_check_child_def Let_def split: list.splits;
      metis list.exhaust)
  have inst: "lpc_seg_check_instance_boundary (LPCGoals pre) G guards vs (map Var vs)
      ce (lpcn_ground ?nd) (lpcn_guards ?nd) (lpcn_vars ?nd)
      (lpcsh_bindings receipt) (lpcsh_swaps receipt)"
    and free_check: "lpc_check_link_free fuel [] F (lpctr_free ?entry) (lpcsh_bindings receipt)"
    and inp: "lp_atom_subst (lpctr_input ?entry) ?mu=inp"
    and equal: "lpc_triple_observe_atom (map (lpc_seg_position_template vs) (map ?mu (lpcn_vars ?nd)))
      (lpctr_output ?entry) = lpc_triple_observe_atom (map (lpc_seg_position_template vs) (map Var vs)) out"
    using checked by (auto simp: lpc_triple_check_child_def Let_def state)
  have child_known: "lp_cut_knowledge (set (lpcn_ground ?nd)) (lpcn_guards ?nd) ?eta"
    by (rule lpc_seg_instance_boundary_knowledge[OF inst known])
  have child_free: "lpc_free_knowledge (set (lpctr_free ?entry)) ?eta"
    by (rule lpc_checked_link_free_sound[OF free_check _ free]) (simp add: lp_equations_def)
  have call_eval: "lp_atom_eval inp eta=lp_atom_eval (lpctr_input ?entry) ?eta"
    by (simp add: inp[symmetric] lp_atom_subst_def lp_atom_eval_def lp_ieval_finite_subst map_map o_def)
  have edge': "(a,lp_atom_eval (lpctr_input ?entry) ?eta)\<in>lp_triple_calls (set D) Q"
    using edge by (simp only: call_eval)
  have rep: "lpc_triple_root_rep roots (lpc_return_eval ?eta (lpc_triple_root_state ?entry))
      (lp_atom_eval (lpctr_input ?entry) ?eta) (lp_atom_eval (lpctr_output ?entry))"
    unfolding lpc_triple_root_rep_def
    by (rule exI[of _ ?i], rule exI[of _ ?eta]) (use index child_known child_free in simp)
  have child: "lpc_triple_answer_contract P
      (lpc_return_eval ?eta [(ce,map Var (lpcn_vars ?nd))]) Q (lp_atom_eval (lpctr_output ?entry))"
    using lower[OF edge' rep] by (simp add: lpc_triple_root_state_def state)
  have answer: "lpc_triple_check_instance_answer Q vs (map Var vs) (lpcn_vars ?nd)
      (lpcsh_bindings receipt) (lpctr_output ?entry) out 0 []"
    using equal by (simp add: lpc_triple_check_instance_answer_def)
  show ?thesis by (rule lpc_triple_checked_instance_contract[OF inst program known answer child])
qed

end
