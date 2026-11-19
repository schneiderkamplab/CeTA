theory LP_Cut_Domain_SEG_Triple_Connection
 imports LP_Cut_Domain_SEG_Triple_Observed
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

definition precise_triple_root_rep where
  "precise_triple_root_rep (roots::'f lpc_triple_root list) ss a
      (ret::(nat \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm) \<Rightarrow> ('f lp_cut_symbol,string) lp_iatom) =
    (\<exists>i eta. i<length roots \<and>
      knowledge (set (lpcn_ground (lpctr_node (roots!i))))
        (lpcn_guards (lpctr_node (roots!i))) eta \<and>
      lpc_free_knowledge (set (lpctr_free (roots!i))) eta \<and>
      ss=lpc_return_eval eta (lpc_triple_root_state (roots!i)) \<and>
      a=lp_atom_eval (lpctr_input (roots!i)) eta \<and>
      ret=lp_atom_eval (lpctr_output (roots!i)))"


theorem precise_triple_connection_checked_lower:
  fixes P :: "('f,string) lp_cut_program"
  assumes checked: "lpc_triple_check_connection fuel triples Q roots nd F ss inp out receipt"
    and program: "lp_cut_source_program P"
    and known: "knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and invariant: "lpc_triple_instance_invariant a inp (lpc_return_eval eta ss)"
    and lower: "\<And>us b ret. (a,b)\<in>lp_triple_calls (set triples) Q \<Longrightarrow>
      precise_triple_root_rep roots us b ret \<Longrightarrow> precise_triple_answer_contract P us Q ret"
  shows "precise_triple_answer_contract P (lpc_return_eval eta ss) Q (lp_atom_eval out)"
proof -
  let ?i = "lpctc_target receipt"
  let ?root = "roots!?i"
  let ?child = "lpctr_node ?root"
  let ?mu = "lp_cut_instance_subst (lpctc_bindings receipt)"
  let ?eta = "\<lambda>x. lp_ieval (?mu x) eta"
  have index: "?i<length roots"
    using checked by (simp add: lpc_triple_check_connection_def)
  obtain e observed ce where ss: "ss=[(e,observed)]"
    and state: "lpcn_state ?child=[ce]"
    using checked
    by (auto simp: lpc_triple_check_connection_def Let_def split: list.splits prod.splits;
      metis list.exhaust prod.exhaust)
  have inst: "lpc_seg_check_instance_boundary e (lpcn_ground nd) (lpcn_guards nd) (lpcn_vars nd) observed
      ce (lpcn_ground ?child) (lpcn_guards ?child) (lpcn_vars ?child)
      (lpctc_bindings receipt) (lpctc_swaps receipt)"
    and free_check: "lpc_check_link_free fuel [] F (lpctr_free ?root) (lpctc_bindings receipt)"
    and call: "lpc_triple_check_call triples [] (lpc_triple_observation_atom observed inp)
      (lp_atom_subst (lpctr_input ?root) ?mu) (lpctc_call receipt) (lpctc_call_bindings receipt)"
    and answer: "lpc_triple_check_instance_answer Q (lpcn_vars nd) observed (lpcn_vars ?child)
      (lpctc_bindings receipt) (lpctr_output ?root) out
      (lpctc_success receipt) (lpctc_success_bindings receipt)"
    using checked by (auto simp: lpc_triple_check_connection_def Let_def ss state)
  have child_known: "knowledge (set (lpcn_ground ?child)) (lpcn_guards ?child) ?eta"
    by (rule precise_seg_instance_boundary_knowledge[OF inst known])
  have child_free: "lpc_free_knowledge (set (lpctr_free ?root)) ?eta"
    by (rule lpc_checked_link_free_sound[OF free_check _ free]) (simp add: lp_equations_def)
  obtain sigma where matching: "lp_iatom_subst a sigma=
      lp_atom_eval (lpc_triple_observation_atom observed inp) eta"
    using invariant by (auto simp: ss lpc_triple_instance_invariant_def
      lpc_return_eval_def lpc_triple_observation_atom_eval)
  have call_eval: "lp_atom_eval (lp_atom_subst (lpctr_input ?root) ?mu) eta =
      lp_atom_eval (lpctr_input ?root) ?eta"
    by (simp add: lp_atom_subst_def lp_atom_eval_def lp_ieval_finite_subst map_map o_def)
  have edge: "(a,lp_atom_eval (lpctr_input ?root) ?eta)\<in>lp_triple_calls (set triples) Q"
    using lpc_triple_checked_call[OF call matching, where Q=Q] by (simp add: call_eval)
  have rep: "precise_triple_root_rep roots (lpc_return_eval ?eta (lpc_triple_root_state ?root))
      (lp_atom_eval (lpctr_input ?root) ?eta) (lp_atom_eval (lpctr_output ?root))"
    unfolding precise_triple_root_rep_def
    by (rule exI[of _ ?i], rule exI[of _ ?eta]) (use index child_known child_free in simp)
  have child: "precise_triple_answer_contract P
      (lpc_return_eval ?eta [(ce,map Var (lpcn_vars ?child))]) Q (lp_atom_eval (lpctr_output ?root))"
    using lower[OF edge rep] by (simp add: lpc_triple_root_state_def state)
  show ?thesis unfolding ss
    by (rule precise_triple_checked_instance_contract[OF inst program known answer child])
qed


end
end
