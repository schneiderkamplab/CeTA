theory LP_Prolog_Observer_Continuing_Assembly
 imports LP_Prolog_Observer_Continuing_Block LP_Prolog_Observer_Block_Assembly
begin

definition lpp_check_observer_continuing_coverage where
 "lpp_check_observer_continuing_coverage T fuel P Q nds states contexts Fs functors separation_contexts returned arity actions witnesses =
  (length states=length nds \<and> length contexts=length nds \<and> length Fs=length nds \<and>
   length functors=length nds \<and> length separation_contexts=length nds \<and>
   length actions=length nds \<and> length witnesses=length nds \<and>
   list_all (\<lambda>i.
    (lpp_observer_continuing_equality_frame (states!i) \<longrightarrow>
     lpp_check_observer_equality_row T fuel P Q nds states contexts Fs functors separation_contexts i (actions!i) (witnesses!i)) \<and>
    (lpp_observer_may_univ (states!i) \<longrightarrow>
     lpp_observer_has_continuation (states!i) \<and> lpp_check_observer_univ_row T fuel P Q nds states contexts Fs functors separation_contexts returned arity i (actions!i) (witnesses!i))) [0..<length nds])"

lemma lpp_observer_continuing_equality_coverage:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_observer_continuing_coverage T fuel P Q nds states contexts Fs functors separation_contexts returned arity actions witnesses"
 and bound: "i<length nds"
 and shape: "lpp_observer_continuing_equality_frame (lpc_return_eval eta (states!i))"
 shows "lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functors
  (lpp_separation_node_conditions separation_contexts) lpp_finite_execution i"
proof -
 have row: "lpp_check_observer_equality_row T fuel P Q nds states contexts Fs functors separation_contexts i (actions!i) (witnesses!i)"
 using checked bound shape by (auto simp: lpp_check_observer_continuing_coverage_def list_all_iff lpp_observer_continuing_equality_template)
 show ?thesis by (rule lpp_checked_observer_equality_row[OF compatible transfer row])
qed

lemma lpp_observer_continuing_univ_coverage:
 assumes checked: "lpp_check_observer_continuing_coverage T fuel P Q nds states contexts Fs functors separation_contexts returned arity actions witnesses"
 and bound: "i<length nds"
 and shape: "lpp_observer_univ_frame (lpc_return_eval eta (states!i))"
 shows "lpp_check_observer_univ_row T fuel P Q nds states contexts Fs functors separation_contexts returned arity i (actions!i) (witnesses!i)"
 using checked bound lpp_observer_univ_template[OF shape]
 by (auto simp: lpp_check_observer_continuing_coverage_def list_all_iff)

lemma lpp_observer_continuing_tail_coverage:
 assumes checked: "lpp_check_observer_continuing_coverage T fuel P Q nds states contexts Fs functors separation_contexts returned arity actions witnesses"
 and bound: "i<length nds"
 and shape: "lpp_observer_univ_frame (lpc_return_eval eta (states!i))"
 shows "lpp_observer_has_continuation (states!i)"
 using checked bound lpp_observer_univ_template[OF shape]
 by (auto simp: lpp_check_observer_continuing_coverage_def list_all_iff)

lemma lpp_checked_observer_continuing_acquired_assembly:
 fixes SP :: "string lpp_success_clause list"
 and rest :: "(string lp_cut_symbol,nat) term lp_cut_goal list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and program: "lp_cut_source_program P"
 and internal: "lpp_check_observer_continuing_coverage T fuel P Q nds states contexts Fs functors
  separation_contexts source_returned source_arity actions witnesses"
 and checked: "lpp_check_observer_acquired_row T fuel P Q nds states contexts Fs functors
  separation_contexts i row_action row_witness"
 and clear: "lpc_rest_scopes rest={}"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and frontier_shapes: "lpp_check_observer_frontier_shapes frontier_nodes states"
 shows "lpp_observer_node_contract names operation SP P lpp_builtin_signature
  (lpp_univ_source_builtin names operation) lpp_univ_source_domain Q nds states contexts Fs functors
  (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts))
  (lpp_observer_invariant {v. vars_term v={}} specs rest) rest returned i"
proof -
 have equality: "lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functors
  (lpp_separation_node_conditions separation_contexts) lpp_finite_execution j"
 if "j<length nds" "lpp_observer_continuing_equality_frame (lpc_return_eval nu (states!j))"
 for j and nu :: "string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm"
 by (rule lpp_observer_continuing_equality_coverage[OF compatible transfer internal that])
 have univ: "\<exists>value_var name_var args_var middle facts pair_symbol output_name output_args.
  lpp_check_functor_source_action T fuel P Q nds states contexts Fs functors
   (nds!j) (Fs!j) (states!j) (contexts!j) (functors!j) source_returned source_arity
   (LPPFUniv value_var name_var args_var middle facts) \<and>
  lpp_check_separation_univ separation_contexts j (states!j) name_var args_var middle pair_symbol output_name output_args"
 if "j<length nds" "lpp_observer_univ_frame (lpc_return_eval nu (states!j))"
 for j and nu :: "string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm"
 by (rule lpp_checked_observer_univ_row(1)[OF lpp_observer_continuing_univ_coverage[OF internal that]])
 have exits: "lpp_check_observer_univ_exit (Fs!j) (states!j)"
 if "j<length nds" "lpp_observer_univ_frame (lpc_return_eval nu (states!j))"
 for j and nu :: "string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm"
 by (rule lpp_checked_observer_univ_row(2)[OF lpp_observer_continuing_univ_coverage[OF internal that]])
 have continuing: "lpp_observer_has_continuation (states!j)"
 if "j<length nds" "lpp_observer_univ_frame (lpc_return_eval nu (states!j))"
 for j and nu :: "string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm"
 by (rule lpp_observer_continuing_tail_coverage[OF internal that])
 show ?thesis using checked
 by (cases "(T,fuel,P,Q,nds,states,contexts,Fs,functors,separation_contexts,i,row_action,row_witness)"
     rule: lpp_check_observer_acquired_row.cases)
    (auto intro: lpp_checked_frontier_observer_fresh_univ_node_contract_continuing[OF compatible transfer program continuing equality univ _ _ _ clear covered frontier_shapes exits])
qed

ML \<open>
val thms = @{thms lpp_checked_observer_continuing_acquired_assembly
 lpp_observer_continuing_tail_coverage lpp_observer_continuing_equality_coverage lpp_observer_continuing_univ_coverage};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted continuing assembly" else ();
\<close>
end
