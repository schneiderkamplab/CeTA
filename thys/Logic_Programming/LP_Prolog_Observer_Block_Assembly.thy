theory LP_Prolog_Observer_Block_Assembly
 imports LP_Prolog_Observer_Internal_Coverage
begin

fun lpp_check_observer_acquired_row where
 "lpp_check_observer_acquired_row T fuel P Q nds states contexts Fs functors separation_contexts i
  (Some (LPPFCut (LPCRResolution a gs c m active saved k l A next anchors bindings mode outputs yes no) yes_facts no_facts))
  (Some (LPPSFreshAction normalized_facts failed x y z matching)) =
  (states!i=(LPCClause (LPCAtom a#gs) c m,active)#saved \<and>
   lpp_check_functor_resolution_node T yes_facts no_facts fuel P Q nds states contexts Fs functors
    (nds!i) (Fs!i) a gs c m active saved k l A next anchors bindings mode outputs (contexts!i) (functors!i) yes no \<and>
   lpp_check_separation_fresh fuel P (nds!i) separation_contexts i a c k l mode yes no normalized_facts failed x y z matching)"
| "lpp_check_observer_acquired_row T fuel P Q nds states contexts Fs functors separation_contexts i row_action row_witness = False"

lemma lpp_checked_observer_acquired_assembly:
 fixes SP :: "string lpp_success_clause list"
 and rest :: "(string lp_cut_symbol,nat) term lp_cut_goal list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and program: "lp_cut_source_program P"
 and internal: "lpp_check_observer_internal_coverage T fuel P Q nds states contexts Fs functors
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
 if "j<length nds" "lpp_observer_equality_frame (lpc_return_eval nu (states!j))"
 for j and nu :: "string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm"
 by (rule lpp_observer_internal_equality_coverage[OF compatible transfer internal that])
 have univ: "\<exists>value_var name_var args_var middle facts pair_symbol output_name output_args.
  lpp_check_functor_source_action T fuel P Q nds states contexts Fs functors
   (nds!j) (Fs!j) (states!j) (contexts!j) (functors!j) source_returned source_arity
   (LPPFUniv value_var name_var args_var middle facts) \<and>
  lpp_check_separation_univ separation_contexts j (states!j) name_var args_var middle pair_symbol output_name output_args"
 if "j<length nds" "lpp_observer_univ_frame (lpc_return_eval nu (states!j))"
 for j and nu :: "string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm"
 by (rule lpp_checked_observer_univ_row(1)[OF lpp_observer_internal_univ_coverage[OF internal that]])
 have exits: "lpp_check_observer_univ_exit (Fs!j) (states!j)"
 if "j<length nds" "lpp_observer_univ_frame (lpc_return_eval nu (states!j))"
 for j and nu :: "string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm"
 by (rule lpp_checked_observer_univ_row(2)[OF lpp_observer_internal_univ_coverage[OF internal that]])
 show ?thesis using checked
 by (cases "(T,fuel,P,Q,nds,states,contexts,Fs,functors,separation_contexts,i,row_action,row_witness)"
     rule: lpp_check_observer_acquired_row.cases)
    (auto intro: lpp_checked_frontier_observer_fresh_univ_node_contract[OF compatible transfer program equality univ _ _ _ clear covered frontier_shapes exits])
qed

ML \<open>
val thms = @{thms lpp_checked_observer_acquired_assembly};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted acquired observer assembly" else ();
\<close>
end
