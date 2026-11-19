theory LP_Prolog_Observer_Plan_Nodes
 imports LP_Prolog_Observer_Continuing_Plan LP_Prolog_Observer_Family
begin

lemma lpp_observer_plan_role_at:
 assumes checked: "lpp_check_observer_plan version plan_rows frontier_indices states actions witnesses"
 and bound: "i<length states"
 shows "\<exists>role. (i,role)\<in>set plan_rows"
proof -
 have "i\<in>set (map fst plan_rows)"
  using checked bound by (simp add: lpp_check_observer_plan_def)
 then show ?thesis by auto
qed

lemma lpp_observer_plan_internal_not_frontier:
 assumes checked: "lpp_check_observer_plan version plan_rows frontier_indices states actions witnesses"
 and row: "(i,LPPORInternal block_index)\<in>set plan_rows"
 shows "i\<notin>set frontier_indices"
proof -
 have "distinct (map fst plan_rows)"
  using checked by (simp add: lpp_check_observer_plan_def)
 then have unique: "inj_on fst (set plan_rows)" by (simp add: distinct_map)
 have same: "role=LPPORInternal block_index" if "(i,role)\<in>set plan_rows" for role
  using inj_onD[OF unique _ that row] by simp
 show ?thesis
 proof
  assume "i\<in>set frontier_indices"
  then obtain role where member: "(i,role)\<in>set plan_rows"
   and ordinary: "\<not>lpp_observer_internal_role role"
   using checked by (auto simp: lpp_check_observer_plan_def)
  have "role=LPPORInternal block_index" by (rule same[OF member])
  then show False using ordinary by simp
 qed
qed

lemma lpp_observer_plan_empty_state:
 "lpp_check_observer_plan version plan_rows frontier_indices states actions witnesses \<Longrightarrow>
  (i,LPPOREmpty)\<in>set plan_rows \<Longrightarrow> states!i=[]"
 by (auto simp: lpp_check_observer_plan_def list_all_iff)

lemma lpp_observer_plan_internal_contract:
 assumes checked: "lpp_check_observer_plan version plan_rows frontier_indices states actions witnesses"
 and row: "(i,LPPORInternal block_index)\<in>set plan_rows"
 shows "lpp_observer_node_contract names operation SP P B U D Q nds states contexts Fs functors
  (lpp_observer_frontier_conditions (set frontier_indices) node_conditions) J rest returned i"
 using lpp_observer_plan_internal_not_frontier[OF checked row]
 by (simp add: lpp_observer_node_contract_def lpp_observer_frontier_conditions_def)

text \<open>Only successful-return and nonempty boundary roles require external
node contracts here. Internal rows are checked by acquired-block composition;
empty rows have the existing empty-state contract. All rows remain in the plan.\<close>

lemma lpp_observer_planned_node_contract:
 fixes SP :: "string lpp_success_clause list"
 and rest :: "(string lp_cut_symbol,nat) term lp_cut_goal list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and program: "lp_cut_source_program P"
 and clear: "lpc_rest_scopes rest={}"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and assembled: "lpp_check_observer_continuing_plan T fuel P Q nds states contexts Fs functors
  source_returned arity separation_contexts version plan_rows frontier_indices actions witnesses"
 and bound: "i<length nds"
 and included: "\<And>child u. lpp_premised_functor_module_rep names operation SP nds states contexts Fs functors
   (lpp_observer_frontier_conditions (set frontier_indices) (lpp_separation_node_conditions separation_contexts))
   (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<Longrightarrow> child_rep child u"
 and external: "\<And>role. (i,role)\<in>set plan_rows \<Longrightarrow>
   (role=LPPORBoundary \<or> (\<exists>saved. role=LPPORReturned saved)) \<Longrightarrow>
   lpp_observer_referenced_node_contract names operation SP P lpp_builtin_signature
    (lpp_univ_source_builtin names operation) lpp_univ_source_domain Q nds states contexts Fs functors
    (lpp_observer_frontier_conditions (set frontier_indices) (lpp_separation_node_conditions separation_contexts))
    child_rep (lpp_observer_invariant {v. vars_term v={}} specs rest) rest returned i"
 shows "lpp_observer_referenced_node_contract names operation SP P lpp_builtin_signature
    (lpp_univ_source_builtin names operation) lpp_univ_source_domain Q nds states contexts Fs functors
    (lpp_observer_frontier_conditions (set frontier_indices) (lpp_separation_node_conditions separation_contexts))
    child_rep (lpp_observer_invariant {v. vars_term v={}} specs rest) rest returned i"
proof -
 have local: "lpp_check_observer_local_assembly T fuel P Q nds states contexts Fs functors
  source_returned arity separation_contexts version plan_rows frontier_indices actions witnesses"
 and plan: "lpp_check_observer_plan version plan_rows frontier_indices states actions witnesses"
 and lengths: "length nds=length states"
  using assembled by (auto simp: lpp_check_observer_continuing_plan_def lpp_check_observer_local_assembly_def)
 have state_bound: "i<length states" using bound lengths by simp
 obtain role where row: "(i,role)\<in>set plan_rows"
  using lpp_observer_plan_role_at[OF plan state_bound] by blast
 show ?thesis
 proof (cases role)
  case LPPORLocal
  show ?thesis by (rule lpp_observer_local_to_referenced_node[OF _ included]) (rule lpp_observer_local_assembly_node_contract[OF program clear covered compatible transfer local row[unfolded LPPORLocal]])
 next
  case (LPPORAcquired block_index)
  show ?thesis by (rule lpp_observer_local_to_referenced_node[OF _ included]) (rule lpp_observer_continuing_plan_acquired_contract[OF compatible transfer program clear covered assembled row[unfolded LPPORAcquired]])
 next
  case (LPPORInternal block_index)
  show ?thesis by (rule lpp_observer_local_to_referenced_node[OF _ included]) (rule lpp_observer_plan_internal_contract[OF plan row[unfolded LPPORInternal]])
 next
  case (LPPORReturned saved)
  show ?thesis by (rule external[OF row]) (simp add: LPPORReturned)
 next
  case LPPOREmpty
  show ?thesis by (rule lpp_observer_local_to_referenced_node[OF _ included]) (rule lpp_observer_empty_node_contract[OF lpp_observer_plan_empty_state[OF plan row[unfolded LPPOREmpty]]])
 next
  case LPPORBoundary
  show ?thesis by (rule external[OF row]) (simp add: LPPORBoundary)
 qed
qed

ML \<open>
val thms = @{thms lpp_observer_planned_node_contract};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted observer node assembly" else ();
\<close>
end
