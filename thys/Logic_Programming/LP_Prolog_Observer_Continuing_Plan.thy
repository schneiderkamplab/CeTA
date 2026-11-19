theory LP_Prolog_Observer_Continuing_Plan
 imports LP_Prolog_Observer_Continuing_Assembly LP_Prolog_Observer_Plan
begin

fun lpp_observer_acquired_role where
 "lpp_observer_acquired_role (LPPORAcquired _) = True"
| "lpp_observer_acquired_role _ = False"

definition lpp_check_observer_continuing_plan where
 "lpp_check_observer_continuing_plan T fuel P Q nds states contexts Fs functors
  returned arity separation_contexts version plan_rows frontier_indices actions witnesses =
  (lpp_check_observer_local_assembly T fuel P Q nds states contexts Fs functors
    returned arity separation_contexts version plan_rows frontier_indices actions witnesses \<and>
   lpp_check_observer_continuing_coverage T fuel P Q nds states contexts Fs functors
    separation_contexts returned arity actions witnesses \<and>
   list_all (\<lambda>row. lpp_observer_acquired_role (snd row) \<longrightarrow>
    lpp_check_observer_acquired_row T fuel P Q nds states contexts Fs functors
     separation_contexts (fst row) (actions!fst row) (witnesses!fst row)) plan_rows)"

text \<open>Acceptance supplies conditional local and acquired node contracts.
Returned rows, empty rows and module boundaries still require source assembly.
The original pending ledger is not shortened by this check.\<close>

theorem lpp_observer_continuing_plan_acquired_contract:
 fixes SP :: "string lpp_success_clause list"
 and rest :: "(string lp_cut_symbol,nat) term lp_cut_goal list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and program: "lp_cut_source_program P"
 and clear: "lpc_rest_scopes rest={}"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and assembled: "lpp_check_observer_continuing_plan T fuel P Q nds states contexts Fs functors
  source_returned arity separation_contexts version plan_rows frontier_indices actions witnesses"
 and row: "(i,LPPORAcquired block_index)\<in>set plan_rows"
 shows "lpp_observer_node_contract names operation SP P lpp_builtin_signature
  (lpp_univ_source_builtin names operation) lpp_univ_source_domain Q nds states contexts Fs functors
  (lpp_observer_frontier_conditions (set frontier_indices) (lpp_separation_node_conditions separation_contexts))
  (lpp_observer_invariant {v. vars_term v={}} specs rest) rest returned i"
proof -
 have internal: "lpp_check_observer_continuing_coverage T fuel P Q nds states contexts Fs functors
    separation_contexts source_returned arity actions witnesses"
 and entry: "lpp_check_observer_acquired_row T fuel P Q nds states contexts Fs functors
     separation_contexts i (actions!i) (witnesses!i)"
 and shapes: "lpp_check_observer_frontier_shapes (set frontier_indices) states"
  using assembled row by (auto simp: lpp_check_observer_continuing_plan_def
    lpp_check_observer_local_assembly_def lpp_check_observer_plan_def list_all_iff)
 show ?thesis by (rule lpp_checked_observer_continuing_acquired_assembly[OF compatible transfer program internal entry clear covered shapes])
qed

ML \<open>
val thms = @{thms lpp_observer_continuing_plan_acquired_contract};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted continuing observer plan" else ();
\<close>
end
