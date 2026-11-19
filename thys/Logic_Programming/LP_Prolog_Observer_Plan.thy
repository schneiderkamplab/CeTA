theory LP_Prolog_Observer_Plan
 imports LP_Prolog_Observer_Frontier_Module LP_Prolog_Separation_Subject_XML
begin

datatype lpp_observer_row_role =
 LPPORLocal | LPPORAcquired nat | LPPORInternal nat | LPPORReturned nat |
 LPPOREmpty | LPPORBoundary

fun lpp_observer_internal_role where
 "lpp_observer_internal_role (LPPORInternal _) = True"
| "lpp_observer_internal_role _ = False"

fun lpp_observer_internal_witness where
 "lpp_observer_internal_witness (Some LPPSPairAction) = True"
| "lpp_observer_internal_witness (Some (LPPSReflexiveAction _ _)) = True"
| "lpp_observer_internal_witness (Some (LPPSUnivAction _ _ _)) = True"
| "lpp_observer_internal_witness _ = False"

fun lpp_observer_acquired_witness where
 "lpp_observer_acquired_witness (Some (LPPSFreshAction _ _ _ _ _ _)) = True"
| "lpp_observer_acquired_witness _ = False"

fun lpp_observer_returned_frame where
 "lpp_observer_returned_frame ((LPCGoals [],payload)#saved) = Some (length saved)"
| "lpp_observer_returned_frame _ = None"

fun lpp_observer_head_witness where
 "lpp_observer_head_witness (Some (LPPSUnificationAction h)) = h"
| "lpp_observer_head_witness _ = None"

fun lpp_check_observer_row_role where
 "lpp_check_observer_row_role LPPORLocal ss action witness =
  (action\<noteq>None \<and> witness\<noteq>None \<and> lpp_observer_returned_frame ss=None \<and>
   \<not>lpp_observer_internal_witness witness \<and> \<not>lpp_observer_acquired_witness witness)"
| "lpp_check_observer_row_role (LPPORAcquired block_index) ss action witness =
  (action\<noteq>None \<and> lpp_observer_acquired_witness witness)"
| "lpp_check_observer_row_role (LPPORInternal block_index) ss action witness =
  (action\<noteq>None \<and> lpp_observer_internal_witness witness)"
| "lpp_check_observer_row_role (LPPORReturned saved) ss action witness =
  (lpp_observer_returned_frame ss=Some saved \<and>
   \<not>lpp_observer_internal_witness witness \<and> \<not>lpp_observer_acquired_witness witness)"
| "lpp_check_observer_row_role LPPOREmpty ss action witness =
  (ss=[] \<and> action=None \<and> witness=None)"
| "lpp_check_observer_row_role LPPORBoundary ss action witness =
  (ss\<noteq>[] \<and> lpp_observer_returned_frame ss=None \<and> action=None \<and> witness=None)"

definition lpp_check_observer_plan where
 "lpp_check_observer_plan version plan_rows frontier_indices (states::string lpc_return_state list)
  (actions::lpp_functor_action option list) witnesses =
  ((version::nat)=1 \<and> map fst plan_rows=[0..<length states] \<and>
   length actions=length states \<and> length witnesses=length states \<and>
   frontier_indices=map fst (filter (\<lambda>row. \<not>lpp_observer_internal_role (snd row)) plan_rows) \<and>
   lpp_check_observer_frontier_shapes (set frontier_indices) states \<and>
   list_all (\<lambda>row. lpp_check_observer_row_role (snd row)
     (states!fst row) (actions!fst row) (witnesses!fst row)) plan_rows)"

text \<open>All nonlocal roles remain independently required obligations. Trace
identifiers are references, not proof of an acquired block or its exits.\<close>
definition lpp_observer_plan_pending where
 "lpp_observer_plan_pending plan_rows = map fst (filter (\<lambda>row. snd row\<noteq>LPPORLocal) plan_rows)"

definition lpp_check_observer_local_assembly where
 "lpp_check_observer_local_assembly T fuel P Q nds states contexts Fs functors
  returned arity separation_contexts version plan_rows frontier_indices actions witnesses =
  (lpp_check_observer_plan version plan_rows frontier_indices states actions witnesses \<and>
   length nds=length states \<and> length contexts=length states \<and>
   length Fs=length states \<and> length functors=length states \<and>
   length separation_contexts=length states \<and>
   list_all (\<lambda>row. snd row=LPPORLocal \<longrightarrow>
    (case actions!fst row of None \<Rightarrow> False | Some action \<Rightarrow>
     lpp_check_functor_source_action T fuel P Q nds states contexts Fs functors
      (nds!fst row) (Fs!fst row) (states!fst row) (contexts!fst row) (functors!fst row)
      returned arity action \<and>
     lpp_check_frontier_observer_local (set frontier_indices) P (nds!fst row) (contexts!fst row)
      separation_contexts (fst row) (states!fst row) action
      (lpp_observer_head_witness (witnesses!fst row)))) plan_rows)"

lemma lpp_observer_local_assembly_checked_row:
 assumes "lpp_check_observer_local_assembly T fuel P Q nds states contexts Fs functors
  returned arity separation_contexts version plan_rows frontier_indices actions witnesses"
 and "(i,LPPORLocal)\<in>set plan_rows"
 shows "\<exists>action. actions!i=Some action \<and>
  lpp_check_functor_source_action T fuel P Q nds states contexts Fs functors
   (nds!i) (Fs!i) (states!i) (contexts!i) (functors!i) returned arity action \<and>
  lpp_check_frontier_observer_local (set frontier_indices) P (nds!i) (contexts!i)
   separation_contexts i (states!i) action (lpp_observer_head_witness (witnesses!i))"
 using assms by (auto simp: lpp_check_observer_local_assembly_def list_all_iff split: option.splits)

theorem lpp_observer_local_assembly_node_contract:
 fixes SP :: "string lpp_success_clause list"
 and rest :: "(string lp_cut_symbol,nat) term lp_cut_goal list"
 assumes program: "lp_cut_source_program P"
 and clear: "lpc_rest_scopes rest={}"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and assembled: "lpp_check_observer_local_assembly T fuel P Q nds states contexts Fs functors
  source_returned arity separation_contexts version plan_rows frontier_indices actions witnesses"
 and row: "(i,LPPORLocal)\<in>set plan_rows"
 shows "lpp_observer_node_contract names operation SP P lpp_builtin_signature
  (lpp_univ_source_builtin names operation) lpp_univ_source_domain Q nds states contexts Fs functors
  (lpp_observer_frontier_conditions (set frontier_indices) (lpp_separation_node_conditions separation_contexts))
  (lpp_observer_invariant {v. vars_term v={}} specs rest) rest returned i"
proof -
 obtain action where checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functors
   (nds!i) (Fs!i) (states!i) (contexts!i) (functors!i) source_returned arity action"
 and extra: "lpp_check_frontier_observer_local (set frontier_indices) P (nds!i) (contexts!i)
   separation_contexts i (states!i) action (lpp_observer_head_witness (witnesses!i))"
 using lpp_observer_local_assembly_checked_row[OF assembled row] by blast
 show ?thesis by (rule lpp_checked_frontier_local_contract[OF program clear covered compatible transfer checked extra])
qed

lemma lpp_observer_nonlocal_remains_pending:
 "(i,role)\<in>set plan_rows \<Longrightarrow> role\<noteq>LPPORLocal \<Longrightarrow>
  i\<in>set (lpp_observer_plan_pending plan_rows)"
 by (auto simp: lpp_observer_plan_pending_def)

lemma lpp_observer_plan_complete_indices:
 "lpp_check_observer_plan version plan_rows frontier_indices states actions witnesses \<Longrightarrow>
  map fst plan_rows=[0..<length states]"
 by (simp add: lpp_check_observer_plan_def)

lemma lpp_observer_plan_stale_rejected:
 "version\<noteq>1 \<Longrightarrow> \<not>lpp_check_observer_plan version plan_rows frontier_indices states actions witnesses"
 by (simp add: lpp_check_observer_plan_def)

lemma lpp_observer_plan_missing_rows_rejected:
 "length plan_rows\<noteq>length states \<Longrightarrow>
  \<not>lpp_check_observer_plan version plan_rows frontier_indices states actions witnesses"
 by (auto simp: lpp_check_observer_plan_def dest: arg_cong[where f=length])

ML \<open>
val thms = @{thms lpp_observer_local_assembly_node_contract lpp_observer_local_assembly_checked_row lpp_observer_nonlocal_remains_pending
 lpp_observer_plan_complete_indices lpp_observer_plan_stale_rejected lpp_observer_plan_missing_rows_rejected};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted observer plan checker" else ();
\<close>
end
