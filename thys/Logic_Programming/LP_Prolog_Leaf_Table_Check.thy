theory LP_Prolog_Leaf_Table_Check
 imports LP_Prolog_Leaf_Action_Check
begin

text \<open>Every represented local action has checked side evidence. A missing
action denotes exhaustion or an explicit external module contract. It cannot
silently remove a source branch or discharge a Split boundary.\<close>

definition lpp_check_leaf_control where
 "lpp_check_leaf_control T fuel P Q nds states contexts Fs functor_contexts
    separation_contexts returned arity actions witnesses slots =
  (lpp_check_functor_control T fuel P Q nds states contexts Fs functor_contexts returned arity actions \<and>
   length separation_contexts=length nds \<and> length witnesses=length nds \<and>
   list_all (\<lambda>i. case (actions!i,witnesses!i) of
     (None,None) \<Rightarrow> True
   | (Some action,Some witness) \<Rightarrow>
      lpp_check_separation_action fuel P (nds!i) (contexts!i) (Fs!i) separation_contexts i (states!i) action witness \<and>
      lpp_check_leaf_action_coverage (nds!i) (contexts!i) (functor_contexts!i) (separation_contexts!i) slots action witness
   | _ \<Rightarrow> False) [0..<length nds])"

theorem lpp_checked_leaf_table_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_leaf_control T fuel P Q nds states contexts Fs functor_contexts
   separation_contexts returned arity actions witnesses slots"
 and slots: "slots=map fst specs"
 and program: "lp_cut_source_program P"
 and boundary: "\<And>j. j<length nds \<Longrightarrow> actions!j=None \<Longrightarrow> states!j\<noteq>[] \<Longrightarrow>
   lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) (\<lambda>ss. lpp_finite_execution ss \<and> lpp_leaf_stack_invariant {u. vars_term u={}} specs ss) returned arity j"
 and initial: "lpp_separation_node_conditions separation_contexts i eta"
 and root: "i<length nds"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and invariant: "(\<lambda>ss. lpp_finite_execution ss \<and> lpp_leaf_stack_invariant {u. vars_term u={}} specs ss) (lpc_return_eval eta (states!i))"
 and residual: "SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]}"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_return_eval eta (states!i)) (lp_ild Q) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]
   (\<lambda>rho. [(returned,map rho [0..<arity])])"
proof -
 have base: "lpp_check_functor_control T fuel P Q nds states contexts Fs functor_contexts returned arity actions"
  using checked by (simp add: lpp_check_leaf_control_def)
 show ?thesis
 proof (rule lpp_premised_functor_table_contract[where node_conditions="lpp_separation_node_conditions separation_contexts" and J="(\<lambda>ss. lpp_finite_execution ss \<and> lpp_leaf_stack_invariant {u. vars_term u={}} specs ss)", OF base program _ _ _ initial root known free observed functors invariant residual])
  show "\<And>swaps ss. (\<lambda>ss. lpp_finite_execution ss \<and> lpp_leaf_stack_invariant {u. vars_term u={}} specs ss) ss \<Longrightarrow> (\<lambda>ss. lpp_finite_execution ss \<and> lpp_leaf_stack_invariant {u. vars_term u={}} specs ss) (lpc_return_scope_word swaps ss)"
   by (simp add: lpp_finite_execution_scope_word lpp_leaf_stack_scopes)
 next
  fix j action assume bound: "j<length nds" and action: "actions!j=Some action"
  have source_check: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
    (nds!j) (Fs!j) (states!j) (contexts!j) (functor_contexts!j) returned arity action"
   by (rule lpp_functor_control_complete(3)[OF base bound action])
  have row: "(case (actions!j,witnesses!j) of
     (None,None) \<Rightarrow> True
   | (Some selected,Some witness) \<Rightarrow>
      lpp_check_separation_action fuel P (nds!j) (contexts!j) (Fs!j) separation_contexts j (states!j) selected witness \<and>
      lpp_check_leaf_action_coverage (nds!j) (contexts!j) (functor_contexts!j) (separation_contexts!j) slots selected witness
   | _ \<Rightarrow> False)"
   using checked bound unfolding lpp_check_leaf_control_def list_all_iff by auto
  obtain witness where local_check: "lpp_check_separation_action fuel P (nds!j) (contexts!j) (Fs!j)
    separation_contexts j (states!j) action witness"
   and coverage: "lpp_check_leaf_action_coverage (nds!j) (contexts!j) (functor_contexts!j) (separation_contexts!j) (map fst specs) action witness"
   using row action slots by (cases "witnesses!j") auto
  show "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) (\<lambda>ss. lpp_finite_execution ss \<and> lpp_leaf_stack_invariant {u. vars_term u={}} specs ss) returned arity j"
   by (rule lpp_checked_leaf_separation_action_node_contract[OF compatible transfer source_check local_check coverage])
 next
  fix j assume bound: "j<length nds" and absent: "actions!j=None"
  show "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) (\<lambda>ss. lpp_finite_execution ss \<and> lpp_leaf_stack_invariant {u. vars_term u={}} specs ss) returned arity j"
   by (cases "states!j=[]")
    (auto intro: lpp_exhausted_premised_functor_node_contract boundary[OF bound absent])
 qed
qed

lemma lpp_leaf_table_missing_witness_row_rejected:
 "length witnesses\<noteq>length nds \<Longrightarrow>
  \<not>lpp_check_leaf_control T fuel P Q nds states contexts Fs functor_contexts separation_contexts returned arity actions witnesses slots"
 by (simp add: lpp_check_leaf_control_def)

lemma lpp_leaf_table_missing_context_row_rejected:
 "length separation_contexts\<noteq>length nds \<Longrightarrow>
  \<not>lpp_check_leaf_control T fuel P Q nds states contexts Fs functor_contexts separation_contexts returned arity actions witnesses slots"
 by (simp add: lpp_check_leaf_control_def)

lemma lpp_leaf_table_missing_action_witness_rejected:
 "j<length nds \<Longrightarrow> actions!j=Some action \<Longrightarrow> witnesses!j=None \<Longrightarrow>
  \<not>lpp_check_leaf_control T fuel P Q nds states contexts Fs functor_contexts separation_contexts returned arity actions witnesses slots"
 by (auto simp: lpp_check_leaf_control_def list_all_iff; rule bexI[of _ j]; simp)

lemma lpp_leaf_table_orphan_witness_rejected:
 "j<length nds \<Longrightarrow> actions!j=None \<Longrightarrow> witnesses!j=Some witness \<Longrightarrow>
  \<not>lpp_check_leaf_control T fuel P Q nds states contexts Fs functor_contexts separation_contexts returned arity actions witnesses slots"
 by (auto simp: lpp_check_leaf_control_def list_all_iff; rule bexI[of _ j]; simp)

ML \<open>
val checked = @{thms lpp_checked_leaf_table_contract lpp_leaf_table_missing_witness_row_rejected
 lpp_leaf_table_missing_context_row_rejected lpp_leaf_table_missing_action_witness_rejected
 lpp_leaf_table_orphan_witness_rejected};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted leaf table checker" else ();
\<close>
end
